/*
    Copyright (C) 2009  E.Albert, P.Arenas, S.Genaim, G.Puebla, and D.Zanardini
                        https://costa.ls.fi.upm.es

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

:- module(multimap,[
    empty_mm/1,
    put_mm/4,
    put_values_mm/4,
    put_keys_mm/4,
    maps_mm/3,
    values_of_mm/3,
    keys_of_mm/3,
    keys_mm/2,
    values_mm/2,
    keys_multiset_mm/2,
    values_multiset_mm/2,
    count_keys_of_mm/3,
    count_values_of_mm/3,
    remove_mm/4,
    remove_key_mm/3,
    remove_value_mm/3,
    join_mm/3,
    inverse_mm/2,
    compose_mm/3, 
    from_map_mm/2,
    from_pair_list_mm/2,
    to_pair_list_mm/2,
    to_pair_list_with_mm/3,
    project_keys_mm/3,
    project_values_mm/3, 
    sort_values_frequency_mm/3
]).

/** <module> Multimap of elements of type A to elements of type B.

Implementation:  
type multimap<A,B> = map < A , set<B> >
where every value is a non-empty set.

This type uses literal programming 
@author Diego Alonso
@license GPL
*/

:- use_module(list_map,[
    insert_lm/4,maps_lm/3,lookup_lm/3,delete_lm/3,keys_lm/2,values_lm/2,
    zip_lm/3,project_lm/3,open_cursor_lm/4,close_cursor_lm/3
]).
:- use_module(set_list,[
    insert_sl/3,contains_sl/2,cardinal_sl/2,remove_sl/3,union_sl/3,
    unions_sl/2,intersection_sl/3,difference_sl/3
]).
:- use_module(maybe,[eval_maybe/3]).
:- use_module(multiset,[from_set_ms/2, union_ms/3, sum_ms/3]).
:- use_module(list_utils, [concat_lu/2]).

/*
empty_mm( ? MMap : multimap<_,_>) is det. 

MMap is the empty multimap, that contains no pairs. 
*/
empty_mm([]). 

/*
put_mm(
    + MMap : multimap<K,V>, + Key : K, + Value : V, - NMMap : multimap<K,V>
) is det. 

NMMap is the result of adding the mapping from Key to Value in MMap. If MMap 
already maps Key to Value, then the predicate succeeds and MMap = NMMap.
*/
put_mm( MMap, Key, Value, NMMap) :-
    open_cursor_lm( MMap, Key, MVals, Cursor),
    eval_maybe(MVals,[],Vals),
    insert_sl( Vals, Value, NVals),
    NMVals = [(Key,NVals)],
    close_cursor_lm( Cursor, NMVals ,NMMap ).

/*
put_values(
    + MMap : multimap<K,V>, + Key : K,  + Values : set<V>,
    - NMMap : multimap<K,V>
) is det.

NMMap is the result of adding to MMap the mappings from Key to each Value
in Values. 

*/
put_values_mm( MMap, _Key, [], MMap) :- !.
put_values_mm( MMap, Key, Values, NMMap) :-
    open_cursor_lm( MMap, Key, MVals, Cursor),
    eval_maybe( MVals, [], Vals),
    union_sl( Vals, Values, NVals), 
    close_cursor_lm(Cursor, [(Key,NVals)] ,NMMap).
    
/*
put_keys_mm( 
    + MMap : multimap<K,V>, + Keys : set<K>, + Value : V, 
    - NMMap : multimap<K,V>
) is det.

NMMap is the result of adding to MMap a mapping from each key in Keys to Value.
*/
put_keys_mm( MMap , [], _Value, MMap).
put_keys_mm( MMap , [Key|Keys], Value, NMMap) :-
    put_mm( MMap, Key, Value, NMMap1),
    put_keys_mm( NMMap1 , Keys, Value, NMMap).

/*
maps_mm( + MMap:multimap<K,V> , +Key:K, +Value:V) is semidet. 

True if MMap contains the mapping from Key to Value. 
*/
maps_mm( MMap, Key, Value) :-
    lookup_lm( MMap, Key, Vals),
    contains_sl( Vals, Value).

/*
values_of_mm( + MMap : multimap<K,V>, + Key : K, - Vals : set<V>) is det.

The predicate fails if there are no values for Key.
*/
values_of_mm( MMap, Key, Vals) :-
    open_cursor_lm( MMap, Key, MVals, _Cursor),
    eval_maybe( MVals, [], Vals),
    Vals\=[].

/*
keys_of_mm( + MMap : multimap<K,V>, + Val : V , - Keys : set<K>) is det.

Keys is the set of Keys that are mapped to Val in MMap. 
*/
keys_of_mm( MMap, Val , Keys ) :- keys_of_x(MMap,Val,Keys).

keys_of_x( [], _Val, []).
keys_of_x( [MRec|MMap], Val, Keys) :-
    keys_of_xx( MRec, Val, Keys0, Keys),
    keys_of_x( MMap, Val, Keys0).
    
keys_of_xx( (AKey, AVals), Val, Keys, [AKey|Keys]) :-
    contains_sl(AVals,Val),
    !.
keys_of_xx( _MRec, _Val, Keys, Keys).

/*
count_keys_of_mm( + MMap : multimap<K,V>, + Value : V, - Count : int) is det. 

Count is the number of keys that map to Value in MMap.
*/
count_keys_of_mm( MMap, Value, Count) :-
    keys_of_mm( MMap, Value, Keys), 
    cardinal_sl( Keys, Count). 

/*
count_values_of( + MMap : multimap<K,V>, + Key : K, - Count : int) is det. 

Count is the number of values Keyt is mapped to in MMap. 
*/
count_values_of_mm( MMap, Key, Count) :-
    values_of_mm( MMap, Key, Vals),
    cardinal_sl( Vals, Count).
    
/*
keys_mm( + MMap : multimap<K,V>, - Keys : set<K>) is det.

Keys is the set of Keys of Multimap. 
*/
keys_mm( MMap, Keys) :- keys_lm( MMap, Keys).

/*
values_mm( + MMap : multimap<K,V>, - Vals : set<V>) is det.

Vals is the set of values in Multimap. 
*/
values_mm( MMap, Vals) :-
    values_lm( MMap, VSets),
    unions_sl( VSets, Vals).

/*
keys_multiset_mm( + MMap : multimap<K,V>, - KeysMS : set<K> ) is det.

Ogtains the multiset of the keys in multimap, in which the multiplicity of 
each key is the number of values it is mapped to in MMap. 
*/
keys_multiset_mm( [], [] ).
keys_multiset_mm( [ (Key,Vals) | MMap], [ (Key,Mult) | KeysMS] ) :-
    cardinal_sl( Vals, Mult), 
    keys_multiset_mm( MMap, KeysMS). 

/*
values_multiset_mm( + MMap : multimap<K,V>, - ValsMS : multiset<V>) is det.

Obtains the multiset of the values in multimap, in which the multiplicity of 
each value is the number of keys that map to it in MMap.
*/
values_multiset_mm( MMap, ValsMS) :-
    values_lm( MMap, Vals_Sets),
    values_multiset_x(Vals_Sets, [], ValsMS).
    
values_multiset_x( [] , ValsMs,ValsMs). 
values_multiset_x( [Vals|Vals_Sets] , ValsMs1,ValsMs) :-
    from_set_ms(Vals,MVals),
    sum_ms(MVals,ValsMs1,ValsMs2), 
    values_multiset_x(Vals_Sets,ValsMs2,ValsMs).

/*
remove_mm(
    + MMap : multimap<K,V>, + Key : K, + Value : V, - NMMap : multimap<K,V>
) is det. 

NMMap is the map that contains all mappings in MMap except for (Key,Value).    
*/
remove_mm( MMap, Key, Value, NMMap) :-
    open_cursor_lm( MMap, Key, MVals, Cursor ),
    remove_x( MVals, Key, Value, NMRec), 
    close_cursor_lm( Cursor, NMRec, NMMap).

remove_x( [], _Key, _Value, []).
remove_x( [Vals], Key, Value, NMRec) :- 
    remove_sl( Vals, Value, NVals),
    remove_xx( NVals, Key, NMRec).

remove_xx( [], _Key, []).
remove_xx( [NVal|NVals], Key, [ (Key,[NVal|NVals]) ] ).


/*
remove_key_mm( 
    + MMap : multimap<K,V>, + Key : K, - NMMap : multimap<K,V>
) is det.

NMMap is the result of removing from MMap all the pairs which key is Key. 
*/
remove_key_mm( MMap, Key, NMMap) :- delete_lm( MMap, Key, NMMap).

/*
remove_value_mm(
    + MMap : multimap<K,V>, + Val : V, - NMMap : multimap<K,V>
) is det.

NMM, ap is the result of removing from MMap all the pairs which value is Val.
*/
remove_value_mm([],_Val,[]).
remove_value_mm([ (AKey, AVals) | MMap1 ],Val,NMMap) :-
    remove_value_x( AKey, AVals, Val, NMMap1, NMMap), 
    remove_value_mm(MMap1,Val,NMMap1).

remove_value_x( AKey, AVals, Val, NMMap1, NMMap) :-
    remove_sl(AVals,Val,NVals),
    put_head( NVals, AKey, NMMap1, NMMap).

put_head( [], _Key, Map, Map).
put_head( [Val|Vals], Key, Map, [(Key,[Val|Vals])|Map]).


/*
join_mm( 
    + MMapA : multimap<K,V>, + MMapB : multimap<K,V>, - NMMap : multimap<K,V>
) is det.

NMMap is the join or union of the multimaps MMapA and MMapB, which means that 
NMMap maps all pairs (K,V) that are mapped either in MMapA or in MMapB.
*/
join_mm( MMapA, MMapB, NMMap) :-
    zip_lm( MMapA, MMapB, ZMMap), 
    join_x( ZMMap, NMMap).

join_x([], []).
join_x([ (Key, MVals) | ZMM1 ],  [ (Key, NVals)  | NMM1] ) :-
    join_xx( MVals, NVals),
    join_x(ZMM1, NMM1).

join_xx( left( Vals) , Vals).
join_xx( right(Vals), Vals). 
join_xx( both(ValsA,ValsB), NVals) :- union_sl(ValsA,ValsB,NVals).

/*
inverse_mm( + MMap : multimap<K,V> , - InvMMap : multimap<K,V>)

NMMap is the multimap that is the inverse of MMap, that is to say NMMap contains
a mapping (V,K) if and only if MMap contains the mapping (K,V).

*/
inverse_mm( MMap, InvMMap ) :- inverse_x( MMap, [], InvMMap).

inverse_x( [], InvMMap, InvMMap).
inverse_x( [ (Key,Vals)|MM1 ], NMM0 , InvMMap) :-
    put_keys_mm( NMM0, Vals, Key, NMM1), 
    inverse_x( MM1, NMM1, InvMMap).

/*
project_keys_mm( 
    + MMap : multimap<K,V>, + Keys : set<K>, - NMMap : multimap<K,V
) is det.

NMMap is the multimap that contains all the mappings in MMap which 
key is contained in Keys. 
*/
project_keys_mm( MMap, Keys, NMMap) :- project_lm( MMap, Keys, NMMap).

/*
project_values_mm(  
    + MMap : multimap<K,V>, + Vals : set<V>, - NMMap : multimap<K,V>
) is det.

NMMap is the multimap that contains all the mappings in MMap which 
value is contained in Vals. 
*/
project_values_mm([],_Vals,[]).
project_values_mm([ (Key,OVals) | MM1],Vals,NMMap) :- 
    project_values_x( Key,OVals,Vals, NMM1, NMMap), 
    project_values_mm(MM1,Vals,NMM1).

project_values_x( Key,OVals,Vals, NMM1, NMMap) :- 
    intersection_sl(OVals,Vals,NVals),
    put_head( NVals, Key, NMM1, NMMap).

/*
from_map_mm( +LMap:map<K,V>, -MMap:multimap<K,V>) is det.

MMap is the multimap that contains the pairs <k,v> that are also mapped 
in LMap.
*/
from_map_mm( [] , []).
from_map_mm( [ (Key,Val) | LMap ]  , [ (Key, [Val])| MMap ]) :- 
    from_map_mm(LMap, MMap). 

/*
to_pair_list_mm( +MMap:multimap<K,V> , -PList:list<(K,V)>) is det.

PList is a sorted pair list that contains all pairs (k,v) such that 
the multimap MMap maps k with v. 

Example: to_pair_list_mm( [ (a , [1,2] ) , (b , [3,4] ) ], [
    (a,1) , (a,2) , (b,3) , (b,4) 
]).
*/
to_pair_list_mm( MMap, Pairs) :- to_pair_list_with_mm( ',' , MMap, Pairs).
    
/*
to_pair_list_with_mm( 
    + Func: ,
    + MMap: multimap<K,V>,
    - Terms: Func<K,V>
) is det. 
*/
to_pair_list_with_mm( Func, MMap, Pairs) :- 
    to_pair_list_with_x( MMap, Func, Pairs ). 
    
to_pair_list_with_x( [], _Func, [] ).
to_pair_list_with_x( [ (Key,Vals) | MMap ], Func, Pairs ) :- 
    to_pair_list_with_xx( Vals, Key, Func, Pairs_x, Pairs ), 
    to_pair_list_with_x( MMap, Func, Pairs_x ).

to_pair_list_with_xx( [], _Key, _Func, Pairs, Pairs ).
to_pair_list_with_xx( [Val|Vals], Key, Func, Pairs_x, [Pair|Pairs_xx]) :- 
    Pair =.. [Func , Key, Val],
    to_pair_list_with_xx( Vals, Key, Func, Pairs_x, Pairs_xx).

/*
from_pair_list_mm( +Pair_List:list<(K,V)> , -MMap:multimap<K,V> ) is det.

MMap is the multimap that maps two elements k,v if and only if Pair_List 
contains the pair (k,v)
*/
from_pair_list_mm( Pairs, MMap ) :- from_pair_list_x( Pairs, [], MMap). 

from_pair_list_x( [], MMap, MMap). 
from_pair_list_x( [Pair|Pairs], MMap_1, MMap) :- 
    from_pair_list_xx( Pair, MMap_1,MMap_2), 
    from_pair_list_x( Pairs, MMap_2, MMap).

from_pair_list_xx( (Key,Val) , MMap_1, MMap_2) :- 
    put_mm( MMap_1 , Key , Val , MMap_2).

/*
compose_mm( 
    + MMap_A : multimap<A,B>, + MMap_B : multimap <B,C>, 
    - NMMap:multimap<A,C> )
is det.

NMMap is the multimap that maps a pair (a,c) if and only if 
there exists some element B such that 
MMapA.maps(a,B) && MMapB.maps(B,c).
*/

% First loop: running through the pairs (Key,Vals of MapA)
compose_mm( [] , [], []). 
compose_mm( [] , [_|_], []). 
compose_mm( [_|_], [] , []). 
compose_mm( [ (KeyA,BVals) |MMapA], MMapB, [(KeyA,CVals)|NMMap]) :- 
    compose_mm( MMapA, MMapB , NMMap), 
    compose_x( BVals, MMapB, [], CVals). 

% Second loop: running through the values of the pair of MapA. 
compose_x( [] ,          _MMapB, CVals,   CVals).
compose_x( [BVal|BVs] ,  MMapB, CVals1, CVals) :-
    compose_x( BVs, MMapB, CVals1, CVals2),
    values_of_mm( MMapB, BVal, CVals3),
    union_sl( CVals2, CVals3, CVals).

/*
sort_values_frequency_mm( 
    + MMap : multimap<K,V>, + Vals:set<V>, - Queue:list<V>
) is det.
*/
sort_values_frequency_mm( MMap, Vals, Queue) :-
    frequencies( Vals, MMap, [], Freq_MM),
    values_lm( Freq_MM, Freq_Queues),
    concat_lu( Freq_Queues, Queue).

frequencies( [], _MMap, Freq_MM, Freq_MM).
frequencies( [Val|Vals], MMap, FMM0, Freq_MM) :-
    frequencies_x( Val, MMap, FMM0, FMM1), 
    frequencies( Vals, MMap, FMM1, Freq_MM).

frequencies_x( Val, MMap, FMM0, FMM1) :- 
    count_keys_of_mm( MMap, Val, Freq),
    put_mm( FMM0, Freq, Val, FMM1).
