/*
    Copyright (C) 2009  E.Albert, P.Arenas, S.Genaim, G.Puebla, and D.Zanardini
                        https://costa.ls.fi.upm.es

    This program is free software: you can redistribute it and/or modify it 
    under the terms of the GNU General Public License as published by the Free
    Software Foundation, either version 3 of the License, or (at your option) 
    any later version.

    This program is distributed in the hope that it will be useful, but WITHOUT 
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

:-module(list_map,[
    empty_lm/1,
    size_lm/2,
    maps_lm/3,
    lookup_lm/3,
    insert_lm/4,
    key_of_lm/3,
    delete_lm/3,
    update_lm/5,
    keys_lm/2,
    values_lm/2,
    project_lm/3,
    fillup_lm/4, 
    join_lm/3,
    meet_lm/3,
    split_lm/5,
    is_submap_lm/2,
    compose_lm/3,
    zip_lm/3,
    open_cursor_lm/4,
    close_cursor_lm/3, 
    product_lm/3,
    map_values_lm/3,
    check_values_lm/2
]).

/** <module> A Map (or table) of Keys to Values, which is a finite injective 
function from a type of terms Keys to another type of terms Vals. 

This module defines operations for processing Maps, that are implemented as a
list of pairs (Key,Value), sorted by the Keys and without repeated keys. 

type map<K,V> = list <(K,V)>  where
 * the list is syntactically sorted by the keys and
 * there are no two records with the same key

@author Diego Alonso
@license GPL
*/

:- use_module(list_utils,[length_lu/2]).
:- use_module(maybe     ,[eval_maybe/3]).
:- use_module(pair_list,[firsts_pl/2,seconds_pl/2, lookup_second_pl/3 ]). 
:- use_module(set_list, [intersection_sl/3,is_subset_sl/2,contains_sl/2]). 

/*
empty_lm( + Map : map<_,_>) is det. 

Map is the empty map, that maps no key to no value. 
*/
empty_lm([]).

/*
insert_lm( + Map : map<K,V>, + Key : K, + Val : V, - NMap : map<K,V> ) is det. 
 
NMap is the Map that results from adding to Map the mapping of Key to Val.
If Map already contains a record of Key to another Old_Value,
then NMap won't map Key to Old_Val, but to the newer Val. 

Examples: 
 * insert_lm( [], a, 1, NMap)          ?       NMap = [(a,1)].
 * insert_lm( [(a,1)], b, 2, NMap)     ?       NMap = [(a,1),(b,2)].
 * insert_lm( [(a,1)], a, 2, NMap)     ?       NMap = [(a,2)].
*/
insert_lm( [], Key, Val, [ (Key, Val) ] ).
insert_lm( [Rec|Recs], Key, Val, NRecs ) :-
    Rec = ( RKey , _OVal ),
    compare( Comp, RKey, Key), 
    put_x( Comp, [Rec|Recs], Key, Val, NRecs). 

put_x( <, [Rec|Recs], Key, Val, [Rec|NRecs]) :- 
    insert_lm( Recs, Key, Val, NRecs ).
put_x( =, [_Rec|Recs], Key, Val, [NRec|Recs]) :-    NRec = ( Key, Val).
put_x( >, Recs, Key, Val, [NRec|Recs]) :-           NRec = (Key, Val).

/*
lookup_lm( + Map : map<K,V> , + Key : K , - Value : V ) is semidet. 

If Map contains some mapping with Key, then Value is unified to 
the value of that mapping. 

Examples: 
 *  lookup_lm( [], a, Val)            ?   false.
 *  lookup_lm( [(a,1)], a, Val)       ?   Val = 1.
 *  lookup_lm( [(a,1)], b, Val)       ?   false.
 
*/
lookup_lm( [(RKey,RVal)|Recs], Key, Val) :- 
    compare( Comp, RKey, Key), 
    lookup_x( Comp, Key, RVal, Recs, Val).

lookup_x( < , Key, _RVal, Recs, Val) :- lookup_lm(Recs,Key,Val).
lookup_x( = , _Key, Val, _Recs, Val).

/*
maps_lm( + Map : map<K,V> , + Key : K, + Value : V) is semidet. 

True if the term Key is mapped to the term Value in Map.
This predicate should not be used for retrieving information: 
if you Value is a variable, the predicate doesn't bind Value to the mapping of
Key (if any), it tells if Key is mapped to that variable.

Examples:
 * maps_lm( [(a,1)], a, 1)      ?       true.
 * maps_lm( [(a,1)], a, N)      ?       false.
 * maps_lm( [], a, 1)           ?       false.

*/
maps_lm( Map, Key, Val ) :- contains_sl( Map, (Key,Val) ). 

/*
key_of_lm( + Map : map<K,V> , + Val : V,  - Key : K) is nondet.

Gives in Key all the keys mapped to Val in Map. 
*/
key_of_lm( Map, Val, Key) :- lookup_second_pl( Map, Val, Key). 

/*
delete_lm( + Map : map<K,V> , ? Key : K, - NMap : map<K,V> ) is det.

NMap is the result of removing from Map a mapping of Key to any value.
If Map doesn't contain a mapping of Key, then NMap = Map.
*/
delete_lm( [], _Key, []).
delete_lm( [Rec|Recs], Key, NRecs ) :- 
    Rec = (RKey , _RVal),
    compare( Comp, RKey, Key), 
    remove_x( Comp, Rec, Recs, Key, NRecs ).
remove_x( < , Rec, Recs, Key, [Rec|NRecs] ) :- 
    delete_lm(Recs, Key, NRecs ).
remove_x( = , _Rec, Recs, _Key, Recs ).
remove_x( > , Rec, Recs, _Key, [Rec|Recs] ).

/*
update_lm( + Map:map<K,V>, + Key:K, -OVal:V, +NVal:V, -NMap:map<K,V>). 
*/
update_lm( Map, Key, OVal, NVal, NMap) :- 
    open_cursor_lm( Map, Key, [OVal], Cursor), 
    close_cursor_lm( Cursor, [(Key,NVal)], NMap). 

/*
keys_lm( + Map : map<K,_> , -Keys : set<K>) is det. 

Keys is the set that contains all elements of type Key that are mapped 
to some value in Map.  
*/
keys_lm( Map, Keys ) :- firsts_pl( Map, Keys ). 

/*
values_lm( + Map : map<_,V> , - Values : list<V> ) is det.

Values is the list of values in the Map.
*/
values_lm( Map, Values ) :- seconds_pl( Map, Values ). 

/*
size_lm( + Map : map<K,V> , - Size : int) is det. 

Size is the number of records in Map.
*/
size_lm( Map, Size ) :- length_lu( Map, Size ). 

/*
project_lm( + Map : map<K,V> , + Keys : set<K> , - NMap : map<K,V> ) is det.

NMap is a map that contains those records of Map which key is contained in Keys.

project_lm( Map, Keys, NMap) -> forall Key:term, Val:term  
    maps_lm( NMap, Key, Val) <--> 
        maps_lm( Map, Key, Val), contains_sl( Keys, Key).

*/
project_lm( [], [], []) :- !.
project_lm( [], [_|_], []) :- !.
project_lm( [_|_], [], []) :- !. 
project_lm( [Rec|Recs], [Key|Keys], NMap) :- 
    Rec = (RKey, _RVal), 
    compare( Comp, RKey, Key), 
    project_x( Comp, [Rec|Recs], Recs_x, [Key|Keys], Keys_x, NMap_x, NMap), 
    project_lm( Recs_x, Keys_x, NMap_x ) .

project_x( <, [_Rec|Recs], Recs, Keys, Keys, NMap, NMap).
project_x( =, [Rec|Recs], Recs, [_Key|Keys], Keys, NMap, [Rec|NMap]). 
project_x( >, Recs, Recs, [_Key|Keys], Keys, NMap, NMap).

/*
  fillup_lm( + Map: map<K,V>, + Keys : set<K>, + Val : V, - NMap : map<K,V>) is det.

NMap is the union of Map and entries to link each Key in Key (but not in Map)
  and the value V.  
*/
fillup_lm( [], [], _ , []) :- !. 
fillup_lm( [], [K|Ks], V, [(K,V)|Map] ) :- !, 
    fillup_lm( [], Ks, V, Map).
fillup_lm( M,  [] , _, M) :- !.
fillup_lm( [R|Rs], [K|Ks], V, [NRec|NMap]) :-
    R = (RK,_RV),
    compare( Comp, K, RK),
    fillup_x( Comp,  [R|Rs], Rs_x, [K|Ks], Ks_x, V, NRec),
    fillup_lm( Rs_x, Ks_x, V, NMap).

fillup_x( <,      Rs , Rs, [K|Ks], Ks, V, (K,V)).
fillup_x( =, [Rec|Rs], Rs, [_|Ks], Ks, _, Rec  ).
fillup_x( >, [Rec|Rs], Rs,    Ks , Ks, _, Rec  ).
    
    



/*
join_lm ( + MapA : map<K,V>, + MapB : map<K,V>, - Join : map<K,V>) is semidet.

Join is the joint map of MapA and MapB, that is to say it's the minimal map 
that contains all the pairs of MapA and MapB.
This is a partial operation: in order to succeed MapA and MapB must hold that
if there is a common key, its associated value must also be the same.
*/
join_lm( [], [], []) :- !.
join_lm( [], [R|Rs], [R|Rs]) :- !.
join_lm( [R|Rs], [], [R|Rs]) :- !.
join_lm( [RecA|MapA], [RecB|MapB], [JRec|Join] ) :-
    RecA = (KeyA, _ValA), 
    RecB = (KeyB, _ValB), 
    compare( Comp, KeyA, KeyB ), 
    join_x( Comp, [RecA|MapA], MapA_x, [RecB|MapB], MapB_x, JRec ),
    join_lm( MapA_x, MapB_x, Join).
    
join_x( <, [RecA|MapA], MapA, MapB, MapB, RecA ).
join_x( =, [RecA|MapA], MapA, [RecB|MapB], MapB, RecA ) :- RecA == RecB. 
join_x( >, MapA, MapA, [RecB|MapB], MapB, RecB ).

/*
meet_lm( + MapA : map<K,V>, + MapB : map<K,V> , - Meet : map<K,V> ) is det. 

Meet is the map that contains all the key-value pairs that are in both maps. 
*/
meet_lm( MapA, MapB, Meet ) :- intersection_sl( MapA, MapB, Meet). 

/*
split_lm( 
    + Map:map<K,V> , +Key:K , -Pref:map<K,V>, -MVal:maybe<V>, -Post:: map<K,V>
) is det. 
*/
split_lm( Map, Key, Prefix, MVal, Post ) :- 
    open_cursor_lm( Map, Key, MVal,  ( Prefix, [], Post) ).

/*
*/
is_submap_lm( SubMap, SuperMap ) :- is_subset_sl( SubMap, SuperMap). 

/*
zip_lm( + MapA : map<K,V>, + MapB : map<K,W>, 
    - Zip : map < K,(maybe<V>,maybe<W>)
) is det. 

ZipMap is the map that contains all keys that are either in MapA and MapB,
and which values are the pairs ( MA, MB) where 
 * MA is the maybe value of Key in MapA (null if MapA doesn't contain Key).
 * MB is the maybe value of Key in MapB (null if MapA doesn't contain Key).

*/
zip_lm( [], [], []) :- !.
zip_lm( [] , [RecB|MapB], [MRec|ZMap] ) :- !, 
    zip_right( RecB, MRec),
    zip_lm( [], MapB, ZMap ).
zip_lm( [RecA|MapA], [], [MRec|ZMap] ) :- !, 
    zip_left( RecA, MRec ),
    zip_lm( MapA, [], ZMap ).
zip_lm( [RecA|MapA] , [RecB|MapB] , [MRec|ZMap] ) :- 
    RecA = (KeyA,_ValA),
    RecB = (KeyB,_ValB),
    compare( Comp, KeyA, KeyB),
    zip_x1( Comp, RecA, RecB, MRec), 
    zip_x2( Comp, [RecA|MapA] , [RecB|MapB], MapA_x, MapB_x ), 
    zip_lm( MapA_x, MapB_x, ZMap ). 

zip_left( (E,V) , (E,left(V) ) ).
zip_right( (E,V) , (E,right(V) ) ).

zip_x1( <, (Key,LVal), _RecB,       (Key,left(LVal))).
zip_x1( =, (Key,LVal), (Key,RVal),  (Key, both(LVal,RVal))). 
zip_x1( >, _RecA,      (Key,RVal),  (Key, right(RVal) )). 

zip_x2( < , [_|MapA] , MapB     , MapA, MapB ).
zip_x2( = , [_|MapA] , [_|MapB] , MapA, MapB ).
zip_x2( > ,     MapA , [_|MapB] , MapA, MapB ).

/*
product_lm( + AMap:map<KA,VA>, + BMap:map<KB,VB> - PMap:map<(KA,KB),(VA,VB)>)

*/
product_lm( [], _, []).
product_lm( [_|_], [], []) :- !. 
product_lm( [RecA|MapA], [RecB|MapB], Prod ) :- 
    product_x( [RecB|MapB], RecA, Prod_x, Prod), 
    product_lm( MapA, [RecB|MapB], Prod_x). 

product_x( [], _, Prod, Prod).
product_x( [RecB|MapB], RecA, Prod_Tail, [ProdRec|Prod_x]) :- 
    product_xx( RecA, RecB, ProdRec), 
    product_x( MapB, RecA, Prod_Tail, Prod_x). 

product_xx( (KA,VA), (KB,VB), ( (KA,KB), (VA,VB) ) ). 

/*
compose_lm( + MapA:map<A,B> , + MapB:map<B,C> , - CMap: map<A,C>) is det.

CMap is the composition of MapA and MapB, i.e. it's the map such that 
CMap.contains( (a,c) ) iff exists B :: 
    MapA.maps(a,b) && MapB.maps(b,c)

*/
compose_lm( [] , _, []).
compose_lm( [_|_], [] , []) :- !.
compose_lm( [ (KeyA,ValB) | MapA], [RecB|MapB], MapC) :-
    compose_x( KeyA, ValB, [RecB|MapB], MapC1, MapC),
    compose_lm( MapA, [RecB|MapB], MapC1).

compose_x( KeyA, ValB, MapB, MapC1, MapC) :-
    lookup_lm(MapB, ValB, ValC)
    ->  MapC = [(KeyA, ValC) | MapC1]
    ;   MapC = MapC1.
    
/*
open_cursor_key_lm( 
    + LMap:map<K,V>, + Key:K, - MVal:maybe<V>, - Cursor:cursor_lm<K,V>
) is det.

Opens a cursor in LMap at the point defined by Key. 

( Pred , TailPred, Key , Succ)
- Pred: an open list (tail is a variable), with all records before Key.
- TailPred: the variable that holds the Tail of the Pred list. 
- Key: the key that splits Pred and Succ
- Succ: a list map with all the pairs after Key. 
*/
open_cursor_lm( Map, Key, MVal, Cursor) :-
    Cursor = ( Prefix, TailVar, Tail),
    open_cursor_x( Map, Key, Prefix, TailVar, Tail, MVal).

open_cursor_x( [], _Key, TailVar, TailVar,[], [] ).
open_cursor_x( [Rec|Recs], Key, Prefix, TailVar, Tail, MVal) :- 
    Rec = ( RKey, _RVal ), 
    compare( Comp, RKey, Key ), 
    open_cursor_xx( Comp, [Rec|Recs], Key, Prefix, TailVar, Tail, MVal).

open_cursor_xx( < , [Rec|Recs], Key, [Rec|Prefix], TailVar, Tail, MVal) :- 
    open_cursor_x( Recs, Key, Prefix, TailVar, Tail, MVal ).
open_cursor_xx( = , [Rec|Recs], _Key, TailVar, TailVar, Recs, [RVal] ) :- 
    Rec = ( _RKey, RVal).
open_cursor_xx( > , [Rec|Recs], _Key, TailVar, TailVar, [Rec|Recs], [] ).

/*
close_cursor_lm( 
    + Cursor : cursor_lm<K,V>, +MVal : maybe<V>, - LMap : map<K,V>
) is det.

*/
close_cursor_lm( Cursor, MRec, LMap) :- close_cursor_x( MRec, Cursor, LMap ).
close_cursor_x( [], (LMap, Succ , Succ), LMap ).
close_cursor_x( [Rec], (LMap, [Rec|Succ], Succ), LMap ).


:-meta_predicate check_values_lm(1,+).

check_values_lm(Pred,Map):-
	maplist(check_second(Pred),Map).

:-meta_predicate map_values_lm(1,+,-).
map_values_lm(Pred,Map,Map2):-
	maplist(apply_to_second(Pred),Map,Map2).

check_second(Pred,(_Key,Elem)):-
	call(Pred,Elem).
	
apply_to_second(Pred,(Key,Elem),(Key,Elem2)):-
	call(Pred,Elem,Elem2).
	
	

