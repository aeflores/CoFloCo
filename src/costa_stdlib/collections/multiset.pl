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

:- module(multiset,[
    empty_ms/1,
    add_ms/3, add_many_ms/4,
    multiplicity_ms/3, cardinal_ms/2, contains_ms/2, elements_ms/2,
    elements_list_ms/2, cardinal_list_ms/2,
    
    remove_ms/3, remove_many_ms/4, remove_all_ms/3,
    is_subset_ms/2, is_superset_ms/2,
    add_set_ms/3, add_list_ms/3,  remove_set_ms/3,
    sum_ms/3,  difference_ms/3, strictdiff_ms/3, bidifference_ms/5,
    union_ms/3, intersection_ms/3,
    product_ms/3,
    replicate_ms/3, divide_ms/3, exact_divide_ms/3, divides_ms/2, 
    filter_divisible_ms/3, 
    substitute_ms/4,
    project_ms/3,
    subset_polydown_ms/2,  subset_polynup_ms/2,
    subset_size_down_ms/2,  subset_size_up_ms/2,
    subset_max_size_ms/3,  subset_min_size_ms/3,  subset_size_ms/3,
    to_list_ms/2,  from_list_ms/2, from_set_ms/2,
    super_multiset_set_card_ms/4, super_multiset_set_max_card_ms/4,
    multiset_set_max_card_ms/3,  multiset_set_card_ms/3,
    filter_max_card_ms/3, filter_card_ms/3, filter_min_card_ms/3
]).

/** <module> Multiset (a.k.a. Bag) of elements of any type (even variables). 
A Bag is a data structure that may contain any element with a different 
multiplicity. 

The bag is implemented as 
type multiset<A> = map<A,integer> where
for each pair (A,N), the number N is the multiplicity of the element A in the 
multiset, and it must hold that N >= 0. 

Example: a multiset of chars that contains 'a' two times 'a', three 'b' and 
one 'c' is written as  '[ (a,2) , (b,3) , (c,1) ]'.

@author Diego Alonso
@license GPL
*/

:- use_module( pair_list, [zip/3,unzip/3]). 
:- use_module(maybe,[eval_maybe/3]).
:- use_module(list_map,[ insert_lm/4,maps_lm/3,lookup_lm/3,delete_lm/3,keys_lm/2,
    values_lm/2,project_lm/3,zip_lm/3,open_cursor_lm/4,close_cursor_lm/3]).
:- use_module(stdlib(arithmetic_utils),[exact_divide_list/3,gcd_list/2,
    max/3,min/3,sum_list/2,increment/3,decrement/3,divides/2,divide_list/3]).
:- use_module( stdlib(fraction_list), [multiply_frl/3]). 

/*
empty_ms( ? MSet : multiset<_>) is det. 

MSet is the empty multiset. 
*/
empty_ms( [] ).

/*
add_ms( + MSet : multiset<A>, ? Elem : A, - NMSet : multiset<A> ) is det.

NMSet is the result of adding to MSet one instance of Elem.

Examples:
 * add_ms( [(a,1),(b,1)], a, N) ?    N = [ (a,2) , (b,1) ].
 * add_ms( [(a,1),(b,1)], c, N) ?    N = [ (a,1) , (b,1) ,(c,1) ].
*/
add_ms( MSet, Elem, NMSet) :- add_many_ms( MSet, 1, Elem, NMSet).

/*
add_many_ms( 
    + MSet : multiset<A>, + Mult : int, + Elem : A, - NMSet : multiset<A>
) is det. 

NMSet is the result of adding to MSet Mult instances of Elem.

Examples: 
 * add_many_ms( [(a,1),(b,1)], 2, a, N) ?    N = [ (a,3) , (b,1) ].
 * add_many_ms( [(a,1),(b,1)], 0, a, N) ?    N = [ (a,1) , (b,1) ].
*/
add_many_ms( MSet, 0, _Elem, MSet) :- !. 
add_many_ms( MSet, Mult, Elem, NMSet) :-    
    % Precondition: Num is a non-zero  number. 
    integer(Mult),
    % implicit by cut: Mult =\= 0,
    open_cursor_lm( MSet , Elem , MMult , Cursor),
    eval_maybe( MMult, 0 , Mult1),
    NMult is Mult1 + Mult,
    (NMult =< 0 -> NMMult = [] ; NMMult = [(Elem,NMult)]),
    close_cursor_lm(Cursor, NMMult, NMSet).

/*
multiplicity_ms( + MSet : multiset<A>,  + Elem : A, - Mult : int) is det.  

Mult is the multiplicity of Elem in MSet. If Elem is not in set, Mult is zero. 

Examples: 
 * multiplicity_ms( [ (a,3), (b,2) ], a, Mult) ?   Mult = 3. 
 * multiplicity_ms( [ (a,3), (b,2) ], c, Mult) ?   Mult = 0. 
*/
multiplicity_ms( MSet, Elem, Mult) :-
    lookup_lm( MSet , Elem , Mult),
    !.
multiplicity_ms( _MSet, _Elem, 0).

/*
contains_ms( + MSet : multiset<A>, + Elem : A ) is semidet. 

Returns true if MSet contains at least one Elem, that is to say if
the multiplicity of Elem in MSet is greater or equal to 1. 
It fails if MSet doesn't contain any element. 

Examples: 
 * contains_ms( [ (a,3), (b,2) ], a) ?   true. 
 * contains_ms( [ (a,3), (b,2) ], c) ?   false. 
*/
contains_ms( MSet, Elem) :- lookup_lm( MSet, Elem, _Mult).

/*
remove_ms( + MSet : multiset<A>, + Elem : A, - NMSet : multiset<A> ) is det. 

NMSet is the result of removing from MSet one instance of Elem.
If MSet doesn't contain Elem, the predicate still succeeds and NMSet= MSet.

Examples: 
* remove_ms( [ (a,2),(b,1)], a, NMSet) ?        NMSet = [(a,1),(b,1)].
* remove_ms( [ (a,2),(b,1)], b, NMSet) ?        NMSet = [(a,2)].
* remove_ms( [ (a,2),(b,1)], c, NMSet) ?        NMSet = [(a,2),(b,1)].
*/
remove_ms( MSet, Elem, NMSet) :- add_many_ms( MSet, -1, Elem, NMSet).

/*
remove_many_ms(
    + MSet : multiset<A>, + Mult : int, + Elem : A, - NMSet : multiset<A>
) is det. 

NMset is the result of removing Mult instances of Elem of NMSet. This 
predicate succeeds even if MSet.count(Elem) =< Mult.

Examples: 
 * remove_many_ms( [(a,2),(b,1)], 2, a, NMSet) ?    NMSet = [(b,1)]. 
 * remove_many_ms( [(a,2),(b,1)], 3, a, NMSet) ?    NMSet = [(b,1)]. 
 * remove_many_ms( [(a,2),(b,1)], 2, b, NMSet) ?    NMSet = [(a,2)]. 
 * remove_many_ms( [(a,2),(b,1)], 2, c, NMSet) ?    NMSet = [(a,2),(b,1)].
*/
remove_many_ms( MSet, Mult, Elem, NMSet ):-
    integer(Mult), 
    NMult is 0 - Mult,
    add_many_ms( MSet, NMult, Elem, NMSet ). 

/*
remove_all_ms( 
    + MSet : multiset<A>, + Elem : A , - NMSet : multiset<A>
) is det. 

NMSet is the result of removing from MSet all appearances of Elem.
This predicate always succeeds even if MSet doesn't contain Elem, 
in which case NMSet is equals to MSet.

Examples:
 * remove_all_ms( [(a,2),(b,1)], a, NMSet) ?        NMSet = [(b,1)]. 
 * remove_all_ms( [(a,2),(b,1)], c, NMSet) ?        NMSet = [(a,2),(b,1)].
*/
remove_all_ms( MSet, Elem, NMSet ) :- delete_lm( MSet, Elem, NMSet ).

/*
add_set_ms( 
    + MSet : multiset<A>,  + Set : set<A>, - NMSet : multiset<A>
) is det. 

NMSet is the result of adding to MSet one instance of each elem in Set.
*/
add_set_ms( MSet, [], MSet ) :- !.    
add_set_ms( MSet, [Elem|Set], NMSet ) :-
    add_ms( MSet, Elem, NMS1 ),
    add_set_ms( NMS1, Set, NMSet ).

/*
add_list_ms( 
    + MSet : multiset<A>, + Elems : list<A>, - NMSet : multiset<A> 
) is det.

NMSet is the result of adding to MSet one instance of each elem in Elems.
*/
add_list_ms( MSet, [], MSet) :- !.
add_list_ms( MSet, [E|Es], NMSet) :-
    add_ms( MSet, E, NMS1),
    add_list_ms( NMS1, Es, NMSet).

/*
remove_set_ms( 
    + MSet : multiset<A>, + Set : set<A>, - NMSet : multiset<A>
) is det. 

NMSet is the result of removing from MSet one instance of each elem in Set.
*/
remove_set_ms( MSet, Set, NMSet) :- 
    from_set_ms( Set, DMSet), 
    difference_ms( MSet, DMSet, NMSet).

/*
remove_list_ms(
    + MSet : multiset<A>, + Elems : list<A>, - NMSet : multiset<A>
) is det.

NMSet is the result of removing from MSet each element in Elems once.
*/
remove_list_ms( MSet, List, NMSet) :- remove_list_x( List, MSet, NMSet). 

remove_list_x( [], MSet, MSet).
remove_list_x( [E|Es], MSet, NMSet) :-
    remove_ms( MSet, E, NMS1),
    remove_list_x( NMS1, Es, NMSet).

/*
cardinal_ms( + MSet : multiset<_> , - Card : int) is det.

Card is the cardinal of MSet, that is to say the total number of elements or, 
simmilarly, the sum of the multiplicities of each element. 

Postcondition: Card >= 0. 

Examples: 
 * cardinal_ms( [], C)          ?       C = 0. 
 * cardinal_ms( [(a,3),(b,2)],C) ?       C = 5.
*/
cardinal_ms( MSet, Card) :-
    values_lm( MSet, Mults),
    sum_list( Mults, Card).

/*
cardinal_list_ms( + MSets : list<multiset<_>>, - Cards : list<int>  ) 
*/
cardinal_list_ms( [], [] ).
cardinal_list_ms( [MSet|MSets] , [Card|Cards] ) :- 
    cardinal_ms( MSet, Card), 
    cardinal_list_ms( MSets, Cards). 


/*
elements_ms( + MSet : multiset<A>, - Elems : set<A> ) is det.

Elems is the set of elements contained at least once in MSet. 

Examples:
 * elements_ms( [],Elems)                   ?   Elems = [].
 * elements_ms( [(a,2),(b,1)],Elems)        ?   Elems = [a,b].
 * elements_ms( [(a,2),(b,1),(c,3)],Elems)  ?   Elems = [a,b,c]. 
  
*/
elements_ms( MSet, Elems) :- keys_lm( MSet, Elems). 

/*
elements_list_ms( 
    + MSets : list<multiset<A>> , - Elems_Lists : list<set<A>>
) is det.  
*/
elements_list_ms( [], [] ). 
elements_list_ms( [Ms|Mss], [EL|ELs] ) :- 
    elements_ms( Ms, EL ), 
    elements_list_ms( Mss, ELs ). 
    
   
/*
is_subset_ms( + MSetA : multiset<A> , + MSetB : multiset<B>) is semidet. 

MSetA is a subset of MSetB, that is to say for every element E in MSetA 
it holds that  MSetA.multiplicity(E) =< MSetB.multiplicity(E).

Examples: 
 * is_subset_ms( [(a,2),(b,1)] , [(a,2),(b,1)]) ?      true
 * is_subset_ms( [(a,2),(b,1)] , [(a,3),(b,1)]) ?      true
 * is_subset_ms( [(a,2),(b,1)] , [(a,1),(b,1)]) ?      false
*/
is_subset_ms( Sub, Super) :- is_superset_ms( Super, Sub).

is_subset_ms( [], _Super).
is_subset_ms( [RSub|Sub], [RSup|Super] ) :-
    RSub = ( ESub, _MSub),
    RSup = ( ESup, MSup),
    compare( Comp, ESub, ESup),
    is_subset_x( Comp, [RSub|Sub], MSup, NSub),
    is_subset_ms( NSub, Super).

is_subset_x( = , [ (_ESub,MSub) |Sub], MSup, Sub) :-  MSub =< MSup.
is_subset_x( > , Sub, _MSup, Sub).

/*
is_superset_ms( + Super: multiset<A> , + Sub : multiset<B>) is semidet. 

Decides if Super is a superset of Sub, i.e if for every Elem:A,
Super.count(Elem) >= Sub.count(Elem). 

Examples: 
 * is_superset_ms( [(a,2),(b,1)] , [(a,2),(b,1)]) ?      true
 * is_superset_ms( [(a,2),(b,1)] , [(a,3),(b,1)]) ?      false
 * is_superset_ms( [(a,2),(b,1)] , [(a,1),(b,1)]) ?      true
*/
is_superset_ms( Sup, Sub ) :- is_subset_ms( Sub, Sup). 

/*
sum_ms(
    + MSetA : multiset<A>, + MSetB : multiset<A>, - Sum : multiset<A>
) is det. 

Sum is the sum of MSetA and MSetB, which means that for each elem  E in Sum, 
Sum.count(E) = MSetA.count(E) + MSetB.count(E).

Properties of the Sum:
 * Commutative:      sum(A,B,S) <--> sum(B,A,S). 
 * Associative:      sum(A,B,S1),sum(S1,C,S) <--> sum(B,C,S2),sum(A,S2,S).
 * Neutral element:  empty(E) --> add(A,E,A).
 * Superset:         sum(A,B,S) --> subset(A,S), subset(B,S)
*/
sum_ms( MSetA, MSetB, Sum) :-
    zip_lm( MSetA, MSetB, ZMSet ),
    sum_x( ZMSet, Sum).

sum_x( [], []).
sum_x(  [ (Elem,EMuls) |ZMSet] ,[ (Elem,Mul) | Sum]) :-
    sum_xx( EMuls, Mul),
    sum_x( ZMSet, Sum).

sum_xx( left(V), V).
sum_xx( right(V), V).
sum_xx( both(A,B), Sum ) :- Sum is A + B.  

/*
difference_ms(
    + MSetA : multiset<A>, + MSetB : multiset<A> , - Diff : multiset<A>
) is det. 

Diff is the difference of MSetA and MSetB. Formally, for every E in Diff, 
Diff.count(E) = max ( MSetA.count(E) - MSetB.count(E), 0)

Properties of the difference:
 * Neutral element:      empty(E) -> difference(A,E,A).
 * Subset:               difference(A,B,D) -->  subset(D,A)
 * Inverse of the sum:   sum(A,B,S) -> difference(C,B,A) , difference(C,A,B)
*/
difference_ms( MSetA, MSetB, Diff) :-
    zip_lm( MSetA, MSetB, ZMSet),
    difference_x( ZMSet, Diff).

difference_x( [], [] ).
difference_x( [ZRec|ZMS1], Diff ) :-
    difference_xx( ZRec, Diff1, Diff),
    difference_x( ZMS1, Diff1).

difference_xx( ZRec, Diff1, Diff) :-
    ZRec = ( Elem, Cards),
    difference_cards( Cards, M_Diff),
    insert_aux( M_Diff, Elem, Diff1, Diff).

difference_cards( left(A), A).
difference_cards( right(_), 0).
difference_cards( both(A,B), Diff) :-
    A > B 
    ->  Diff is A - B
    ;   Diff = 0.

insert_aux( 0, _Elem, Map, Map) :- !.
insert_aux( Mult, Elem, Map, [(Elem,Mult)|Map]).
    

/*
strictdiff_ms( 
    + Sup : multiset<A>, + Sub : multiset<A> , - SDiff : multiset<A>
) is semidet.

SDiff is the strict difference of the multisets Sup and Sub. 
Formally, for every E in Sup or Sub, it holds that: 
 * Sup.count(E) >= Sub.count(E) 
 * SDiff.count(E) = Sup.count(E) - Sub.count(E)

It's like the difference, but it only succeeds if the first MSet is a superset
of the second one.
*/
strictdiff_ms(MSetA, MSetB, NMSet) :-
    zip_lm(MSetA,MSetB,ZMSet),
    strictdiff_x(ZMSet,NMSet).

strictdiff_x([],[]).
strictdiff_x( [ ZRec | ZMap],SDiff) :-
    strictdiff_xx( ZRec, SDiff1, SDiff ), 
    strictdiff_x( ZMap, SDiff1 ). 

strictdiff_xx( ZRec, SDiff1, SDiff ) :- 
    ZRec = ( Elem, Cards), 
    strictdiff_cards( Cards,NCard ),
    insert_aux( NCard, Elem, SDiff1, SDiff ).

strictdiff_cards( left(A), A).
strictdiff_cards( both(A,B), SDiff) :-
    A >= B,
    SDiff is A - B.  

/*
union_ms( 
    + MSetA : multiset<A>, + MSetB : multiset<A>, - Union : multiset<A>
) is det. 
 
NMSet is the union of MSA and MSB, what menas that for all element E in NMSet, 
NMSet.multiplicity(E) = max( MSA.multiplicity(E) , MSB.multiplicity(E) ).

Properties of the Union: 
 * Commutative:   union(A,B,U) <--> union(B,A,U)
 * Asociative:    union(A,B,U1),union(N1,C,U) <--> union(B,C,U2),union(A,N2,U).
 * Neutral element:  empty(E) -> union(A,E,A).
 * Idempotency:      union(A,A,A)
 * Superset:         union(A,B,U) -->  subset(A,U), subset(B,U)
 * Minimal common superset: subset(A,C), subset(B,C), union(A,B,U)--> subset(U,C)

*/
union_ms( MSetA, MSetB, Union ) :-
    zip_lm( MSetA, MSetB, ZMSet ),
    union_x( ZMSet, Union ).

union_x( [], [] ).
union_x(  [ ZRec|ZMap] , [NRec|Union] ) :-
    union_xx( ZRec, NRec ),
    union_x( ZMap, Union ). 

union_xx( (Elem,Cards) , (Elem, NCard) ) :- union_cards(Cards,NCard). 

union_cards( left(V), V).
union_cards( right(V), V).
union_cards( both(A,B), Max) :- max(A,B,Max).

/*
intersection_ms( 
    + MSetA : multiset<A>, + MSetB : multiset<A>, - Inters : multiset<A>
) is det.
  
MSN is the intersection of MSetA and MSetA, which means that for every term E,
Inters.multiplicity(E) == min ( MSetA.multiplicity(E) , MSetB.multiplicity(E) )

Properies: 
 * Commutativity:  intersection(A,B,N) <-> intersection(B,A,N).
 * Associativity:  intersection(A,B,N1),intersection(N1,C,N) <-> 
                        intersection(B,C,N2),intersection(N2,A,N).
 * Idempotency:    intersection(A,A,A)
 * Subset:         intersection(A,B,N) --> subset(N,A), subset(N,B)
 * Maximal common subset: 
        intersection(A,B,N), subset(C,A), subset(C,B) --> subset(C,N).

Sum-difference-union-intersection equations: 
    sum(A,B,S) <--> union(A,B,U),intersection(A,B,I), sum(U,I,S)
*/
intersection_ms(MSetA, MSetB, Inters) :-
    zip_lm(MSetA,MSetB,ZMSet),
    intersection_x(ZMSet,Inters).

intersection_x( [], [] ).
intersection_x( [ ZRec | ZMS1], Inters ) :-
    intersection_xx( ZRec, Inters1, Inters ), 
    intersection_x(ZMS1,Inters1 ).

intersection_xx( ZRec, Inters1,Inters) :- 
    ZRec = ( Elem, Cards), 
    intersection_cards(Cards,NCard),
    insert_aux( NCard, Elem, Inters1, Inters).

intersection_cards( left(_), 0).
intersection_cards( right(_), 0).
intersection_cards( both(A,B), Min) :- min( A,B, Min).

/*
bidifference_ms( 
    + MSetA : multiset<A> , + MSetB : multiset<A> , 
    - ADiff : multiset<A> , - Inters:multiset<A> , - BDiff:multiset<A> 
) is det.
*/
bidifference_ms( MSetA, MSetB, ADiff, Inters, BDiff) :- 
    zip_lm(MSetA,MSetB,Zip),
    bidifference_x( Zip, ADiff, Inters, BDiff). 

bidifference_x( [],[],[],[]). 
bidifference_x([ ZRec | ZMS1], ADiff, Inters, BDiff) :-
    bidifference_xx(ZRec, Diff_A1, Inters1, Diff_B1, ADiff, Inters, BDiff),
    bidifference_x( ZMS1, Diff_A1, Inters1, Diff_B1). 

bidifference_xx( ZRec, Diff_A1, Inters1, Diff_B1, Diff_A, Inters, Diff_B) :-
    ZRec = (Elem,Cards), 
    bidiff_cards( Cards, DA, In, DB), 
    insert_aux( DA, Elem, Diff_A1, Diff_A),
    insert_aux( In, Elem, Inters1, Inters),
    insert_aux( DB, Elem, Diff_B1, Diff_B).

bidiff_cards( left(A), A, 0, 0) .
bidiff_cards( right(B), 0, 0, B).
bidiff_cards( both(A,B), DA, Min, DB) :- 
    min(A,B,Min), 
    DA is A - Min, 
    DB is B - Min. 

/*
replicate_ms( 
     + MSetB : multiset<A>, + Num : int ,- RepMS : multiset<A>
) is det.

RepMS is the multiset such that 
forall E : RepMS.multiplicity(E) = Num * MSet.multiplicity(E)

Precondition: N >= 0
*/

%pattern: precondition checking, processing. 
replicate_ms( [], _N,  [] ).
replicate_ms( [P|Ms], N, RMs ) :- replicate_x( N, [P|Ms], RMs ). 

replicate_x( 0, _, [] ) :- !. 
replicate_x( 1, MSet, MSet) :- !. 
replicate_x( N, MSet, RMset ) :-
    N >= 2,
    unzip( MSet, Elems, Mults),
    multiply_frl( Mults, N , NMults), 
    zip( Elems, NMults, RMset). 

/*
divide_ms
*/
divide_ms( [], _, [] ) :-! .
divide_ms( Ms, 1, Ms ) :- !. 
divide_ms( MSet, Div, QMSet ) :- divide_x( MSet, Div, QMSet). 

divide_x( [], _Div, []). 
divide_x( [P|MSet], Div, QMSet) :- 
    divide_xx( P, Div, QMSet_x, QMSet), 
    divide_x( MSet, Div, QMSet_x). 

divide_xx( P, Div, QMSet, [(E,NM)|QMSet]) :- 
    P = ( E,M), 
    M >= Div, 
    !,
    NM is M // Div.
divide_xx( _P, _Div, QMSet, QMSet). 

/*
exact_divide_ms( + MSet : multiset<A> , + Num : int , - NMSet : multiset<A> 
) is semidet. 

True 
Fails if some multiplicity is not divisable by num. 
*/
exact_divide_ms( [], _, [] ) :- !.
exact_divide_ms( Ms, 1, Ms ) :- !. 
exact_divide_ms( MSet, Div, QMSet ) :- 
    Div >= 2, 
    unzip( MSet, Elems, Mults ), 
    exact_divide_list( Mults, Div, NMults ), 
    zip( Elems, NMults, QMSet ). 

/*
is_divisible_ms( 
*/
divides_ms( MSet , Div ) :- 
    unzip( MSet, _Elems, Mults), 
    gcd_list( Mults, Gcd), 
    divides( Div, Gcd). 

/*
filter_divisible_ms( MSets, Div, Filt). 

*/   
filter_divisible_ms( [], _Div, []). 
filter_divisible_ms( [Ms|MSets], Div, Filt) :- 
    filter_divisible_x( Ms, Div, Filt_x, Filt), 
    filter_divisible_ms( MSets, Div, Filt_x). 

filter_divisible_x( Ms, Div, Filt, [Ms|Filt]) :- 
    divides_ms( Ms, Div), 
    !. 
filter_divisible_x( _Ms, _Div, Filt, Filt).

/*
product_ms(
    + MSetA : multiset<A>, + MSetB : multiset<A>, - Prod : multiset<A>
) is det.

NMSet is the cartesian product of MSetA and MSetB, which means that 
forall (X,Y) :  P.count( (X,Y) ) = A.count(X) * B.count(Y)

*/
product_ms( [] , [], []) :- !.
product_ms( [] , [_|_], []) :- !.
product_ms( [_|_], [] , []) :- !.
product_ms( [(A,MA) | MSetA] , [RecB|MSetB], ProdMS) :- 
    product_x([RecB|MSetB],A,MA,ProdMS1,ProdMS),
    product_ms(MSetA, [RecB|MSetB], ProdMS1).

product_x([] , _A , _MA, ProdMS, ProdMS).
product_x( [ (B,MB) | MSetB] , A, MA, ProdMS1, ProdMS) :- 
    NM is MA * MB, 
    ProdMS = [ ( (A,B) , NM) | ProdMS2], 
    product_x(MSetB, A, MA, ProdMS1,ProdMS2). 

/*
substitute_ms( 
    + MSet : multiset<A>, + ElemA : A, + ElemB : A, - NMSet : multiset<A>
) is det.

NMSet is the result of substituting ElemA by ElemB in MSet.
*/
substitute_ms( MSet, ElemA, ElemB, NMSet) :-    
    open_cursor_lm( MSet, ElemA, Cursor, MVal), 
    Cursor = ( MSet1, Tail, Tail),
    substitute_x( MVal, ElemB, MSet1, NMSet). 

substitute_x( [], _ElemB, NMSet, NMSet).
substitute_x( [Mult], ElemB, MSet1, NMSet) :- 
    add_many_ms( MSet1, Mult, ElemB, NMSet).

/*
project_ms( 
    + MSet : multiset<A>, + Elems : set<A>, - NMSet : multiset<A>
) is det.

NMSet is a multiset that contains only the elements (with multiplicity) that 
are in the set Elems. More formally, 

forall E : NMSet.mult(E) = if Elems.contains(E) then MSet.count(E) else 0. 
*/
project_ms( MSet, Elems, NMSet ) :- project_lm( MSet, Elems, NMSet ).

/*
to_list_ms( + MSet : multiset<A>, - List : list<A> ) is det.

List is a sorted list in which each element of MSet appears as many times as
its multiplicity in MSet.
*/
to_list_ms( [] , []).
to_list_ms( [ (Elem,Mult)|MSet], List) :- 
    to_list_x( Mult, Elem, List0, List), 
    to_list_ms( MSet, List0).

to_list_x( 0, _Elem, List, List) :- !. 
to_list_x( N, Elem, List0, [Elem|List]) :- 
    % Cut-implicit: N > 0
    NN is N -1, 
    to_list_x(NN,Elem,List0, List). 

/*
from_list_ms( + List : list<A>, - MSet : multiset<A>) is det.

MSet is the multiset that contains all the elements in List with a 
multiplicity that is the number of appearances of that element in the list. 
*/
from_list_ms( List, MSet) :- from_list_x( List, [], MSet).

from_list_x( [], MSet, MSet).
from_list_x( [Elem|List], MSet0, MSet) :- 
    add_ms( MSet0, Elem, MSet1), 
    from_list_x( List, MSet1, MSet).

/*
from_set_ms( + Set : set<A> , - MSet : multiset<A>) is det.

MSet is the multiset that contains all the elements in Set with a 
multiplicity of one.
*/
from_set_ms( [] , []).
from_set_ms( [E|Es], [(E,1) |Ms]) :- from_set_ms(Es,Ms).

/*
subset_polydown_ms( + MSet : multiset<A> , - Sub : multiset<A> ) is nondet.
    
This predicate returns in NMSet all submultisets of MSet, following a 
polynomial down strategy: 
if NMSetA is returned before NMSetB , then the polynomial interpretation 
of NMSetA is greater to the one of NMSetB.
*/
subset_polydown_ms([],[]).
subset_polydown_ms( [(Elem,Mult)|MS1] ,Sub) :-
    subset_polydown_x( Elem, Mult, Sub1, Sub), 
    subset_polydown_ms(MS1,Sub1).

subset_polydown_x( Elem, Mult, Sub1, Sub) :- 
    decrement(Mult,1,NMult),
    Sub = [ (Elem, NMult) | Sub1].
subset_polydown_x( _Elem, _Mult, Sub, Sub). % NMult = 0

/*
subset_polynup_ms( + MSet : multiset<A> , - NMSet : multiset<A>) is nondet. 
    
This predicate returns in NMSet all submultisets of MSet, following a 
polynomial up strategy: 
if NMSetA is returned before NMSetB , then the polynomial interpretation 
of NMSetA is lesser to the one of NMSetB.
*/
subset_polynup_ms([],[]).
subset_polynup_ms( [ (Elem,Mult) | MS1],Sub) :-
    subset_polynup_x( Elem, Mult, Sub1, Sub),
    subset_polynup_ms(MS1,Sub1).

subset_polynup_x( _Elem, _Mult, Sub, Sub). % NMult = 0
subset_polynup_x( Elem, Mult, Sub1, Sub) :- 
    increment(1,Mult,NMult),
    Sub = [ (Elem, NMult) | Sub1].

/*
subset_size_down_ms( + MSet : multiset<A>, - NMSet : multiset<A>) is nondet. 
    
This predicate returns in NMSet all submultisets of MSet, following a 
cardinal down  strategy: 
if NMSetA is returned before NMSetB , then the cardinal of 
NMSetA is greater to the one of NMSetB.
*/
subset_size_down_ms( MSet, Sub) :-
    cardinal_ms( MSet, Card),
    subset_max_size_ms( MSet, Card, Sub).

/*
subset_size_up_ms( + MSet : multiset<A> , - NMSet : multiset<A>) is nondet.

This predicate returns in NMSet all submultisets of MSet, following a 
cardinal up  strategy: 
if NMSetA is returned before NMSetB , then the cardinal of 
NMSetA is lesser to the one of NMSetB.
*/
subset_size_up_ms( MSet, Sub) :-
    cardinal_ms( MSet, Card),
    subset_min_size_ms( MSet, Card, Sub).

/*
subset_max_size_ms(
    + MSet : multiset<A>, + NCard : int, - Sub : multiset<A>
) is det.
    
Returns in NMSet all submultisets of MSet which cardinality is lesser or 
equal to NCard.
*/
subset_max_size_ms( MSet, NCard, Sub) :-
    cardinal_ms( MSet, Card), 
    min( Card, NCard, NCard1),
    decrement( NCard1 ,0, NN ),
    subset_size_x( MSet, Card, NN, Sub).

/*
subset_min_size_ms(
    + MSet : multiset<A>, + NCard : int, - Sub : multiset<A>
) is nondet.
    
Returns in NMSet all submultisets of MSet which cardinality is greater or 
equal to NCard.
*/
subset_min_size_ms( MSet, NCard, Sub) :-
    cardinal_ms( MSet, Card), 
    max( 0, NCard, NCard1),
    increment( NCard1, Card, NN),
    subset_size_x( MSet, Card, NN, Sub).

/*
subset_size_ms( 
    + MSet : multiset<A>, + NCard : integer, - Sub : multiset<A>
) is det.

This predicates generates in NMSet all multisets that are contained in MSet 
and which cardinal is NCard. 
Those subsets are generated following a 
*/
subset_size_ms( MSet, NCard, Sub) :-
    NCard >= 0,
    cardinal_ms( MSet, Card),
    Card >= NCard,
    subset_size_x( MSet, Card, NCard, Sub).

subset_size_x(_MSet, _Card, 0, []) :- !.
subset_size_x( MSet,  Card, Card, MSet) :- !.
subset_size_x( MSet,  Card, NCard, Sub) :-
    0 < NCard, 
    NCard < Card,
    !,
    MSet = [ (Elem,Mult) | MS1],
    C1 is Card-Mult,
    min(Mult,NCard,M1),
    MM2 is NCard -C1,
    max(MM2,0,M2), 
    % Calcular M2
    decrement(M1,M2,NMult),
    NC1 is NCard-NMult,
    NC1 =< C1,
    ( NMult = 0
    ->  Sub = Sub1
    ;   Sub = [ (Elem,NMult) |Sub1]
    ),
    subset_size_x(MS1,C1,NC1,Sub1).


/*
multiset_set_card_ms( 
    + Set : set<A>, + Card : int , - MSet: set<A> ) is nondet.

Returns in MSet, lexicographically ordered, 
the Multisets with cardinal Card and which elements are in Set. 

*/
multiset_set_card_ms( Set, Card, MSet) :- mssc_x( Set, Card, MSet).

mssc_x( [], 0, []).
mssc_x( [Elem|Set], C, MSet) :- 
    compare( Comp, 0, C), 
    mssc_xx( Comp, [Elem|Set], C, MSet). 

mssc_xx( '=', [_|_], 0, []).
mssc_xx( '<', [Elem|Set], C, MSet ) :- 
    mscc_xxx( Elem, C, NC, MSet_x, MSet ), 
    mssc_x( Set, NC, MSet_x ).
    
mscc_xxx( Elem, C, NC, MSet, [(Elem,Mult)|MSet] ) :-
    decrement(C,1,Mult), 
    NC is C - Mult. 
mscc_xxx( _Elem, C, C, MSet, MSet ).


/*
multiset_set_max_card_ms( 
    + Set : set<A>, + Max_Card : int , - MSet: set<A> ) is nondet.

Returns in MSet, lexicographically ordered, 
the Multisets with cardinal Card and which elements are in Set. 

*/
multiset_set_max_card_ms( Set, Card, MSet) :- 
    decrement( Card, 0, C), 
    mssc_x( Set, C, MSet).

/*
super_multiset_set_card_ms( 
    + MSet : multiset<A>, + Set: set<A>, + Card: int, - SMSet:multiset<A>) 
is nondet. 

SMSet is a multiset that is a superset of MSet 

SMSet = union ( MSet, NMSet) where NMSet es 

*/
super_multiset_set_card_ms( MSet, Set, NCard, SMSet) :- 
    cardinal_ms( MSet, Card), 
    NCard >= Card,
    Else_Card is NCard - Card, 
    multiset_set_card_ms( Set, Else_Card, Supplement_MSet), 
    sum_ms( MSet, Supplement_MSet, SMSet). 

super_multiset_set_max_card_ms( MSet, Set, NCard, SMSet) :- 
    cardinal_ms( MSet, Card), 
    NCard >= Card, 
    Else_Card is NCard - Card, 
    multiset_set_max_card_ms( Set, Else_Card, Supplement_MSet),
    sum_ms( MSet, Supplement_MSet, SMSet).

set_card_complement_ms( MSet, Set, NCard, Complement_Ms) :- 
    cardinal_ms( MSet, Card), 
    NCard >= Card, 
    Comp_Card is NCard - Card, 
    multiset_set_card_ms( Set, Comp_Card, Complement_Ms).

    
/*
filter_max_card_ms( MSets, Max_Card, Filt )
*/
filter_max_card_ms( [], _Max_Card, [] ).
filter_max_card_ms( [MSet|MSets], Max_Card, Filt ) :- 
    filter_max_card_x( MSet, Max_Card, Filt_x, Filt ), 
    filter_max_card_ms( MSets , Max_Card, Filt_x).

filter_max_card_x( MSet, Max_Card, Filt, [MSet|Filt] ) :- 
    cardinal_ms( MSet, Card), 
    Card =< Max_Card , 
    !. 
filter_max_card_x( _MSet, _Max_Card, Filt, Filt ).

/*
filter_card_ms( MSets, Card, Filt )
*/
filter_card_ms( [], _Card, [] ).
filter_card_ms( [MSet|MSets], Card, Filt ) :- 
    filter_card_x( MSet, Card, Filt_x, Filt ), 
    filter_card_ms( MSets , Card, Filt_x).

filter_card_x( MSet, Card, Filt, [MSet|Filt] ) :- 
    cardinal_ms( MSet, Card), 
    !. 
filter_card_x( _MSet, _Card, Filt, Filt ).

/*
filter_min_card_ms( MSets, Min_Card, Filt )
*/
filter_min_card_ms( [], _Min_Card, [] ).
filter_min_card_ms( [MSet|MSets], Min_Card, Filt ) :- 
    filter_min_card_x( MSet, Min_Card, Filt_x, Filt ), 
    filter_min_card_ms( MSets , Min_Card, Filt_x).

filter_min_card_x( MSet, Min_Card, Filt, [MSet|Filt] ) :- 
    cardinal_ms( MSet, Card),
    Card >= Min_Card,
    !.
filter_min_card_x( _MSet, _Min_Card, Filt, Filt ).
