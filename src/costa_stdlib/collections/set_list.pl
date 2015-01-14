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

:- module(set_list,[
    empty_sl/1,
    insert_sl/3,
    contains_sl/2,
    remove_sl/3,
    cardinal_sl/2,
    union_sl/3,
    substitute_sl/4,
    intersection_sl/3,
    difference_sl/3,
    unions_sl/2,
    intersections_sl/2,
    is_superset_sl/2,
    is_subset_sl/2,
    compare_inclusion_sl/3,
    disjoint_sl/2,
    product_sl/3,
    from_list_sl/2,
    element_sl/2,
    subset_poly_down_sl/2,subset_poly_up_sl/2,
    subset_cardinal_down_sl/2, subset_cardinal_down_max_cardinal_sl/3,
    subset_cardinal_up_sl/2, subset_cardinal_up_max_cardinal_sl/3,
    subset_cardinal_sl/3,
    filter_max_cardinal_sl/3,
    filter_cardinal_sl/3,
    filter_min_cardinal_sl/3
]).

/** <module> Set of elements over a sorted list without repetitions.

This module implements a Set of elements that uses as store a list without 
repetitions and sorted with the standard term order @<, @=<, ==, @>=, @>. 

type set<A> = list<A> where Set is sorted and has no repetitions. 

The Set invariant can be broken if one variable of one of its elements is bound
to another term.

@author Diego Alonso
@license GPL
*/

:- use_module(list_utils, [length_lu/2,sort_rdup/2, element_lu/2]).
:- use_module(stdlib(arithmetic_utils),[increment/3,decrement/3,min/3]).
:- use_module(pair_list,[cartesian_product/3]).

/*
empty_sl( - Set : set<A> ) is det.

Set is the empty set, that contains no element.
*/
empty_sl( [] ).

/*
insert_sl( + Set : set<A>, + Elem : A, - NSet : set<A> ) is det. 

NSet is the result of inserting Elem in Set. If Set already contains
Elem, then NSet = Set and the predicate succeeds.

Examples: 
 * insert_sl(    [], a, NSet) ?     NSet = [a]. 
 * insert_sl( [a,c], d, NSet) ?     NSet = [a,c,d].
 * insert_sl( [a,c], c, NSet) ?     NSet = [a,c].
 
*/
insert_sl( [], Elem, [Elem]).
insert_sl( [Y|Ys], Elem, NYs ) :- 
    compare( Comp, Y, Elem), 
    insert_x( Comp, [Y|Ys], Elem, NYs).
    
insert_x( < ,  [Y|Ys], Elem, [Y|Ns] ) :-  insert_sl( Ys, Elem, Ns ).
insert_x( = ,  Ys, _Elem, Ys ). 
insert_x( > ,  Ys, Elem, [Elem|Ys] ).

/*
contains_sl( + Set : set<A> , + Elem : A ) is semidet. 

True if Set contains Elem. 

@param Set  The set we ask about.
@param Elem The element we look in the set for. Caution: if Elem is a variable 
    then the predicate doesn't bind Elem to each element in Set, it tells if 
    Set contains that variable.

Examples: 
 * contains_sl( [], a) ?                false.
 * contains_sl( [a,b,c], a) ?           true.
 * contains_sl( [a,b,c], d) ?           false. 
*/
contains_sl( [Y|Ys], Elem) :- 
    compare( Comp, Y, Elem), 
    contains_x( Comp, Ys, Elem).

contains_x( < ,  Ys, Elem) :- contains_sl(Ys, Elem).
contains_x( = , _Ys, _Elem).

/*
remove_sl( + Set : set<A>, + Elem : A , - NSet : set<A>) is det.  

NSet is the result of removing Elem from Set. If Set doesn't contain Elem,
then the predicate succeeds and NSet = Set. 

Examples: 
 * remove_sl( [], a, NSet) ?          NSet = [].
 * remove_sl( [a],a, NSet) ?          NSet = [].
 * remove_sl( [a,b,c],b, NSet) ?      NSet = [a,c].
 * remove_sl( [a,b,c],d, NSet) ?      NSet = [a,b,c]. 
*/
remove_sl( [], _Elem, []). 
remove_sl( [Y|Ys], Elem, NYs) :-
    compare( Comp, Y, Elem), 
    remove_x( Comp, Y, Ys, Elem, NYs).

remove_x( '<', Y, Ys,  Elem, [Y|Ns]) :- remove_sl(Ys, Elem, Ns).
remove_x( '=', _Y, Ys, _Elem, Ys).
remove_x( '>', Y, Ys, _Elem, [Y|Ys]).

/*
cardinal_sl( + Set : set<A>, - Card : int) is det. 

Card is the cardinal of Set, which is the number of elements.

Examples: 
 * cardinal( [], 0).
 * cardinal( [a,b,c],3). 
*/
cardinal_sl( Set, Card) :- length_lu( Set, Card).

/*
from_list_sl( + List : list<A>, - Set : set<A> ) is det. 

Set is the set that contains all the elements in the List.

from_list_sl( List, Set) -> 
    forall term Term: contains_lu(List, Term) <--> contains_sl( Set, Term).
    
Examples:
 * from_list_sl( [], Set)           ?       Set = [].
 * from_list_sl( [c,b,c,a], Set)    ?       Set = [a,b,c].
*/
from_list_sl( List, Set) :- sort_rdup( List, Set).

/*
union_sl( + ASet : set<A>, + BSet : set<B>, - Union : set<A>) is det. 

Union is the Union of ASet and BSet, which means that 
Union contains a term Term if and only if either ASet or BSet contains Term. 

Properties: 
 * Associative:         union(A,B,N1),union(N1,C,N) <--> 
                        union(B,C,N2),union(A,N2,N)
 * Commutative:         union(A,B,N) <--> union(B,A,N).
 * Neutral element:     empty(E) -> union(A,E,A).
 * Superset:            union(A,B,N) -> subset(A,N).
 * Minimal superset:    union(A,B,N), subset(A,C), subset(B,C) -> subset(N,C).

*/
union_sl( [], SetB, SetB ). 
union_sl( [A|As], [], [A|As] ) :- !. 
union_sl( [A|As], [B|Bs], [Elem|Union] ) :-
    compare( Comp, A, B ),
    union_xel( Comp, A, B, Elem ), 
    union_xas( Comp, [A|As], As_x ), 
    union_xbs( Comp, [B|Bs], Bs_x ), 
    union_sl( As_x, Bs_x, Union ).

union_xel( < , A, _B, A ).
union_xel( = , A, _B, A ).
union_xel( > ,_A,  B, B ).

union_xas( < , [_|As], As ). 
union_xas( = , [_|As], As ).
union_xas( > , As, As ). 

union_xbs( < , Bs, Bs ). 
union_xbs( = , [_|Bs], Bs ).
union_xbs( > , [_|Bs], Bs ). 

/*
intersection_sl( + ASet : set<A>, + BSet : set<A>, - Inters : set<A>) is det. 

Inters is the intersection of ASet and BSet, which means that Inters contains 
a term Term if and only if both ASet and BSet contains Term. 

Properties: 
 * Commutativity:  intersection(A,B,N) <--> intersection(B,A,N).
 * Asociativity:   intersection(A,B,N1), intersection(N1,C,N) <-->
                   intersection(B,C,N2), intersection(A,N2,N)
 * Subset:         intersection(A,B,I) -> subset(I,A), subset(I,B)
 * Maximal subset: intersection(A,B,I), subset(C,A), subset(C,B) -> subset(C,I).
*/
intersection_sl( [], _BSet, [] ).
intersection_sl( [_|_], [], [] ) :- !.
intersection_sl( [A|As], [B|Bs], Inters ) :-
    compare( Comp, A, B), 
    intersection_x( Comp, A, As, B, Bs, As_x, Bs_x, Inters_x, Inters), 
    intersection_sl( As_x, Bs_x, Inters_x).
    
intersection_x( <, _A, As,  B, Bs, As, [B|Bs], Inters, Inters ).
intersection_x( =,  A, As, _B, Bs, As, Bs, Inters, [A|Inters] ).
intersection_x( >,  A, As, _B, Bs, [A|As], Bs, Inters, Inters ).

/*
difference_sl( + ASet : set<A> , + BSet : set<A>, - Diff : set<A> ) is det. 

Diff is the difference of SetA and SetB, which means that for every term Term, 
Diff contains Term if and only if ASet contains Term and BSet doesn't.

Examples: 
 * difference_sl( [a,b,c], [a,d], Diff )    ?       Diff = [b,c].

*/
difference_sl( [], _BSet, [] ) :- !.
difference_sl( ASet, [], ASet ) :- !.
difference_sl( [A|ASet], [B|BSet], Diff ) :-
    compare( Comp, A, B), 
    difference_x( Comp, A, ASet, B, BSet, As_x, Bs_x, Diff_x, Diff),
    difference_sl( As_x, Bs_x, Diff_x).

difference_x( < ,  A, ASet,  B, BSet, ASet, [B|BSet],  Diff, [A|Diff]).
difference_x( = , _A, ASet, _B, BSet, ASet, BSet,    Diff, Diff).
difference_x( > ,  A, ASet, _B, BSet, [A|ASet], BSet, Diff, Diff).

/*
unions_sl( + Sets : list<set<A>>, - Union : set<A>) is det. 
*/
unions_sl( Sets, Union) :- unions_x( Sets, [], Union). 
unions_x( [], Union, Union).
unions_x( [Set|Sets], Union0, Union) :- 
    union_sl( Set, Union0, Union1), 
    unions_x( Sets, Union1, Union).

/*
intersections_sl( + Sets : list<set<A>>, - Inters : set<A>) is det.
*/
intersections_sl( Sets, Inters ) :-
    intersections_x( Sets, [], Inters ).

intersections_x( [], Inters, Inters ).
intersections_x( [Set|Sets], Inters0, Inters ) :- 
    intersection_sl( Set, Inters0, Inters1),
    intersections_x( Sets, Inters1, Inters).

/*
product_sl( + ASet : set<A> , + BSet : set<B>, - Prod : set< (A,B) > ) is det.

Prod is the cartesian product of SetA and SetB, it's the set of pairs (A,B) 
such that for each terms A and B, 
contains_sl(Prod, (A,B) ) <--> contains_sl( SetA, A), contains_sl(SetB, B). 

Examples: 
 * product_sl( [], [], Prod) ?          Prod = [].
 * product_sl( [a,b], [1,2], Prod) ?    Prod = [ (a,1),(a,2),(b,1),(b,2)].

*/
product_sl( ASet, BSet, Prod) :- cartesian_product( ASet, BSet, Prod). 

/*
substitute_sl( + Set : set<A> , +ElemA : A, +ElemB : A, - NSet : set<A>) is det.

Substitutes ElemA by ElemB. NSet = Set [ ElemA -> ElemB ]

@param Set      The Set in which the substitution is performed. 
@param ElemA    The Value that is substituted in Set, if present.  
@param ElemB    The Value that substitutes ElemA in Set.  
@param NSet     The Set that results after performing the substitution. 
*/
substitute_sl(Set, ElemA, ElemB, NSet) :-
    open_cursor_sl( Set, ElemA, Cursor, Found), 
    Cursor = ( NSet, TailVar, Tail),
    substitute_x( Found, ElemB, TailVar, Tail).

substitute_x( true,   ElemB, Tail, [ElemB|Tail]). 
substitute_x( false, _ElemB, Tail , Tail ).

/*
is_subset_sl( + Sub : set<A>, + Super : set<A> ) is semidet. 

Decides if Sub is a subset of Super, which means that Super contains all the 
elements in Sub. 

Examples: 
 * superset([a,b,c],[a,b])  ?       true.
 * superset([a,b],[b,d])    ?       false.

@param Super    The set we ask to be a superset of Sub.
@param Sub      The set we ask to be a subset of Super. 

*/
is_subset_sl( [], _Super). 
is_subset_sl( [Sub_E|Sub], Super) :- 
    open_cursor_sl( Super, Sub_E, Cursor, true),
    Cursor = ( _Prefix, _TailVar, Super_Tail), 
    is_subset_sl( Sub, Super_Tail).

/*
is_superset_sl( + Super : set<A>, + Sub : set<A>) is semidet.
  
Decides if SetA is a superset  of SetB, that is to say if
all elements of SetB are also in SetA

Examples: 
 * superset([a,b,c],[a,b])  ?       true.
 * superset([a,b],[b,d])    ?       false.

@param Super    The set we ask to be a superset of Sub.
@param Sub      The set we ask to be a subset of Super. 
*/
is_superset_sl( Super, Sub) :- is_subset_sl( Sub, Super). 

/*
compare_inclusion_sl( 
    + As:set<A>, + Bs:set<A> , - Comp : { '<' , '=', '>', '|' }
) is det.

Compares the sets As and Bs and returns an atom 
< : As is a subset of Bs. 
> : As is a superset of Bs.
= : As and Bs are equal. 
'|': neither As contains Bs nor viceversa: they are "parallell".

*/
compare_inclusion_sl( [], [], = ) :- !.
compare_inclusion_sl( [], [_|_], < ) :- !.
compare_inclusion_sl( [_|_], [], > ) :- !.
compare_inclusion_sl( [A|As], [B|Bs], Comp) :- 
    compare( EComp, A, B), 
    compare_inclusion_x( EComp, [A|As], [B|Bs], Comp).

compare_inclusion_x( =, [_A|As], [_B|Bs], Comp) :- 
    compare_inclusion_sl( As, Bs, Comp).
compare_inclusion_x( <, [_A|As],  Bs, Comp) :- 
    % decide if answeer is '>' or '|' : 
    is_superset_sl( As, Bs ) 
    ->  Comp = '>'
    ;   Comp = '|'.
compare_inclusion_x( >, As, [_B|Bs], Comp) :- 
    % decide if answeer is '>' or '|' :
    is_superset_sl( Bs, As )
    ->  Comp = '<'
    ;   Comp = '|'.

/*
disjoint_sl( + ASet : set<A>, + BSet : set<A> ) is semidet. 

True if ASet and BSet are disjoint, if they have no common element. 
False if they have some element in common. 
*/
disjoint_sl( [], _BSet ).
disjoint_sl( [_|_], [] ) :- !.
disjoint_sl( [A|ASet], [B|BSet] ) :-
    compare( Comp, A, B),
    disjoint_x( Comp, A, ASet, B, BSet, ASet_x, BSet_x),
    disjoint_sl( ASet_x, BSet_x).

disjoint_x( <, _A, ASet, B, BSet, ASet, [B|BSet] ). 
disjoint_x( >, A, ASet, _B, BSet, [A|ASet], BSet ). 

/*
open_cursor_sl(
    + Set:set<A>, + Elem:A , 
    - Cursor: ( Prefix: open_set<A>, TailVar: var, Tail:set<A>), 
    - Found: bool
) is det.
*/
open_cursor_sl( Set, Elem, Cursor, Found) :-
    Cursor = ( Prefix, TailVar, Tail), 
    open_cursor_x( Set, Elem, Prefix, TailVar, Tail, Found).

open_cursor_x( [], _Elem, TailVar , TailVar, [], false).
open_cursor_x( [X|Set], Elem, Prefix, TailVar, Tail, Found) :- 
    compare( Comp, X, Elem), 
    open_cursor_xx( Comp, [X|Set], Elem, Prefix, TailVar, Tail, Found).

open_cursor_xx( < , [X|Set], Elem, [X|Prefix], TailVar, Tail, Found) :- 
    open_cursor_x( Set, Elem, Prefix, TailVar, Tail, Found).
open_cursor_xx( = , [_X|Set], _Elem, TailVar, TailVar, Set, true).
open_cursor_xx( >,  Set, _Elem, TailVar, TailVar, Set, false).

/*
close_cursor_sl( + MElem: maybe<A>, Cursor:cursor_sl<A>, -Set:set<A>).
                
*/
close_cursor_sl( []    , (Pre,       Tail , Tail), Pre).
close_cursor_sl( [Elem], (Pre, [Elem|Tail], Tail), Pre).

/*
element_sl( + Set : set<A> , - Elem: A) is nondet.

Bounds Elem to each element in Set, following a direct order. 
*/
element_sl( Set, Elem) :- element_lu( Set, Elem).

/*
filter_max_cardinal_sl( 
    + Sets : list<set<A>>  , + Max_Card: int , - Filt :  list<set<A>> )

Filt = filter ( \s -> cardinal s =< Max_Card ) Sets

*/ 
filter_max_cardinal_sl( [] , _Max_Card , [] ). 
filter_max_cardinal_sl( [Set|Sets], Max_Card, Filt ) :- 
    filter_max_cardinal_x( Set, Max_Card, Filt_x, Filt ), 
    filter_max_cardinal_sl( Sets, Max_Card, Filt_x ). 

filter_max_cardinal_x( Set, Max_Card, Filt, [Set|Filt] ) :- 
    cardinal_sl( Set, Card),
    Card =< Max_Card,
    !. 
filter_max_cardinal_x( _Set, _Max_Card, Filt, Filt ).

/*
filter_cardinal_sl( 
    + Sets : list<set<A>>  , + Card: int , - Filt :  list<set<A>> )

Filt = filter ( \s -> cardinal s == Card ) Sets

*/ 
filter_cardinal_sl( [] , _Card , [] ). 
filter_cardinal_sl( [Set|Sets], Card, Filt ) :- 
    filter_cardinal_x( Set, Card, Filt_x, Filt ), 
    filter_cardinal_sl( Sets, Card, Filt_x ). 

filter_cardinal_x( Set, Card, Filt, [Set|Filt] ) :- 
    cardinal_sl( Set, Card), 
    !. 
filter_cardinal_x( _Set, _Card, Filt, Filt ).

/*
filter_min_cardinal_sl( 
    + Sets : list<set<A>>  , + Max_Card: int , - Filt :  list<set<A>> )

Filt = filter ( \s -> cardinal s =< Max_Card ) Sets

*/ 
filter_min_cardinal_sl( [] , _Min_Card , [] ). 
filter_min_cardinal_sl( [Set|Sets], Min_Card, Filt ) :- 
    filter_min_cardinal_x( Set, Min_Card, Filt_x, Filt ), 
    filter_min_cardinal_sl( Sets, Min_Card, Filt_x ). 

filter_min_cardinal_x( Set, Min_Card, Filt, [Set|Filt] ) :- 
    cardinal_sl( Set, Card),
    Card =< Min_Card,
    !. 
filter_min_cardinal_x( _Set, _Min_Card, Filt, Filt ).



/*
subset_poly_down_sl( + Set : set<A>, - Sub : set<A> ) is nondet.

Sub is bound to every subset in Sub following a polynomial-down order: 
if Sub is bound to SubA before SubB then the polynomial interpretation 
of SubA is lesser to the one of SubB.

Polynomial Interpretation: for a given Set, you can code each subset Sub of Set
as a binary array in which the nth digit says if Sub contains the nth element
of Set. That binary array can then be read as a number in a base-2.

Examples: 
 * subset_poly_down_sl( [], Sub)         ?   Sub = []. 
 * subset_poly_down_sl( [a], Sub)        ?   Sub = [a]   ;   Sub = [].  
 * subset_poly_down_sl( [a,b,c], Sub)    ?  
        Sub = [a,b,c]   ;   Sub = [a,b] ;   Sub = [a,c] ;   Sub = [a]   ;
        Sub = [b,c]     ;   Sub = [b]   ;   Sub = [c]   ;   Sub = []    . 

*/
subset_poly_down_sl( [], []).
subset_poly_down_sl( [Elem|Set], Sub) :-
    subset_poly_down_x( Elem, Sub0, Sub),
    subset_poly_down_sl(Set, Sub0).

subset_poly_down_x(  Elem, Sub, [Elem|Sub] ).
subset_poly_down_x( _Elem, Sub, Sub).

/*
subset_poly_up_sl( + Set : set<A>, - Subset : set<A> ) is nondet.

Sub is bound to every subset in Sub following a polynomial-up order: 
if Sub is bound to SubA before SubB then the polynomial interpretation 
of SubA is lesser to the one of SubB.

Examples: 
 * subset_poly_up_sl( [], Sub)         ?   Sub = []. 
 * subset_poly_up_sl( [a], Sub)        ?   Sub = []   ;   Sub = [a].  
 * subset_poly_up_sl( [a,b,c], Sub)    ?  
        Sub = []    ;   Sub = [c]   ;   Sub = [b]   ;   Sub = [b,c]     ;
        Sub = [a]   ;   Sub = [a,c] ;   Sub = [a,b] ;   Sub = [a,b,c]   . 

*/
subset_poly_up_sl( [], [] ).
subset_poly_up_sl( [Elem|Set], Sub ) :-
    subset_poly_up_x( Elem, Sub0, Sub), 
    subset_poly_up_sl(Set, Sub0).

subset_poly_up_x( _Elem, Sub, Sub).
subset_poly_up_x(  Elem, Sub, [Elem|Sub]).

/*
subset_cardinal_up_sl( + Set : set<A>, - Sub : set<A> ) is nondet.

Sub is bound to every subset in Sub following a cardinal-up, polynomial-down
order: if Sub is bound to SubA before SubB then the cardinal of SubA is lesser 
or equal than the cardinal of SubB, or they have the same cardinal and the 
polynomial interpretation of SubA is lesser to the one of SubB.

Examples: 
 * subset_cardinal_up_sl( [], Sub)         ?   Sub = []. 
 * subset_cardinal_up_sl( [a], Sub)        ?   Sub = []   ;   Sub = [a].  
 * subset_cardinal_up_sl( [a,b,c], Sub) ? 
    Sub = []    ;   Sub = [a]   ;   Sub = [b]   ;   Sub = [c]  ; 
    Sub = [a,b] ;   Sub = [a,c] ;   Sub = [b,c] ;   Sub = [a,b,c].

*/
subset_cardinal_up_sl( Set, Sub) :-
    cardinal_sl(Set, Card),
    increment(0,Card, N),
    subset_cardinal_sl(Set, N, Sub).

subset_cardinal_up_max_cardinal_sl( Set, Max_Card, Sub ) :- 
    cardinal_sl( Set, Card), 
    min( Max_Card, Card, NCard), 
    increment(0,NCard, N),
    subset_cardinal_sl( Set, N, Sub).

/*
subset_cardinal_down_sl( + Set : set<A>, - Subset : set<A> ) is nondet.

Sub is bound to every subset in Sub following a cardinal-down, polynomial-down
order: if Sub is bound to SubA before SubB then the cardinal of SubA is lesser 
or equal than the cardinal of SubB, or they have the same cardinal and the 
polynomial interpretation of SubA is lesser to the one of SubB.

Examples: 
 * subset_cardinal_down_sl( [], Sub)         ?   Sub = []. 
 * subset_cardinal_down_sl( [a], Sub)        ?   Sub = [a]   ;   Sub = [].  
 * subset_cardinal_down_sl( [a,b,c], Sub) ? 
    Sub = [a,b,c]   ; Sub = [a,b]   ;   Sub = [a,c] ;   Sub = [b,c] ; 
    Sub = [a]       ; Sub = [b]     ;   Sub = [c]   ;   Sub = [].

*/
subset_cardinal_down_sl(Set, Sub) :-
    cardinal_sl(Set, Card),
    decrement(Card, 0, N), 
    subset_cardinal_sl(Set, N, Sub).

subset_cardinal_down_max_cardinal_sl( Set, Max_Card, Sub ) :- 
    cardinal_sl( Set, Card), 
    min( Max_Card, Card, NCard), 
    decrement( NCard, 0, N ),
    subset_cardinal_sl( Set, N, Sub).

/*
subset_cardinal_sl( +Set : set<A>, + Size : int, - Subset : set<A>) is nondet.

Subset is bound to every subset of Set of a certain Size. Subsets of the same
size are bound to Subset in a polynomial-down order.

Precondition: 0 =< Size =< Card     where cardinal_sl( Set, Card).

Examples: 
 * subset_cardinal_sl( [], 0, Subset)       ?   Subset = [].
 * subset_cardinal_sl( [], 1, Subset)       ?   false.
 * subset_cardinal_sl( [a,b], 0, Subset)    ?   Subset = [].
 * subset_cardinal_sl( [a,b], 1, Subset)    ?   Subset = [a] ; Subset = [b].
 * subset_cardinal_sl( [a,b], 2, Subset)    ?   Subset = [a,b].
 * subset_cardinal_sl( [a,b,c], 2, Subset)  ?   
        Subset = [a,b]  ;   Subset = [a,c]  ; Subset = [b,c]. 

*/
subset_cardinal_sl(Set, Size, Subset) :-
    cardinal_sl(Set, Card),
    subset_cardinal_1(Set, Card, Size, Subset).

subset_cardinal_1( Set, Card, Size, Sub) :- 
    compare( ZComp, 0, Size), 
    subset_cardinal_2( ZComp, Set, Card, Size, Sub). 

subset_cardinal_2( =, _Set, _Size, _Card, [] ). 
subset_cardinal_2( <, Set, Card, Size, Sub) :- 
    compare( CComp, Size, Card), 
    subset_cardinal_3( CComp, Set, Card, Size, Sub).

subset_cardinal_3( = , Set, Card, Card, Set).
subset_cardinal_3( <, [X|Set], Card, Size, Sub) :- 
    Card_x is Card -1,
    (   Size_x is Size - 1 , Sub = [X|Sub_x]
    ;   Size_x = Size      , Sub = Sub_x 
    ),
    subset_cardinal_1( Set, Card_x, Size_x, Sub_x).
