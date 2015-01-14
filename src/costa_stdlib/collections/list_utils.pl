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

:- module(list_utils,[
    null_lu/1, length_lu/2, contains_lu/2, count_lu/3,
    element_lu/2, element_rev_lu/2,
    last_lu/2,init_lu/2, 
    insert_lu/4, insert_end_lu/3,
    get_lu/3, get_many_lu/3,
    set_lu/4, set_many_lu/4,
    get_replace_lu/5, get_replace_many_lu/5,
    quit_lu/3, quit_many_lu/3,
    take_lu/3,drop_lu/3,split_at_lu/4,slice_lu/4,divide_in_chunks_lu/3,
    append_lu/3, concat_lu/2,
    replicate_lu/3,
    sort_lu/2,
    nub_lu/2,
    remove_lu/3,remove_many_lu/3,
    sort_rdup/2,
    delete_lu/3,
    difference_lu/3,
    reverse_lu/2,
    partition_lu/3,
    disjoint_lu/2
]).

/** <module> Predicates that handle lists of any kind of elements. 

type list<A> ::=    []  |   [ A | list<A> ]

@author Diego Alonso
@license GPL
*/

/*
null_lu( + List : list<A> ) is semidet.
null_lu( - List : list<A> ) is det.

*/
null_lu( [] ).

/*
length_lu( +List:list<A> , ?Length:int) is det.

Length is the length of List. 

Examples: 
 * length_lu( [], L)        ?   L = 0.
 * length_lu( [a,b,c],3)    ?   L = 3.
*/
length_lu( List , Length ) :- length_x( List , 0 , Length ). 

length_x( [] , Length , Length ).
length_x( [_Elem|List] , Acc , Length ) :- 
    NAcc is Acc + 1 ,
    length_x( List , NAcc , Length ).

/*
contains_lu( + List : list<A>, + Elem : A) is semidet.  

True if one of the elements of the List is syntactically equal to Elem.

Examples: 
 * contains_lu( [] , a )        ?   false.
 * contains_lu( [a,b,c] , a)    ?   true.
 * contains_lu( [a,b,c] , d)    ?   false.
 * contains_lu( [A,B,C] , A)    ?   true.
 * contains_lu( [A,B,C] , D)    ?   false <--  D not unified with A,B or C.
*/
contains_lu( [ X | Xs] , Elem) :- Elem == X, ! ; contains_lu( Xs, Elem).

/*
elem_index_lu( + List : list<A>, + Elem : A, - Index : int ) is nondet.

*/
elem_index_lu( List, Elem, Index ) :- 
    elem_index_x( List, Elem, 1, Index ). 

elem_index_x( [X|_Xs], Elem, Index, Index ) :- X == Elem.
elem_index_x( [_X|Xs], Elem, Index, NIndex ) :- 
    Index_1 is Index + 1, 
    elem_index_x( Xs, Elem, Index_1, NIndex). 

/*
elem_indices_lu( + List : list<A> , + Elem: A , - Indices: list<int> ) is det.

*/
elem_indices_lu( List, Elem, Indices ) :- 
    elem_indices_x( List, Elem, 1, Indices ). 

elem_indices_x( [], _Elem, _Index, [] ).
elem_indices_x( [Head|List], Elem, Index, Indices )  :- 
    elem_indices_xx( Head, Elem, Index, Indices_x, Indices), 
    Index_1 is Index + 1, 
    elem_indices_x( List, Elem, Index_1, Indices_x). 

elem_indices_xx( Head, Elem, Index, Indices, [Index|Indices]) :- 
    Head == Elem, 
    !.
elem_indices_xx( _Head, _Elem, _Index, Indices, Indices).

/*
element_lu( +List:list<A> , -Elem:A ) is nondet.

Returns in Elem all the elements of List, following the order in the list. 

Examples: 
 * element_lu ( [], X)          ?   false.
 * element_lu ( [a,b,c], X)     ?   X = a ; X = b ; X = c. 
*/
element_lu( [ Elem|_List], Elem ). 
element_lu( [_Head| List], Elem ) :- element_lu( List, Elem ).

/*
element_rev_lu( +List:list<A> , -Elem:A ) is nondet.

Gives the elements of List, in the order contrary to the order in the list.

Examples: 
 * element_rev_lu ( [], X)      ?   false.
 * element_rev_lu ( [a,b,c], X) ?   X = c ; X = b ; X = a.
*/
element_rev_lu( [_Head| List], Elem ) :- element_rev_lu( List , Elem ).
element_rev_lu( [ Elem|_List], Elem ).

/*
count_lu( + List: list<A>, + Elem:A , - Count: integer) is det. 

Count is the number of elements E in List such that Elem == E. 

Examples: 
 * count_lu( [], a, C )         ?   C = 0.
 * count_lu( [a,b,a], a, C )    ?   C = 2.
 * count_lu( [a,b,a], b, C )    ?   C = 1.
 * count_lu( [a,b,a], d, C )    ?   C = 0.
 * count_lu( [A,B,A], A, C )    ?   C = 2. % B is not unified with A.
 * count_lu( [A,B,C], D, C )    ?   C = 0. % D is not unified with A,B,C.
*/
count_lu( List, Elem, Num) :- count_x( List, Elem, 0, Num).

count_x( [], _Elem, Num, Num).
count_x( [Head|List], Elem, Num0, Num ) :-
    count_xx( Head, Elem, Num0, Num1 ),
    count_x(  List, Elem, Num1, Num  ).

count_xx( E, Elem, Num0, Num1) :-
    E == Elem
    ->  Num1 is Num0 + 1
    ;   Num1 = Num0.

/*
last_lu( +List:list<A>, -Last:A) is semidet. 

Last is the last element in the List. Fails if List is empty.

Examples:
 * last_lu( [], L)      ?   false.
 * last_lu([a,b],L).    ?   L = b.
*/
last_lu( [Head|List], Last) :- last_x( List, Head, Last ).

last_x( [], Last, Last).
last_x( [Head|List], _Y, Last) :- last_x( List, Head, Last ).

/*
init_lu( + List:list<A>, - Init:list<A>) is semidet.

Init is the list with all the elements of A except the last one.
Fails if List is empty.

Examples: 
 * init_lu( [], X)      ?   false.
 * init_lu( [a,b], X)   ?   X = [b]. 
*/
init_lu( [Head|Tail], Init) :- init_x( Tail, Head, Init).

init_x( [], _X, []).
init_x( [Y|Ys], X, [X|Zs]) :- init_x( Ys, Y, Zs).

/*
insert_end_lu( + List:list<A>, + Elem:A, - NList:list<A> ) is det.
*/
insert_end_lu( [], Elem, [Elem] ). 
insert_end_lu( [Head|List], Elem, [Head|NList] ) :- 
    insert_end_lu( List, Elem, NList). 

/*
get_lu( + List : list<A> , + Index : int , - Elem : A ) is det. 

Elem is the Index-th Element of List, where the elements are numbered starting 
with one: the head of a nonempty list is  the 1st element, 
not zero-th as used in the C family (C,C++, Objective-C, Java, ...).
The reason for using this nummeration is coherence with Prolog's arg() function.

The predicate fails (false) if Index =< 0 or length_lu(List,L), Index > L.

*/
get_lu( List, Index, Elem) :- get_x( List, 1, Index, Elem ).

get_x( [Elem|_List], Act, Index, Elem) :- Act = Index, !.
get_x( [_Head|List], Act, Index, Elem) :-
    Act < Index,
    NAct is Act + 1,
    get_x( List, NAct, Index, Elem ).

/*
get_many_lu( + List:list<A>, + Indices:list<int>, - Elems:list<A> ) is det.

Preconditions: Indices is sorted and for every element Ind in Indices, 
1 =< Ind =< L where length_lu(List, L). 

Postconditions: Elems is a list such that length(Elems)=length(Indices) and 
forall i : Elems[i] = List[ Indices[i] ].

*/
get_many_lu( List, Indices, Elems) :- 
    get_many_x( Indices, 1, List, Elems).

get_many_x( [], _Act, _List, []). 
get_many_x( [Ix|Ices], Act, [Head|List], Elems ) :-
    compare( Comp, Act, Ix), 
    get_many_xx( Comp, [Ix|Ices], NIces, Head, Elems_x, Elems), 
    NAct is Act + 1, 
    get_many_x( NIces, NAct, List, Elems_x).

get_many_xx( '<', Ices, Ices, _Head, Elems, Elems).
get_many_xx( '=', [_Ix|Ices], Ices, Head, Elems, [Head|Elems]).

/*
set_lu( 
    + List : list<A>, + Index : int, + NElem : A, - NList : list<A> 
) is semidet.

Replaces the element at the Index-th position, OElem, with NElem.
Index must be in the range 1..L where L is the length of the List. 

*/
set_lu( [_Head|List], 1, NElem, [NElem|List] ) :- !.
set_lu( [Head|List], N, NElem, [Head|NList] ) :- 
    N > 1,
    NN is N-1,
    set_lu( List, NN, NElem, NList).

/*
set_many_lu( 
    + List:list<A>, + Indices:list<int>, + Elems:list<A>, - NList: list<A>
) is det.

Precondition: 
 * Indices is a sorted list of indices for List. 
 * forall Ix in Indices: 1 =< Ix =< length(List).
 * length(Indices) = length(Elems).
Postcondition: 
 * length(NList) = length( List). 
 
Example: 
 * set_many_lu( [a,b,c,d,e,f,g,h], [2,4,7], [x,y,z], NL) ? 
        NL = [a, x, c, y, e, f, z, h].
 
*/
set_many_lu( List, Indices, Elems, NList ) :-
    set_many_x( Indices, Elems, 1, List, NList).

set_many_x( [], [], _OIndex, List, List).
set_many_x( [Ix|Ices], [Elem|Elems], Act, [Head|List], [NHead|NList] ) :-
    compare( Comp, Act, Ix), 
    set_many_xx( Comp, [Ix|Ices], NIces, [Elem|Elems], NElems, Head, NHead),
    NAct is Act + 1,
    set_many_x( NIces, NElems, NAct, List,  NList).

set_many_xx( '<', Ices, Ices, [Elem|Elems], [Elem|Elems], Head, Head).
set_many_xx( '=', [_Ix|Ices], Ices, [Elem|Elems], Elems, _Head, Elem).


/*
get_replace_lu( 
    + List: list<A>, + Num:integer, + NElem:A, -OElem:A, -NList:list<A> 
).
    
*/
get_replace_lu( [Elem|List], 1, NElem,  Elem, [NElem|List]) :- !. 
get_replace_lu( [Elem|List], N, NElem, OElem, [Elem|NList]) :- 
    N > 1,
    NN is N-1,
    get_replace_lu( List, NN, NElem, OElem, NList).

/*
get_replace_many_lu( 
    + List:list<A>, + Indices:list<int>, + NElems:list<A>, 
    - OElems:list<A>,  - NList:list<A> ) is det. 
    
Preconditions: 
 * Indices is a sorted list of numbers between 1 and length(List).
 * Indices and NElems have the same length. 

Postconditions: 
 * OElems has the same length as Indices.

    
*/
get_replace_many_lu( List, Indices, NElems, OElems, NList) :- 
    get_replace_many_x( Indices, NElems, OElems, 1, List, NList). 

get_replace_many_x( [], [], [], _Act, List,  List).
get_replace_many_x( [Ix|Ices], NElems, OElems, Act, [OHead|OList], [NHead|NList] ) :- 
    compare( Comp, Act, Ix),
    get_replace_many_2( Comp, NElems, OElems, OHead, NHead),
    get_replace_many_4( Comp, NElems, NElems_x, OElems, OElems_x),
    get_replace_many_3( Comp, [Ix|Ices],NIces),
    NAct is Act + 1,
    get_replace_many_x( NIces, NElems_x, OElems_x, NAct, OList, NList).

get_replace_many_2( <, _, _, Head, Head ).
get_replace_many_2( =, [NElem|_], [OHead|_OElems], OHead, NElem ).

get_replace_many_4( <, NElems, NElems, OElems, OElems ).
get_replace_many_4( =, [_|NElems], NElems, [_|OElems], OElems ).

get_replace_many_3( <, Ices, Ices).
get_replace_many_3( =, [_|Ices], Ices).

/*
insert_lu( + List: list<A>, + Num: integer, + Elem: A, - NList:list<A>) is det.

Preconditions: 1 =< Num =< length(List) + 1 

Postcondition: length(NList) = length(List) + 1,  
    forall i : 1 =< i < Num: List[i] == NList[i] 
    NList[Num] = Elem
    forall i : Num < i < length(NList) : NList[i] = List[i-1]

*/
insert_lu( List, Num, Elem, NList) :- insert_x( Num, List, Elem, NList). 

insert_x( 1, List, Elem, [Elem |List]) :- !. 
insert_x( Num, [Elem|List], NElem, [Elem|NList] ) :- 
    Num > 1, 
    NNum is Num-1, 
    insert_x( NNum, List, NElem, NList ). 

/*
quit_lu( + List : list<A> , + Num, - NList : list<A>  ) is det.

*/
quit_lu( List, Num, NList) :- quit_x( Num, List, NList). 

quit_x( 1, [_Elem|List], List) :- !.
quit_x( Num, [Elem|List], [Elem|NList]) :- 
    Num > 1, 
    NNum is Num-1, 
    quit_x( NNum, List, NList ).

/*

*/
quit_many_lu( List, Nums, NList) :- quit_many_x( Nums, 1, List, NList). 

quit_many_x( [], _Ix, List, List ).
quit_many_x( [Num|Nums], Ix, [Head|List], NList) :- 
    (   Num = Ix,   !, NNums = Nums,       NList = NList_x
    ;   Num > Ix,   !, NNums = [Num|Nums], NList = [Head|NList_x]
    ),
    NIx is Ix + 1,
    quit_many_x( NNums, NIx, List, NList_x ).

/*
append_lu( + Pres : list<A> , + Posts : list<A> , - List : list<A> ) is det. 

List is the result of appending Post after Pre.  

Examples: 
 * append_lu ( [] , [], App)        ?   App = []. 
 * append_lu ( [a,b] , [], App)     ?   App = [a,b].
 * append_lu ( [] , [c,d], App)     ?   App = [c,d].
 * append_lu ( [a,b] , [c,d], App)  ?   App = [a,b,c,d].
*/
append_lu( [], Posts, Posts ).
append_lu( [Pre|Pres], Post, [Pre|List] ) :- append_lu( Pres, Post , List).

/*
concat( + Lists : list<list<A>>, - Conc : list<A> ) is det. 

Conc is the result of concatenating all the Lists.

Examples: 
 * concat( [ ] , Conc )             ?   Conc = [].
 * concat( [ [],[],[] ] , Conc )    ?   Conc = [].
 * concat( [ [1,2],[],[3,4]], Conc) ?   Conc = [1,2,3,4].
*/
concat_lu( [], [] ).
concat_lu( [A|As] , Bs ) :- concat_x( A , As , Bs ).

concat_x( [],       As,     Bs  ) :- concat_lu(As,Bs).
concat_x( [X|Xs],   As, [X|Bs] ) :- concat_x(Xs,As,Bs).

/*
replicate_lu( + Elem:A , + Num : int, - List : list<A>) is det.

List is the list with N repetitions of A

Precondition: Num >= 0 
*/
replicate_lu( 0, _Elem, [] ) :- !.
replicate_lu( Num,  Elem, [Elem|Elems] ) :- 
    Num >= 1,
    NNum is Num-1, 
    replicate_lu( NNum, Elem, Elems ).

/*
merge_sorted_lu( 
    + AList : list<A> , + BList : list<A>  , - Merge : list<A> 
) is det. 

Pre: AList and BList must be sorted lists, that may have repetitions. 
Post : Merge is a sorted list that contains all the elements in AList and BList,
with all the repetitions from AList plus the repetitions from BList. 

Examples: 
 *  Q: merge_sorted_lu( [a,b,b,c,e], [c,d,f] , M ) ?    
    A: M = [a,b,b,c,c,d,e,f] 

*/
merge_sorted_lu( [], Ys, Ys ) :- !.
merge_sorted_lu( Xs, [], Xs ) :- !. 
merge_sorted_lu( [X|Xs] , [Y|Ys] ,Zs ) :- 
    compare( Comp, X, Y), 
    merge_1( Comp,  [X|Xs] , [Y|Ys], Xs_x, Ys_x ), 
    merge_2( Comp, X, Y, Zs_x, Zs ),  
    merge_sorted_lu( Xs_x, Ys_x, Zs_x ). 

merge_1( <,  [_|Xs] , Ys, Xs, Ys). 
merge_1( =,  [_|Xs] , [_|Ys], Xs, Ys). 
merge_1( >,  Xs , [_|Ys], Xs, Ys). 

merge_2( <, X, _Y, Zs, [X|Zs] ).
merge_2( =, X, Y, Zs, [X,Y|Zs] ).
merge_2( >,_X, Y, Zs, [Y|Zs] ).

/*
sort_lu( + Unsorted: list<A>, - Sorted: list<A> ) is det.

Sorted is a list that contains all the elements in Unsorted, with repetitions, 
but sorting them according to the term order. 

*/
sort_lu( [] , []  ). 
sort_lu( [A], [A] ) :- !. 
sort_lu( [A,B], [A,B] ) :- A @=< B, !.
sort_lu( [B,A], [A,B] ) :- B @> A, !.
sort_lu( As, Bs  ) :- 
    % implicit: length(Xs) >= 2
    ms_div( As, As1, As2 ), 
    sort_lu( As1, Bs1 ),
    sort_lu( As2, Bs2 ), 
    merge_sorted_lu( Bs1, Bs2, Bs ).

ms_div( [], [] , [] ).
ms_div( [A|As], [A|Bs], Cs ) :- ms_div( As, Cs, Bs ).


/*
*/
sort_rdup(Xs,Ys) :- sort(Xs,Ys).

/*
delete_lu ( + List : list<A>, + Elem : A , - NList : list<A>) is det. 

NList is the result of deleting from List ALL the appearances of Elem, 
when an appearance is determined with sintactic equality. 
*/
delete_lu( [], _Elem, [] ).
delete_lu( [X|Xs], Elem, NList ) :-
    delete_x( X, Elem, List1, NList ),
    delete_lu( Xs, Elem, List1 ).

delete_x( X, Elem, List,    List  ) :- 
    X == Elem, 
    !.
delete_x( X, _Elem, List, [X|List] ).

/*
difference_lu( + AList : list<A>, + BList : list<A>, - Diff : list<A> ) is det.

Diff is the list that contains all the elements of AList that are not contained
in BList, appearing in the same order and number than in the AList.

*/
difference_lu( AList, [], AList ) :- !.
difference_lu( [], _BList, [] ).
difference_lu( [AElem|AList], BList, NList ) :- 
    difference_x( AElem, BList, NList_x, NList), 
    difference_lu( AList, BList, NList_x ).

difference_x( AElem, BList, NList, NList ) :- 
    contains_lu( BList, AElem ), 
    !.
difference_x( AElem, _BList, NList, [AElem|NList] ).

/*
reverse_lu( + List : list<A>, - Rev : list<A>) is det. 

Rev is the reverse of the List. 

Examples: 
 * reverse_lu( [], X) ?        X = [].
 * reverse_lu( [a,b], X) ?     X = [b,a].
 
*/
reverse_lu(Xs,Ys):- reverse_x(Xs,[],Ys).

reverse_x([], L, L).
reverse_x([X|Xs],L,R) :- reverse_x(Xs,[X|L],R).

/*
take_lu( + Num : int, + List : list<A> , - Prefix : list<A>) is det. 

If Num =< length(List) then Prefix is the list that contains the first Num
elements of List.
If Num > length(List), then Prefix = List. 

@param Num is the number of elements we want to take. Precondition: Num >= 0.
*/
take_lu( Num, List, Prefix ) :- take_x( List, Num, Prefix ). 

take_x( [], _Num, [] ).
take_x( [Elem|List], Num, Pref ) :- 
    compare( Comp, 0, Num ), 
    take_xx( Comp, [Elem|List], Num, Pref ). 

take_xx( < , [Elem|List], Num, [Elem|Pref] ) :- 
    N1 is Num - 1,
    take_x( List, N1, Pref ).
take_xx( = , _ , 0 , [] ). 

/*
drop_lu( + Num : int, + List : list<A> , -Post : list<A>) is det. 

Postfix is is the list that contains all except the first Num elements 
of List.

*/
drop_lu( Num, List, Post) :- drop_x( List, Num, Post).

drop_x( [], _Num, [] ).
drop_x( [Elem|List], 0, [Elem|List] ) :- !.
drop_x( [_Elem|List], Num,Postfix) :-
    Num > 0,
    N1 is Num-1,
    drop_x(List, N1,Postfix).

/*
split_at_lu( +Num:int , +List:list<A> , -Pre:list<A>, -Post:list<A>) is det.

Precondition: Num >= 0

split_at_lu( N,L,Pre,Post) <--> take_lu(N,L,Pre), drop_lu(N,L,Post). 
*/
split_at_lu( Num, List, Pre, Post ) :- split_at_x( List, Num, Pre, Post ). 

split_at_x( [], _Num, [], [] ).
split_at_x( [Elem|List], Num, Pre, Post ) :- 
    compare( Comp, 0, Num) , 
    split_xx( Comp, [Elem|List], Num, Pre, Post). 

split_xx( <, [Elem|List], Num, Pre, Post) :- 
    Pre = [Elem|Pre_x],
    Num1 is Num - 1,
    split_at_x( List, Num1, Pre_x, Post ).
split_xx( = , Post, 0, [], Post ). 

/*
divide_in_chunks_lu( 
    + Size:integer, + List: list<A>, - Chunks: list<list<A>>
) is det. 

Divides the list List in a series of chunks, with the property that 
 * concat(Chunks, List), 
 * Size * (C-1) < L =< Size * C
 * forall i:0 =<i < C : length(Chunks(i)) = Size
  
Precondition: Size >= 1. 
*/
divide_in_chunks_lu( Size, List, Chunks) :- 
    chunks_x( List, Size, Chunks). 

chunks_x( [] , _Size, [] ). 
chunks_x( [Elem|List], Size, [Pred|Chunks]) :- 
    split_at_lu( Size, [Elem|List], Pred, Tail), 
    chunks_x( Tail, Size, Chunks). 
    
/*
slice_lu( + List:list<A> , + Start:int, + End:int, - Slice : list<A>) is det. 

slice_lu is the list that contains all the elements of List from Start to End.
Preconditions:  Start >= End >= 0

Postconditions: length( Slice) == End - Start = Length
    forall i: 0 =< i < Length : Slice[i] = As[i+Start]

Example: slice_lu( [a,b,c,d,e,f] , 2 , 4 , [ c,d ].
*/
slice_lu( As , Start , End , Slice ) :- 
    % preconditions
    integer(Start), 
    integer(End), 
    End >= Start,
    Start >= 0,
    % code,
    drop_lu(Start, As, Xs),
    Length is End - Start,
    take_lu(Length, Xs, Slice).

/*
nub_lu( + List: list<A> , - NList: list<A>) is det.

NList is the result of removing from List the repeated occurrences of elements,
keeping only the first one. 
*/
:- use_module(tree_234,[empty_tree/1,insert_tree/4,search_tree/3]).

nub_lu( List, NList) :- 
    empty_tree(T), 
    nub_x( List, T, NList).

nub_x( [], _Tree, []).
nub_x( [Elem|List], Tree, NList) :- 
    nub_xx( Elem, Tree, NList_x, NList, NTree), 
    nub_x( List, NTree, NList_x). 

nub_xx( Elem, Tree, NList, NList, Tree) :- 
    search_tree( Tree, Elem, _), 
    !. 
nub_xx( Elem, Tree, NList, [Elem|NList], NTree) :- 
    insert_tree( Tree, Elem, true, NTree). 

/*
remove_lu( +As:list<A> , ?Elem:A , -Rest:list<A>) is det. 

Rest is the result of removing the first appearance of Elem in Rest.

*/
remove_lu([],_,[]).
remove_lu([Elem|List],RElem,List) :- Elem == RElem, !.
remove_lu([Elem|List],RElem,[Elem|List0]) :- 
    remove_lu(List, RElem, List0).




/*
remove_many_lu( + List:list<A>, + Indices:list<int>, - Elems:list<A> ) is det.

Preconditions: Indices is sorted and for every element Ind in Indices, 
1 =< Ind =< L where length_lu(List, L). 

Postconditions: Elems is a list such that length(Elems)=length(List) - length(Indices) and
  Elems contains the Elements of the list not removed 

*/
remove_many_lu( List, Indices, Elems) :- 
    remove_many_x( Indices, 1, List, Elems).

remove_many_x( [], _Act, List, List). 
remove_many_x( [Ix|Ices], Act, [Head|List], Elems ) :-
    compare( Comp, Act, Ix), 
    remove_many_xx( Comp, [Ix|Ices], NIces, Head, Elems_x, Elems), 
    NAct is Act + 1, 
    remove_many_x( NIces, NAct, List, Elems_x).

remove_many_xx( '<', Ices, Ices, Head, Elems, [Head|Elems]).
remove_many_xx( '=', [_Ix|Ices], Ices, _Head, Elems, Elems).



/*
partition_lu( +List:list<A>, +Num:integer, -Subs:list<list<A>> ) is multidet.

Gives a method for dividing List in Num sublists, in which the elements appear
in the same order as in the original list. 

Precondition: Num >= 0
*/
partition_lu( List, Num, Subs) :-
    replicate_lu( Num, [], Subs0),
    partition_x( List, Subs0, Subs). 

partition_x( [], Subs, Subs).
partition_x( [Elem|Elems], Subs0, Subs) :-
    partition_x( Elems, Subs0, Subs1),
    partition_xx( Subs1, Elem, Subs).
    
partition_xx( [Sub|Subs], Elem, [ [Elem|Sub] |Subs]).
partition_xx( [Sub|Subs], Elem, [Sub|NSubs]) :-
    partition_xx( Subs, Elem, NSubs).

/*
disjoint_lu( As, Bs) is semidet. 

True if As and Bs have no common element. 

Examples: 
 * disjoint_lu( [], [])     ?      yes.
 * disjoint_lu( [a], [])    ?      yes.
 * disjoint_lu( [], [b])     ?      yes.
 * disjoint_lu( [a], [a])    ?      no.
 * disjoint_lu( [A], [A])    ?      no.
 * disjoint_lu( [A], [B])    ?      yes. <-- A and B are not unified. 

*/
disjoint_lu( [], _Bs ). 
disjoint_lu( [_|_], [] ) :- !. 
disjoint_lu( [A|As], [B|Bs]  ) :-
    sort_lu( [A|As], As_x), 
    sort_lu( [B|Bs], Bs_x), 
    disjoint_x( As_x, Bs_x).

disjoint_x( [], _Bs ).
disjoint_x( [_|_], [] ) :- !.
disjoint_x( [A|As], [B|Bs]  ) :- 
    compare( Comp, A, B),
    disjoint_xx( Comp, [A|As], [B|Bs]). 

disjoint_xx( '<', [_A|As], [B|Bs]) :- disjoint_x( As, [B|Bs] ).
disjoint_xx( '>', [A|As], [_B|Bs]) :- disjoint_x( [A|As], Bs ).
