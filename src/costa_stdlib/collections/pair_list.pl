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

:- module(pair_list,[
    zip/3,
    unzip/3,
    zip_with/4,
    unzip_with/4,
    cartesian_product/3,
    cartesian_product_with/4,
    cartesian_product_list_with/3,
    swap_pl/2,
    firsts_pl/2,
    seconds_pl/2, 
    lookup_first_pl/3,
    lookup_second_pl/3,
    remove_first_pl/3,
    remove_second_pl/3
]).

/** <module> Utilities for processing and manipulating lists of pairs.

A pair is just a term with two elements separated by a comma.

@author Diego Alonso. 
@license GPL
*/

:- use_module(stdlib(term_utils),[terms_get_args/3]).

/*
zip( +As:list<A>, +Bs:list<B>, -Ps:list<(A,B)> ) is det. 

Ps is the list of pairs (A,B) such that 

forall i: 0 =< i < Ps.length : Ps[i] = (a,b) <--> As[i] = a  & Bs[i] = b

Property: zip(As,Bs,Ps) -->  Ps.length = min( As.length , Bs.length ) 
*/
zip( As,Bs,Ps) :- zip_with( ',' , As,Bs,Ps). 

/*
unzip( +Ps:list<(A,B)>, -As:list<A>, -Bs:list<B>) is det. 

Separates the first and second elements of a list of pairs in two lists.

This is the "inverse" operation of zip:
unzip(Ps,As,Bs) \rightarrow Ps.length = As.length = Bs.length
As.length=Bs.length , zip(As,Bs,Ps) \rightarrow unzip(Ps,As,Bs).
unzip(Ps,As,Bs) \rightarrow zip(As,Bs,Ps)

*/
unzip(Ps,As,Bs) :- unzip_with(',',Ps,As,Bs).

/*
zip_with( :Func, +As:list<A>, +Bs:list<B>, -Ps:list<Func(A,B)>) is det. 

Ps is the list of compound term which have functor Func and two arguments, 
and for each element Ps[i] those arguments are, precisely, As[i] and Bs[i].


*/
zip_with( _Func, [] , _Bs, []) :- !. 
zip_with( _Func, _As, [] , []) :- !. 
zip_with( Func, [A|As], [B|Bs] , [P|Ps]) :-
    P =.. [Func, A,B],
    zip_with(Func,As,Bs,Ps).

/*
unzip_with( 
    : Func, + Ps : list<Func(a,b)>, - As : list<A>, - Bs : list<A> 
) is det. 

*/
unzip_with( Func, Ps, As, Bs) :- unzip_x( Ps, Func, As, Bs ).

unzip_x( [], _Func, [], [] ).
unzip_x( [P|Ps], Func, [A|As], [B|Bs] ) :- 
    P =.. [Func, A, B], 
    unzip_x( Ps, Func, As, Bs ).

/*
cartesian_product ( +As:list<A>, +Bs:list<B>, -Ps:list<(a,b)>) is det. 

Ps is the cartesian product of As and Bs.

Example: cartesian_product( [a,b,c],    [1,2],    [ 
    (a,1),(a,2),(b,1),(b,2),(c,1),(c,2)
]).
*/
cartesian_product( As, Bs, Ps ) :- cartesian_product_with( ',', As, Bs, Ps).

/*
cartesian_product_with( 
    :Func : functor , + As : list<A> , +Bs : list<B>, - Terms : Func<A,B>
) is det. 
*/
cartesian_product_with( Func, As, Bs, Ps) :- carpro_x( As, Bs, Func, Ps).

carpro_x( [], _Bs, _Func, []).
carpro_x( [A|As], Bs, Func, Ps) :- 
    carpro_xx( Bs, A, Func, Ps, Ps_t), 
    carpro_x( As, Bs, Func, Ps_t).

carpro_xx( [], _A, _Func, Ps_t, Ps_t ).
carpro_xx( [B|Bs], A, Func, [P|Ps_x], Ps_t ) :- 
    P =.. [Func , A , B],
    carpro_xx( Bs, A, Func, Ps_x, Ps_t ).   

/*
cartesian_product_list_with( Lists, Func, Ps ). 
*/
cartesian_product_list_with( [], _Func, [] ). 
cartesian_product_list_with( [L|Ls], Func, Ps ) :- 
    carproliwi_x( Ls, L, Func, Ps). 
    
carproliwi_x( [], L, _Func, L). 
carproliwi_x( [L|Ls], Acc, Func, Ps) :- 
    cartesian_product_with( Func, Acc, L, NAcc), 
    carproliwi_x( Ls, NAcc, Func, Ps). 
    



/*
swap_pl( +Ps:list<(A,B)>, -Ns:list<(B,A)>) is det.

Ns is the list that contains all pairs of Ps but swapped.
*/
swap_pl( Ps, Ns ) :- unzip( Ps, As, Bs ) , zip( Bs, As, Ns ).

/*
firsts_pl( + Pairs : list<(A,_)>, - Fsts : list<A> ) is det.
*/
firsts_pl( Pairs, Fsts ) :- terms_get_args( Pairs, 1, Fsts ).

/*
seconds_pl( + Pairs : list<(_,B)>, - Snds : list<A> ) is det.
*/
seconds_pl( Pairs, Snds ) :- terms_get_args( Pairs, 2, Snds ).

/*
lookup_first_pl( + Pairs : list<(A,B)>, + Fst : A, - Snd : B ) is nondet. 
*/
lookup_first_pl( [ Pair|_Pairs], Fst, Snd) :-
    Pair = ( PFst, PSnd ),
    PFst == Fst,
    Snd = PSnd.

lookup_first_pl( [ _Pair|Pairs], Fst, Snd) :-
    % implicit: it isn't this pair
    lookup_first_pl( Pairs, Fst, Snd).

/*
lookup_second_pl( + Pairs:list<(A,B)> , + Snd: B, - Fst : A) is nondets. 

*/
lookup_second_pl( [ Pair | _Pairs] , Snd, Fst) :-
    Pair = ( PFst,PSnd),
    PSnd == Snd,
    Fst = PFst.

lookup_second_pl( [ _Pair|Pairs], Fst, Snd) :-
    % implicit: it isn't this pair
    lookup_second_pl( Pairs, Fst, Snd). 

/*
remove_first_pl
*/
remove_first_pl( [], _Fst, [] ). 
remove_first_pl( [Pair|Pairs], Fst, NPairs ) :-
    remove_first_pl_x( Pair, Fst, Pairs1, NPairs), 
    remove_first_pl( Pairs, Fst, Pairs1).

remove_first_pl_x( Pair , Fst, Pairs, NPairs) :- 
    Pair = ( PFst, _PSnd),
    ( Fst == PFst
    ->  NPairs = Pairs
    ;   NPairs = [ Pair | Pairs ]
    ).

/*
remove_second_pl
*/
remove_second_pl( [], _Snd, [] ). 
remove_second_pl( [Pair|Pairs], Snd, NPairs ) :-
    remove_second_pl_x( Pair, Snd, Pairs1, NPairs), 
    remove_first_pl( Pairs, Snd, Pairs1).  

remove_second_pl_x( Pair, Snd, Pairs, NPairs) :- 
    Pair = ( _PFst, PSnd), 
    ( Snd == PSnd
    ->  NPairs = Pairs
    ;   NPairs = [Pair|Pairs]
    ).
