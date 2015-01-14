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

/** <module> 


@author Diego Alonso
@license GPL
*/

:- module(parsing_writing, [
    parse_operator/3,
    parse_operator_list/3,
    write_map/3,
    write_lists_map/3,
    write_foldl1/3,
    write_foldr1/3,
    write_sum/2,
    write_product/2,
    write_biproduct/3
]).

/*
parse_operator ( + ExpA , + Oper , + Neutral , - ExpBs) :: (
    expression_a , functor , list<expression_b>
).

"Compiles" or parses a expression of type Expression_A, that are built with the
following generic grammar:

ExpA    ::= ExpB
        |   Oper(ExpA,ExpA,...)
where oper may have any number of operands.

compiling, here, means obtaining a list of Expressions of type B, following
this attribute grammar (described by code) 

When the ExpBs are compiled, the list shows them following a"pre-order" of 
the syntactic tree of ExpA.

*/
parse_operator( Exp, Oper, ExpBs) :- 
    parse_operator_x( Exp, Oper, [], ExpBs).

parse_operator_x( Exp , Oper, EBs0,ExpBs) :- 
    compound(Exp),
    Exp =.. [Oper| Args],
    !,
    parse_operator_xx(Args,Oper,EBs0,ExpBs).
% Catchall: it is not an Oper-ation
parse_operator_x( Exp , _Oper, EBs0,[Exp|EBs0]).

parse_operator_xx([] , _Oper, ExpBs,ExpBs). 
parse_operator_xx([Arg|Args] , Oper, EBs0,ExpBs) :- 
    parse_operator_xx(Args,Oper,EBs0,EBs1),
    parse_operator_x(Arg,Oper,EBs1,ExpBs).


/*
parse_operator_list (
    + Exps , Oper, ExpBs
)  is det.
*/
parse_operator_list(Exps,Oper,ExpBs) :-
    parse_operator_xx(Exps,Oper,[],ExpBs).


/*
write_map( + Functor:atom, + Exps:list<A>, - Terms:Functor<A> ). 

*/
write_map(_Functor,[],[]) :- !. 
write_map( Functor, [Exp|Exps], [Term|Terms]) :- 
    Term =.. [Functor, Exp], 
    write_map(Functor, Exps,Terms). 


/*
write_lists_map( 
    + Functor:atom, + ArgsLists: list< list<A > >, - Terms:Functor<A>
) is det.
*/
write_lists_map(_Functor, [] , []) :- !. 
write_lists_map( Functor, [Args| ArgsLists] , [Term|Terms]) :- 
    Term =.. [Functor | Args],
    write_lists_map(Functor, ArgsLists,Terms). 
    

/*
write_foldl1( + List , + Functor , - Term) 

Builds a term applying the the binary functor Functor to the elements of the 
list: 
-. If List is empty, the predicate Fails.
- If List is a singleton , then Term is the only element in the list.
- If list has two elements LS = [A,B], then Term is Functor(A,B).
- For more than two elements, the lists build a chain of binary functors, using
left-associativity: 

Example: 
write_foldl1( 
    [ a ,b ,c ] , 
    f,
    f( f(a,b),c )
).

write_foldl1( 
    [ a ,b ,c ] , 
    '+',
    f( a+b+c )
).

*/
write_foldl1( [ X| Xs], F , Term) :-  write_foldl1_x(Xs,X,F,Term).

write_foldl1_x([],Term,_F,Term) :-!.
write_foldl1_x([C|Cs],T0,F,Term) :- 
    !,
    T1 =.. [F,T0,C],
    write_foldl1_x(Cs,T1,F,Term).


/*
write_foldr1( + List:list<T> , + Functor , - Term:) is semidet.

Builds a term applying the binary Functor to the elements of the List: 
- If List is empty, the predicate Fails.
- If List is a singleton , then Term is the only element in the list.
- If list has two elements LS = [A,B], then Term is Functor(A,B).
- For more than two elements, the lists build a chain of binary functors, using
right-associativity.

Examples: 
write_foldr1( [ a ,b ,c ] ,  f  , f(a,f(b,c)) ).
write_foldr1( [ a ,b ,c ] , '+' , a+(b+c)       ).

*/
write_foldr1( [X|Xs], F, T) :- write_foldr1_x( Xs, X, F, T).

write_foldr1_x( [], X, _F, X).
write_foldr1_x( [Y|Ys], X, F, T) :- 
    T =.. [F,X,T1],
    write_foldr1_x(Ys,Y,F,T1).

/*
write_sum( + Adds:list<A>, - Expr:_) is det.

*/
write_sum([],0).
write_sum([X|Xs],Exp) :- write_foldl1([X|Xs],'+',Exp).


/*
  write_biproduct( + As, + Bs , - Exp)
*/
write_biproduct( As, Bs , Exp) :-
    write_prods( As, Bs, Ps),
    write_sum( Ps, Exp).


write_prods( [], [], []). 
write_prods( [A|As], [B|Bs], [A*B|Ps]) :-
    write_prods( As,Bs,Ps).



/*
write_product :: list , product

[a,b,c]   -> a*b*c
*/
write_product([],1).
write_product([X|Xs],Exp) :- write_foldl1([X|Xs], '*', Exp).

