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

:- module(linear_constraint_system,[
    true_lcs/1, false_lcs/1,
    add_constraint_lcs/3,
    clear_constants_lcs/2,
    elements_lcs/2,
    conjunction_lcs/3,
    evaluate_lcs/2,
    parse_lcs/2,write_lcs/2,write_natural_lcs/2,
    to_greater_lcs/2,to_greater_const_lcs/2,
    to_leqs_lcs/2, to_geqs_lcs/2,
    coeffs_matrices_lcs/4
]).

/** <module> A Linear Constraint System is a set of linear constraints.

type linear_constraint_system<A>  = set<linear_constraint<A>>

We shorten linear_constraint_system as "linconstrsys"

@author Diego Alonso
@license GPL
*/

:- use_module(stdlib(linear_constraint)).
:- use_module(stdlib(list_utils),[length_lu/2]).
:- use_module(stdlib(set_list),[insert_sl/3,contains_sl/2,union_sl/3,
    remove_sl/3, from_list_sl/2]).
:- use_module(stdlib(fraction_list),[negate_frl/2]).

/*
true_lcs( -Lcs: linconstrsys<A> ) is det.

Lcs is the constraint system True, that admits all vectors as a solution.
*/
true_lcs([]).

/*
false_lcs( - Lcs: linconstrsys<A> ) is det. 
*/
false_lcs( [Lc]) :- false_lc(Lc). 

/*
add_constraint_lcs
*/
add_constraint_lcs( Lcs, Lc, NLcs ) :- insert_sl( Lcs, Lc, NLcs ).

% TODO adapt this implementation to work also with non-variables. 

/*
conjunction_lcs( 
    + Lcs_A: linconstrsys<A>, + Lcs_B: linconstrsys<A>, - NLcs: linconstrsys<A>
) is det. 

NLcs is a linear constraint system which meaning is the conjunction of 
Lcs_A and Lcs_B. 
*/
conjunction_lcs( Lcs_A, Lcs_B, NLcs ) :- union_sl( Lcs_A, Lcs_B, NLcs ).

evaluate_lcs( Lcs, NLcs ) :- 
    false_lc( FLc ), 
    ( contains_sl( Lcs, FLc ) 
    ->  false_lcs( NLcs ) 
    ;   true_lc( TLc ), 
        remove_sl( Lcs, TLc, NLcs )
    ).

/*
clear_constants_lcs( + Lcs:linconstrsys<A>, -NLcs:linconstrsys<A>) is det.
*/
clear_constants_lcs( [], [] ).
clear_constants_lcs( [Lc|Lcs], NLcs ) :-
    clear_constants_lcs( Lcs, NLcs1 ),
    clear_constant_lc( Lc, NLc ),
    insert_sl( NLcs1, NLc, NLcs ).

/*
elements_lcs( + Lcs : linconstrsys<A>, -Vars:set<A> ) is det.

*/
elements_lcs( Lcs, Vars ) :- elements_x( Lcs, [], Vars ).
elements_x( [], Vars, Vars ).
elements_x( [Lc|Lcs], Vars0 , Vars ) :- 
    elements_lc( Lc, VLc ),
    union_sl( Vars0, VLc, Vars1 ), 
    elements_x( Lcs, Vars1, Vars ).

/*
parse_lcs( + Expr : ?, - Lcs : linconstrsys<A> ) is semidet.

LinConstr_System is the 

A lcs_expression must follow this grammar: 
lcs_expression ::=  [ lc_expression]
where lc_expression is a linear constraint. 
*/
parse_lcs( Exp, Lcs ) :- 
    parse_x( Exp, Lcsx ), 
    from_list_sl( Lcsx, Lcs). 

parse_x( [], [] ).
parse_x( [Exp|Exps], [Lc|Lcs] ) :-
    parse_lc( Exp, Lc ),
    parse_x( Exps, Lcs ).


/*
write_lcs( + Lcs:linconstrsys<A>,  - Expression_Lcs:lcs_expression) is det.

Writes Lcs as an expression with the form 
lcs_expression ::= [ lc_expression]
*/
write_lcs( [], [] ).
write_lcs( [Lc|Lcs] , [LcExp|LcExps] ) :-
    write_lc( Lc, LcExp ),
    write_lcs( Lcs, LcExps ).

/*
write_natural_lcs( + Lcs : linconstrsys<A>,  - Expression:term). 

Write the System of linear constraints in natural form. 
*/
write_natural_lcs( [] , []).
write_natural_lcs( [Lc|Lcs] , [LcExp| LcExps] ):-
    write_natural_lc( Lc, LcExp ),
    write_natural_lcs( Lcs, LcExps ).


/*
to_nonstrict_underapprox_lcs( + Lcs : linconstrsys , - NLcs : 

NLcs is the result of overapproximating all the strict linear constraints from
Lcs. The resulting 
*/
to_nonstrict_underapprox_lcs( [], [] ).
to_nonstrict_underapprox_lcs( [Lc|Lcs], [NLc|NLcs] ) :-
    to_nonstrict_underapprox_lc( Lc, NLc ), 
    to_nonstrict_underapprox_lcs( Lcs, NLcs). 


/*
to_nonstrict_overapprox_lcs( + Lcs, - NLcs ) 
*/
to_nonstrict_overapprox_lcs( [], [] ).
to_nonstrict_overapprox_lcs( [Lc|Lcs], [NLc|NLcs] ) :-
    to_nonstrict_overapprox_lc( Lc, NLc ), 
    to_nonstrict_overapprox_lcs( Lcs, NLcs). 

/*
to_greater_lcs( 
*/
to_greater_lcs( [], []). 
to_greater_lcs( [Lc|Lcs], [Glc|Glcs] ) :- 
    to_greater_lc( Lc, Glc), 
    to_greater_lcs( Lcs, Glcs). 

/*
to_greater_cons_lcs
*/
to_greater_const_lcs( [] , [] ). 
to_greater_const_lcs( [Lc|Lcs] , [Glc|Glcs] ) :- 
    to_greater_const_lc( Lc , Glc ), 
    to_greater_const_lcs( Lcs, Glcs ). 


/*
  to_leqs_lcs( + Lcs ,)
*/
to_leqs_lcs( [] ,[]).
to_leqs_lcs( [Lc|Lcs], GEqs ) :-
    to_leqs_lc( Lc, GEqs - GEqs_x) ,
    to_leqs_lcs( Lcs, GEqs_x ).

/*
  to_geqs_lcs( + Lcs,  ) is det. 
*/
to_geqs_lcs( [] ,[]).
to_geqs_lcs( [Lc|Lcs], GEqs ) :-
    to_geqs_lc( Lc, GEqs - GEqs_x) ,
    to_geqs_lcs( Lcs, GEqs_x ).

/**/
to_ineqs_lcs( Lcs, =<, INeqs) :- to_leqs_lcs( Lcs, INeqs).
to_ineqs_lcs( Lcs, >=, INeqs) :- to_geqs_lcs( Lcs, INeqs).


/*
  to_matrices_lcs( +  Lcs :lcs<A>, + Elems: set<A> ,
  - As: list<list<fraction>>, - Bs: list<fraction>  
*/
coeffs_matrices_lcs( [], _Elems, [], [] ).
coeffs_matrices_lcs( [Lc|Lcs], Elems, [Row|Rows], [B|Bs] ) :-
    coeffs_row_lc( Lc, Elems, Row , B ), 
    coeffs_matrices_lcs( Lcs, Elems, Rows, Bs ). 

