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

:- module(linear_constraint,[
    true_lc/1, false_lc/1,  linear_constraint/3,
    clear_constant_lc/2, elements_lc/2, solve_element_lc/3,
    parse_lc/2, write_lc/2, write_natural_lc/2,
    to_greater_lc/2, to_greater_const_lc/2,
    to_nonstrict_overapprox_lc/2, to_nonstrict_underapprox_lc/2,
    to_leqs_lc/2,to_geqs_lc/2,coeffs_row_lc/4
]).

/** <module>
  A Linear Constraint has one of the forms "L<R", "L =< R", "L = R",
  "L >= R" or "L > R", where L,R are linear expressions.  
  
  Linear constraints are represented with terms 
  LC =.. [Op , Left, 0]  -- Left `op` 0 , 
  where left is a linear expression in integral form, and 
  Oper is a relational operator.
  
  type linear_constraint<A> =.. [relational, linear_expression<A>, 0]

  We shorten the linear constraint type as  "linconstr",
  and we use the suffix _lc" for methods using linear constraints. 

@author Diego Alonso
@license GPL
*/

:- use_module(fraction,[sign_fr/2, divide_fr/3, sum_fr/3,negate_fr/2]).
:- use_module(stdlib(term_utils),[replace_arg/5]).
:- use_module(stdlib(coefficients_sum),[coeffs_cs/3]).
:- use_module(linear_expression).
:- use_module(relational). 

get_oper( 1, Oper , Oper ).
get_oper( 0, Oper , NOper ) :- to_decrease_relational( Oper, NOper ).
get_oper( -1,Oper , NOper ) :-  reverse_relational( Oper, NOper ).

/*
true_lc( -Lin_Cons:linconstr<_>) is det. 

Lin_Cons is the linear constraint with the semantic value True. 
*/
true_lc( []+0=0 ).

/*
false_lc( -Lin_Cons:linconstr<_>) is det. 

Lin_Cons is the linear constraint with the semantic value False. 
*/
false_lc( []+1=0 ).

/*
linear_constraint( 
    + Lin_Exp : linearexp<A>, + Oper:relational , - Constraint : linconstr<A>
) is det.

Constraint is 
*/
linear_constraint( Lin_Exp, Oper, Lin_Cons) :-
    Lin_Exp = []+Const
    ->  Constraint =.. [Oper,Const,0],
        ( call(Constraint)
        ->  true_lc(Lin_Cons)
        ;   false_lc(Lin_Cons)
        )
    ;   integrate_le(Lin_Exp , _Coeff , Normal_LE),
        Lin_Cons =.. [Oper, Normal_LE, 0]. 

/*
clear_constant ( + Constraint:linconstr<A>, - NConstraint:linconstr<A>) is det.

NLC is a linear constraint parallel to LC which constant is zero.
*/
clear_constant_lc(LC, NLC) :-
    replace_arg( LC, 1, NLExp, LExp, NLC), 
	clear_constant_le(LExp,NLExp).

/*
elements_lc( + Constraint:linconstr<A>, -Vars:set<A>) is det.

Vars is the set of variables of LC
*/
elements_lc(LC,Vars) :- 
	LC =.. [_Op, LExp, 0 ],
	elements_le(LExp,Vars).

/*
solve_element_lc
*/
solve_element_lc( LC, Elem, Constr) :- 
    LC =.. [Oper, LExp, 0], 
    extract_elem_le( LExp, Elem, Coeff, LExp1), 
    divide_fr( -1, Coeff, Coeff1),
    multiply_le( LExp1, Coeff1, NLExp), 
    sign_fr( Coeff, Sign), 
    (Sign = -1
    ->  reverse_relational( Oper, NOper)
    ;   NOper = Oper
    ), 
    write_le( NLExp, Right), 
    Constr =.. [NOper, Elem, Right].    

/*
parse_lc( + Expression: Term , - Constraint:linconstr<A> )  is semidet.

Lin_Constraint is the linear constraint with the semmantics of the constraint 
expression Constraint_Exp, which must be an expression of the form

LCE ::= true
    |   false
    |   linear_expression<A> Op linear_expression<A>

where Op:relational_operator
*/
parse_lc( LC_Exp, NLC) :- 
    LC_Exp == true, 
    true_lc(NLC). 
parse_lc( LC_Exp, NLC) :- 
    LC_Exp == false, 
    false_lc(NLC).     
parse_lc(LC_Exp, NLC) :-
    compound(LC_Exp),
    LC_Exp =.. [Oper, Left, Right],
    is_relational(Oper), 
    parse_le(Left - Right, LExp),
    integrate_le(LExp , _Coeff , Normal_LE),
    NLC =.. [Oper, Normal_LE, 0].

/*
write_lc( + Constraint : linconstr<A>, - Expression: term ) is det.

LinConst_Exp is the output of Lin_Constraint as an expression "L Op 0" where 
L:linear_expression<A> and Op:relational_operator.
*/
write_lc(Constraint, Expression) :-
    replace_arg( Constraint, 1, LExp, LE, Expression ), 
    write_le(LE,LExp).

/*
write_natural_lc( 
    + Constraint : linconstr<A>, - Expression : natlc_exp<A> 
) is det. 

Writes the linear constraint in natural form.
*/
write_natural_lc(Constraint,Expression) :-
    Constraint =.. [Oper, LE, 0],
    split_le(LE,Pos,Neg),
    write_le(Pos,PosExp),
    write_le(Neg,NegExp),
    Expression =.. [Oper, PosExp, NegExp].

/*
*/
to_nonstrict_underapprox_lc( Lc, NLc ) :-
    Lc =.. [Oper, Coeffs + Const, 0],
    ( is_strict( Oper)
    ->  to_nonstrict_under_x( Oper, Const, NOper, NConst),
        NLc =.. [NOper, Coeffs + NConst, 0 ]
    ;   NLc = Lc
    ).

to_nonstrict_under_x( '<' , Const, '=<' , NConst ) :-
    sum_fr( Const,  1, NConst ).
to_nonstrict_under_x( '>' , Const, '>=' , NConst ) :-
    sum_fr( Const, -1, NConst ).

to_nonstrict_overapprox_lc( Lc, NLc ) :-
    Lc =.. [Oper, Le, 0],
    ( is_strict( Oper)
    ->  strict_nonstrict_relational( Oper, NOper),
        NLc =.. [NOper, Le, 0 ]
    ;   NLc = Lc
    ).

to_nonstrict_over_x( '<' , Const, '=<' , Const).
to_nonstrict_over_x( '>' , Const, '>=' , Const).


/*
to_greater_lc( + Lc, + GLc )

*/
to_greater_lc( Lc, Glc ) :- 
    Lc =.. [Oper , LExp, 0 ], 
    to_greater_x( Oper, LExp, NOper, NLExp), 
    Glc =.. [NOper, NLExp , 0].

to_greater_x( <,  LExp, >,  NLExp) :- negate_le( LExp, NLExp). 
to_greater_x( =<, LExp, >=, NLExp) :- negate_le( LExp, NLExp). 
to_greater_x( =,  LExp, =,  LExp). 
to_greater_x( >,  LExp, >,  LExp). 
to_greater_x( >=, LExp, >=, LExp). 

/*
to_greater_const_lc
*/
to_greater_const_lc( Lc, Glc) :- 
    Lc =.. [Oper , LExp, 0 ], 
    to_greater_x( Oper, LExp, NOper, Cs + Const ), 
    negate_fr( Const, NConst), 
    Glc =.. [NOper, Cs + 0, NConst].

/*
  to_geqs_lc 
  
*/
to_geqs_lc( LExp >= 0, [ LExp >= 0| T] - T).
to_geqs_lc( LExp =< 0, [NLExp >= 0| T] - T) :-
    negate_le( LExp, NLExp).
to_geqs_lc( LExp =  0, [ LExp >= 0, NLExp >= 0| T] - T) :-
    negate_le( LExp, NLExp).
to_geqs_lc( LExp > 0 , _ ) :-
    throw( strict_inequality_error( LExp > 0, to_geqs_lc ) ).
to_geqs_lc( LExp < 0 , _ ) :-
    throw( strict_inequality_error( LExp < 0, to_geqs_lc) ).

/*
  to_leqs_lc
*/
to_leqs_lc( LExp =< 0, [ LExp >= 0| T] - T).
to_leqs_lc( LExp >= 0, [NLExp >= 0| T] - T) :-
    negate_le( LExp, NLExp).
to_leqs_lc( LExp =  0, [ LExp =< 0, NLExp =< 0| T] - T) :-
    negate_le( LExp, NLExp).
to_leqs_lc( LExp > 0 , _ ) :-
    throw( strict_inequality_error( LExp > 0, to_leqs_lc ) ).
to_leqs_lc( LExp < 0 , _ ) :-
    throw( strict_inequality_error( LExp < 0, to_leqs_lc) ).


/*
  coeffs_row_lc( + Lc : linconstr<A> , + Elems: set<A>, -Row :list<fraction> , 
*/
coeffs_row_lc( Lc, Elems, Row , Konst ) :-
    Lc =.. [_Oper, Cs+Konst, 0 ] ,
    coeffs_cs( Cs, Elems, Row).
