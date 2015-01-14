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

:- module(linear_expression,[
    zero_le/1,
    add_coeff_elem_le/4,  add_constant_le/3,
    coefficient_le/3, constant_le/2, is_constant_le/1,
    clear_constant_le/2,
    elements_le/2,
    extract_elem_le/4,
    negate_le/2, sum_le/3, subtract_le/3, multiply_le/3,
    split_le/3,
    normalize_le/3, semi_normalize_le/3, weak_normalize_le/3,
    integrate_le/3,
    parse_le/2,  write_le/2
]).

/** <module> A Linear Expression is an expression with the form 
"a_1 * X_1 + ...  + a_n * X_n + K"  where 
 * each "X_i" is a term of type A 
 * each "a_i" is a non-zero rational number and 
 * "K" is a rational number.

type linear_expression<A> =  Coeffs + Const where
 * Coeffs: coefficients_sum<A> 
 * Const : fraction

We shorten linear_expression with linearexp. 


@author Diego Alonso
@license GPL
*/

:- use_module(fraction).
:- use_module(coefficients_sum).
:- use_module(fraction_list,[naturalize_frl/3]).
:- use_module(stdlib(pair_list),[zip/3,unzip/3]).
:- use_module(stdlib(list_map),[open_cursor_lm/4,close_cursor_lm/3]).

/*
zero_le( - Zero : linearexp<A> ) is det.  

Zero is the linear expression with no variables and with constant value zero. 
*/
zero_le( []+0 ).

/*
add_coeff_elem_le(  
    + LExp:linearexp<A>, + Coeff:fraction, + Elem:A, - NLExp:linearexp<A>
) is det.

NLin_Exp = Lin_Exp + Coeff * Elem
*/
add_coeff_elem_le( Coeffs+Const  , Coeff, Var, NCoeffs+Const ) :-
    add_coeff_elem_cs( Coeffs, Coeff, Var, NCoeffs ).

/*
add_constant_le( 
    + LExp : linexp<A>, + Const : fraction - NLExp : linexp<A>
) is det. 

NLExp = LExp + Const
*/
add_constant_le( Coeffs+OConst, Const, Coeffs+NConst ) :-
	sum_fr( OConst, Const, NConst ).

/*
coefficient_le( 
    + LExp : linexp<A>, + Elem : A, - Coeff : fraction
) is det. 

Coeff is the coefficient of Var in LinExp.
*/
coefficient_le( Coeffs+_Const , Var, Coeff) :- 
    coeff_cs( Coeffs, Var, Coeff ).

/*
constant_le( + LExp : linexp<A>, - Constant : fraction) is det.

Constant is the constant value of  Linear_Exp
*/
constant_le( _Coeffs+Const , Const).

/*
clear_constant_le( + LExp : linexp<A>, - NLExp : linexp<A>) is det.

NLExp is the result of setting the constant of Lin_Exp to zero. 
*/
clear_constant_le( Coeffs+_Const, Coeffs+0 ).

/*
is_constant( + LExp : linexp<A> ) is semidet.

Returns true if Lin_Exp is a constant linear expression, that is to say if it
has no variables.
*/
is_constant_le( [] + _Const ).

/*
elements_le(  + LExp : linexp<A> , - Elements : set<A>) is det.

Elements is the set of elements of the linear expression Lin_Exp. 
*/
elements_le( Coeffs+_Const, Vars ) :- elements_cs( Coeffs, Vars ).

/*
negate_le
*/
negate_le( LExp, Neg_Lexp ) :- multiply_le( LExp, -1, Neg_Lexp ). 


/*
sum_le( + LExpA : linexp<A>, + LExpB : linexp<A>, - NExp : linexp<A>) is det.

NLExp is the sum of the linear expressions LExpA and LExpB. 
NLExp = LExpA + LExpB
*/
sum_le( LExpA, LExpB, NLExp ) :-
    LExpA = CoeffsA + ConstA,
    LExpB = CoeffsB + ConstB,
    sum_cs( CoeffsA, CoeffsB, NCoeffs ),
    sum_fr( ConstA, ConstB, NConst ),
    NLExp = NCoeffs + NConst. 

/*
subtract_le( 
    + LExpA : linexp<A> , - LExpB : linexp<A>, - NLExp : linexp<A>
) is det.

NLExp is the subtraction of Lin_ExpA and Lin_ExpB, that is to say

NLExp = LExpA - LExpB.
*/
subtract_le( LExpA, LExpB, NLExp) :-
    LExpA = CoeffsA + ConstA,
    LExpB = CoeffsB + ConstB,
    subtract_cs( CoeffsA, CoeffsB, NCoeffs ),
    subtract_fr( ConstA, ConstB, NConst ),
    NLExp = NCoeffs + NConst. 

/*
multiply_le( 
    + LExp : linexp<A>, + Scalar : fraction, - NLExp : linexp<A> 
) is det.

Multiplies all the coefficients and the constant by the given fraction. 
*/
multiply_le( LExp , Frac , NLExp ) :-
    LExp = Coeffs + Const, 
    multiply_cs( Coeffs, Frac, NCoeffs),
    multiply_fr( Const, Frac, NConst),
    NLExp = NCoeffs + NConst. 

/*
split_le( 
    + LExp: linexp<A>, - Pos_LE : linexp<A>, - Neg_LE : linexp<A>
) is det.
          
Separates LExp in Pos_LE and Neg_LE, with the following properties: 
 * The coefficients and constant of Pos_LE and Neg_LE are positive fractions.
 * LExp = Pol_LE - Neg_LE
 
Examples: 
 * split_le( []+0 , P, N)                   ?   P = []+0 , N = []+0. 
 * split_le( [(a,1),(b,-1)]+(-1) , P, N)    ?   P = [(a,1)]+0 , N = [(b,1)]+1. 

*/
split_le( Coeffs+Const , PosCs+PC , NegCs+NC ) :-
    split_cs( Coeffs, PosCs, NegCs ),
    sign_fr( Const,S ), 
    abs_fr( Const, C ),
    split_x( S, C, PC, NC ). 

split_x(-1, C, 0, C).
split_x( 0, 0, 0, 0).
split_x( 1, C, C, 0).

/*
normalize_le( 
    + LExp : linexp<A>, - Coeff : fraction, - NLExp : linexp<A>
) is det.

NLin_Exp is a linear expression proportional to Lin_Exp with 
<LaTeX> Lin_Exp = Frac * NLin_Exp </LaTeX>

and NLin_Exp is in normal form: either it's a constant of value 1 or its first 
coefficient is +1.     
*/
normalize_le( LExp , Const , NLExp ) :-
    LExp = [] + Const, 
    !, 
    non_zero_fr( Const, NConst), 
    NLExp = [] + NConst.
normalize_le( LExp , Coeff , NLExp ) :-
    % Cut-implicit: Coeffs non empty
    LExp = Coeffs + Const, 
    extract_first_coefficient_cs( Coeffs, Coeff, NCoeffs ), 
    divide_fr( Const, Coeff, NConst ), 
    NLExp = NCoeffs + NConst.

/*
semi_normalize_le( 
    + LExp : linexp<A>, - Coeff : fraction, - NLExp : linexp<A>
) is det.

NLin_Exp is a linear expression proportional to Lin_Exp with 
<LaTeX> LExp = Frac * NLExp </LaTeX>
where Frac is a fraction of positive value (or zero).

and NLExp is in normal form: either it's a constant of value 1 or -1 
or its first coefficient is either  +1 or -1.     

*/
semi_normalize_le(LExp, Coeff, NLExp) :-
    LExp = [] + Const, 
    !, 
    abs_fr(Const,Coeff),  
    sign_fr(Const, NConst), 
    NLExp = [] + NConst. 
semi_normalize_le(LExp, Coeff, NLExp) :-
    LExp = Coeffs + Const, 
    extract_first_abs_coefficient_cs(Coeffs, Coeff, NCoeffs), 
    divide_fr(Const, Coeff, NConst), 
    NLExp = NCoeffs + NConst. 

/*
weak_normalize_le( 
    + LExp : linexp<A>, - Coeff : integer, - NLExp : linexp<A>
) is det.

NLin_Exp is a linear expression proportional to Lin_Exp with 
<LaTeX> Lin_Exp = Frac * NLin_Exp </LaTeX>

and NLin_Exp is in normal form: either it's a constant of value 1, 0 or -1 
or its first coefficient is either  +1 or -1.     

*/
weak_normalize_le(LExp, Coeff, NLExp) :-
    LExp = [] + Const, 
    !,
    numerator(Const,C2),
    Coeff is abs(C2),
    sign_fr( Const, NConst), 
    NLExp = [] + NConst. 
weak_normalize_le(LExp, Coeff, NLExp) :-
    LExp = Coeffs + Const, 
    extract_first_natural_numerator_cs(Coeffs, Coeff, NCoeffs), 
    divide_fr(Const, Coeff, NConst), 
    NLExp = NCoeffs + NConst. 

/*
integrate_le( + LExp : linexp<A>, - Denom:integer, - NLExp:linexp<A>) is det.
              
Refactors Lin_Exp in Denom and NLin_Exp, such that 
 * Lin_Exp = NLin_Exp / Denom
*/
integrate_le( Coeffs + Const , Denom, NCoeffs+NConst) :- 
    unzip(Coeffs,Elems, Frs), 
    naturalize_frl([Const|Frs], [NConst | NFrs], Denom), 
    zip(Elems,NFrs,NCoeffs). 

/*
extract_elem_le( + LExp, + Var, - Coeff, - NLExp
*/
extract_elem_le( Coeffs + Const, Elem, Coeff, NCoeffs + Const) :- 
    open_cursor_lm( Coeffs, Elem, MCoeff, Cursor), 
    close_cursor_lm( Cursor, [], NCoeffs), 
    eval_mcoeff( MCoeff, Coeff). 

eval_mcoeff( [], 0). 
eval_mcoeff( [Coeff], Coeff).

/*
parse_le( + Expression,  - LExp: linexp<A>)

Lin_Exp is the linear expression (representation) that is obtained after parsing
Expression, if Expression is a Linear Expression with the following grammar: 

LinearExp   ::= Fraction 
            |   A
            |   LinearExp * Fraction | Fraction * LinearExp
            |   LinearExp / Coeff
            |   + LinearExp
            |   - LinearExp
            |   LinearExp + LinearExp
            |   LinearExp - LinearExp
*/
parse_le( Expression, LExp) :- parse_x(Expression,[] + 0,1,LExp).
% Design pattern: it runs through expression syntactic tree carrying the 
% linear expression being built, as a pair inherited-synthetized attribute

% Rule: LinearExp :: Fraction
parse_x(Exp, LinH,Coeff,LinS) :-
	parse_fr(Exp,Frac), 
	!,
	multiply_fr(Coeff,Frac,NC),
	add_constant_le(LinH,NC,LinS).

% Rule: LinearExp ::= + LinearExp 
parse_x(Exp,LinH,Coeff,LinS) :-
	compound(Exp),
	Exp = + A,
	!,
	parse_x(A,LinH,Coeff,LinS).

% Rule: LinearExp ::=  - LinearExp 
parse_x(Exp,LinH,Coeff,LinS) :-
    compound(Exp),
    Exp = - A,
	!,
	negate_fr(Coeff,NewC),
	parse_x(A,LinH,NewC,LinS).

% Rule:LinearExp ::= LinearExp  + LinearExp
parse_x(Exp,LinH,Coeff,LinS) :-
    compound(Exp),
    Exp = A+B,
    !,
    parse_x(A, LinH,Coeff,LS1),
    parse_x(B, LS1 ,Coeff,LinS).

% Rule:LinearExp ::= LinearExp  - LinearExp
parse_x(Exp,LinH,Coeff,LinS) :-
    compound(Exp),
    Exp = A-B,
    !,
    parse_x(A, LinH,Coeff,LS1),
    multiply_fr(Coeff,-1,NegC),
    parse_x(B, LS1,NegC,LinS).

% Rule: LinearExp ::= Fraction * LinearExp | LinearExp * Fraction 
parse_x(Exp,LinH,Coeff,LinS) :-
    compound(Exp),
    Exp = A*B,
    ( parse_fr(A,Frac) 
    ->  NExp = B
    ;   parse_fr(B,Frac), 
        NExp = A
    ),
    !,
	multiply_fr(Frac,Coeff,NewC),
	parse_x(NExp,LinH,NewC,LinS).

% Rule: LinearExp ::= LinearExp / Fraction
parse_x(Exp,LinH,Coeff,LinS) :-
    compound(Exp), 
    Exp = A/B, 
    parse_fr(B,Frac), 
    !,
	divide_fr(Coeff,Frac,NCoeff),
	parse_x(A,LinH,NCoeff,LinS).


% Rule : LinearExp ::= A 
parse_x(Elem,LinH,Coeff,LinS) :- add_coeff_elem_le(LinH,Coeff,Elem,LinS).

/*
write_le( +Linear_Exp:linear_expression<A>, -Expression:_ ) is det. 

Exp is the representation of LinearExp without parenthesis. That will have 
the following grammar: 

LinearExp ::= fraction. 
LinearExp ::= LinearExpCoeffs<A> + fraction         <-- fraction > 0 
LinearExp ::= LinearExpCoeffs<A> - fraction         <-- fraction > 0 

LinearCoeffs_Exp ::= fraction * A
LinearCoeffs_Exp ::= LinearCoeffs_Exp + LinearElem
LinearCoeffs_Exp ::= LinearCoeffs_Exp - LinearElem

LinearElem ::= A 
LinearElem ::= fraction * A                         <-- fraction> 0 
LinearElem ::= A / integer                          <-- integer >= 2 

*/
write_le([] + Const, Const) :- !.
write_le(Coeffs+Const, ExpLin) :-
    % Cut-Implicit: Coeffs \= [] 
    write_cs(Coeffs,CSExp),
    write_x(CSExp,Const,ExpLin).

write_x(CSExp,0,CSExp) :- !. 
write_x(CSExp,Const,ExpLin) :- 
    % Implicit: Const \== 0 
    abs_fr(Const, AConst), 
    sign_fr(Const,Sign),
    sign_oper(Sign,Oper),
    ExpLin =.. [Oper , CSExp , AConst].

sign_oper(-1,'-').
sign_oper(1,'+').
