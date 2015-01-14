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

:- module(coefficients_sum,[
    zero_cs/1,
    add_coeff_elem_cs/4,
    coeff_cs/3,
    coeffs_cs/3,
    negate_cs/2,sum_cs/3, subtract_cs/3, multiply_cs/3, divide_cs/3,
    elements_cs/2,
    extract_first_coefficient_cs/3,
    extract_first_abs_coefficient_cs/3,
    extract_first_natural_numerator_cs/3,
    split_cs/3,
    write_cs/2,
    product_cs/3
]).

/** <module> A sum of coefficients represents an expression of the form 
"c_1 * a_1 + c_2 * a_2 + ... + c_n * a_n" where each "a_i" is a non-zero 
rational number.

The implementation maps each element of the parametric type A to its 
coefficient in the expression, and those not in the map are understood to have
a zero coeff.  

type coefficients_sum<A> = map<A ,fraction>  
    where all values V hold $ V \neq 0 $.

The abbreviation for the predicates of coefficients sum will be "cs".
We use the word "coeffsum" as a shorthand for "coefficients_sum". 

@author Diego Alonso
@license GPL
*/

:- use_module(stdlib(list_map)).
:- use_module(stdlib(fraction),[
    fraction/3,decompose_fr/3,numerator/2,denominator/2,greater_fr/2,geq_fr/2,
    lesser_fr/2,leq_fr/2,negate_fr/2,abs_fr/2,sign_fr/2,sum_fr/3,
    subtract_fr/3,multiply_fr/3,inverse_fr/2,divide_fr/3
]).
:- use_module(stdlib(fraction_list),[zip_product_frl/3]).
:- use_module(stdlib(maybe),[eval_maybe/3]).
:- use_module(stdlib(pair_list),[zip/3,unzip/3]).


read_coeff(MC,C) :- eval_maybe(MC,0,C).

/*
zero_cs( + CSum : coeffsum<A> ) is semidet. 
zero_cs( - CSum : coeffsum<A> ) is det. 

CSum is the coefficient sum with the value Zero.
*/
zero_cs([]).

/*
add_coeff_elem_cs( 
    + CSum : coeffsum<A>, + Coeff : fraction, + Elem : A, - NCSum: coeffsum<A>
) is det. 

NCSum is the result of adding to CS

NCSum = CSum + ( Coeff * Elem ) 
*/
add_coeff_elem_cs( CSum, Coeff, Elem, NCSum) :-
	open_cursor_lm( CSum , Elem , MCoeff , Cursor),
	read_coeff( MCoeff,OCoeff),
	sum_fr( OCoeff, Coeff, NCoeff) ,
	(NCoeff == 0 
	->	NMCoeff = []
	;	NMCoeff = [ (Elem,NCoeff) ] 
	),
	close_cursor_lm(Cursor, NMCoeff, NCSum).

/*
coeff_cs( + CSum : coeffsum<A>, + Elem : A, - Coeff : fraction) is det. 

Coeff is the coefficient of Elem in CSum.
*/
coeff_cs( CSum, Elem, Coeff) :-
	open_cursor_lm( CSum, Elem, MCoeff, _Cursor),
	read_coeff( MCoeff,  Coeff).


/*
coeff_cs( + CSum : coeffsum<A>, + Elems : set<A>, - Coeffs : list<fraction>) is det. 

Coeff is the coefficient of Elem in CSum.
*/
coeffs_cs( CSum, Elems, Coeffs ) :-
    project_lm( CSum, Elems, CS1),
    fillup_lm( CS1, Elems, 0, CS2),
    values_lm( CS2, Coeffs).     

/*
elements_cs( + CSum : coeffsum<A>, - Elems : set<A>) is det. 

Elems is the set of elements of the coefficient sum CSum. 
*/
elements_cs(CSum, Elems) :- keys_lm(CSum, Elems).

/*
*/
negate_cs( CSum, NCSum ) :- multiply_cs( CSum, -1 , NCSum ). 
/*
sum_cs( 
    + CSumA : coeffsum<A> , + CSumB : coeffsum<A>, - NCSum : coeffsum<A> 
) is det. 

Sum of coefficients sums: 
NCSum = CSumA + CSumB
*/
sum_cs( CSumA, CSumB, NCSum ) :-
	zip_lm( CSumA, CSumB, ZCSum),
	sum_x( ZCSum, NCSum).

sum_x([] , [] ).
sum_x( [ ZPair | ZCSum ] ,NCSum) :-
    sum_xx( ZPair, NCS1, NCSum),
    sum_x( ZCSum, NCS1).

sum_xx( ( Elem, Coeffs), NCS1, NCSum) :- 
	sum_coeffs( Coeffs, NCoeff),
	insert_coeff( NCoeff, Elem, NCS1, NCSum). 

sum_coeffs( left(A), A).
sum_coeffs( right(B), B). 
sum_coeffs( both(A,B), Sum) :- sum_fr(A, B, Sum).

insert_coeff( 0, _Elem, CSum, CSum) :- !. 
insert_coeff( Coeff, Elem, CSum, [(Elem, Coeff) | CSum]).

/*
subtract_cs( 
    + CSumA : coeffsum<A>, + CSumB : coeffsum<A>, - NCSum : coeffsum<A>
) is det. 

Subtraction: NCSum = CSumA - CSumB	
*/
subtract_cs( CSumA, CSumB, NCSum) :-
	zip_lm( CSumA, CSumB, ZCSum),
	subtract_x( ZCSum, NCSum).

subtract_x( [],[]).
subtract_x( [ ZPair | ZCSum] ,NCSum) :- 
    subtract_xx( ZPair, NCS1, NCSum),
	subtract_x( ZCSum, NCS1).

subtract_xx( ( Elem, Coeffs) , NCS1, NCSum) :- 
    subtract_coeffs(Coeffs,NCoeff),
    insert_coeff( NCoeff, Elem, NCS1, NCSum). 

subtract_coeffs( left(A), A).
subtract_coeffs( right(B), NB) :- negate_fr( B, NB). 
subtract_coeffs( both(A,B), D) :- subtract_fr(A,B,D).

/*
multiply_cs( 
    + CSum:coeffsum<A>, + Coeff:fraction, - NCSum:coeffsum<A>
) is det. 

NCSum is the result of multiplying CSum  by the coefficient Coeff.

Scalar product: NCSum = CSumA * Coeff
*/
multiply_cs( CSum, 1, CSum) :- !.
multiply_cs(_CSum, 0, []  ) :- !.
multiply_cs(CSum,Coeff,NCSum) :-
    % cut-implicit: Coeff \== 1, Coeff \== 0 
    multiply_x(CSum,Coeff,NCSum).

multiply_x( [] ,_Coeff, [] ).
multiply_x(  [ (E, OC) | Sum ], Coeff, [ ( E,NC) | NSum] ) :-
    % Coeff \== 0 and no value is 0, and not_zero * not_zero is not_zero 
    multiply_fr( OC, Coeff, NC), 
    multiply_x(Sum,Coeff,NSum).

/*
product_cs( 
    + A_CSum: coeffsum<A> , + B_CSum : coeffsum<B>, - Prod_CSum : coeffsum<(A,B)>
) is det.
*/
product_cs( A_Sum, B_Sum, Prod) :- 
    product_lm( A_Sum, B_Sum, Prod_Map), 
    unzip( Prod_Map, Keys, Vals), 
    unzip( Vals, AVals, BVals), 
    zip_product_frl( AVals, BVals, Coeffs), 
    zip( Keys, Coeffs, Prod).

/*
divide_cs( 
    + CSum : coeffsum<A>, + Coeff : fraction, - NCSum : coeffsum<A>
) is det.

NCSum is the result of multiplying CSum  by the inverse of Coeff.

Scalar product: NCSum = CSumA / Coeff
*/
divide_cs( CSum, Coeff, NCSum) :-
	inverse_fr(Coeff, NC), 
	multiply_cs(CSum, NC, NCSum).

/*
extract_first_coefficient(  
    + CSum : coeffsum<A>, - Coeff : fraction, - NCSum : coeffsum<A>
) is det. 

Coeff is the first coefficient in CSum , 
CSum = Coeff * NCSum.

Property: NCSum is zero or its first coefficient is 1.
*/
extract_first_coefficient_cs([], 0, []) :- !.
extract_first_coefficient_cs([Pair|CSum], Coeff, [NPair|NCSum]) :-
    Pair = ( Elem, Coeff), 
    NPair = ( Elem, 1), 
	divide_cs(CSum, Coeff, NCSum).

/*
extract_first_abs_coefficient_cs( 
    + CSum : coeffsum<A>, - Coeff : fraction, - NCSum : coeffsum<A>
) is det. 
	
Coeff is the absolute value of the first coefficient in CSum  and 

CSum = Coeff * NCSum.

Property: NCSum is zero or its first coefficient is either 1 or -1.
*/
extract_first_abs_coefficient_cs([], 0, []).
extract_first_abs_coefficient_cs( [Pair|CSum], Coeff, [NPair|NCSum]) :-
    Pair = ( Elem, C), 
	abs_fr(C, Coeff),
	sign_fr( C, S), 
	NPair = ( Elem, S), 
	divide_cs(CSum, Coeff, NCSum).

/*
extract_first_natural_numerator_cs( 
    + CSum : coeffsum<A>,  - Coeff : integer,  - NCSum : coeffsum<A>
) is det.

Coeff is the numerator of the first coefficient in CSum and 
CSum = Coeff * NCSum.

Property: NCSum is zero or its first coefficient is 
+1 or -1 or a fraction +1/D or a fraction -1/D

*/
extract_first_natural_numerator_cs( [], 0, []).
extract_first_natural_numerator_cs( [Pair|CSum], Coeff, [NPair|NCSum] ) :-
    Pair = ( Elem, C1), 
    abs_fr(C1, C2),
    numerator(C2, Coeff),
    divide_fr( C1, Coeff, NC), 
    NPair = ( Elem, NC), 
    divide_cs( CSum, Coeff, NCSum).

/*
split_cs( 
    + Sum : coeffsum<A>, - PSum : coeffsum<A>, - NSum : coeffsum<A>
) is det.

Separates CSum in two coefficients sum, PCSum and NCSum, such that
CSum = PCSum - NCSum
and all the coefficients in PCSum and NCSum are positive.
*/
split_cs( [],[],[]). 
split_cs( [ Pair|Pairs],Poss, Negs) :-
    split_x( Pair, Poss0, Negs0, Poss, Negs),
    split_cs( Pairs, Poss0, Negs0).

split_x( Pair, Poss0, Negs0, Poss, Negs) :-
    Pair = ( Elem, Coeff), 
    sign_fr( Coeff, Sign),
    abs_fr( Coeff, NCoeff), 
    NPair = ( Elem, NCoeff), 
    split_xx( Sign, NPair, Poss0, Negs0, Poss, Negs).

split_xx( 1, Pair, PSum, Negs, [Pair|PSum], Negs).
split_xx(-1, Pair, PSum, Negs, PSum, [Pair|Negs]).

/*
write_cs( + CSum : coeffsum<A>, - CSExp : term) is det. 

Exp is the representation of LinearExp without parenthesis. That will have 
the following grammar: 

CoefficientsSum<A>  ::= CoeffAddend<A> 
                    |   CoefficientsSum<A> + CoeffAddend<A>
CoeffAddend<A>  ::= Fraction * A 

*/
write_cs( [] ,0).
write_cs( [(Elem,Coeff)|CS], Exp) :- 
    write_1( Coeff, Elem, C),
    write_x( CS, C, Exp).

write_x( [], Exp, Exp).
write_x( [(Elem,Coeff)|Cs], Accm, Exp) :- 
    write_xx( Elem, Coeff, Accm, NAccm), 
    write_x( Cs, NAccm, Exp).

write_xx( Elem, Coeff, Accm, NAccm) :- 
    abs_fr( Coeff, ACoeff),
    sign_fr( Coeff, Sign),
    sign_oper( Sign, Oper),
    write_xxx( ACoeff, Elem, Monom),
    NAccm =.. [ Oper, Accm, Monom].

write_xxx( 1, Elem, Elem) :- !.
write_xxx( 1/Denom, Elem, Elem/Denom) :- !.
write_xxx( Coeff, Elem, Coeff * Elem).

sign_oper(-1, '-').
sign_oper( 1, '+').

write_1( 1, Elem,  Elem) :- !.
write_1(-1, Elem, -Elem) :- !.
write_1( 1 / Denom, Elem, Elem/Denom) :- !.
write_1( (-1) / Denom, Elem, - Elem/Denom) :- !.
write_1( Coeff, Elem, Coeff * Elem).

