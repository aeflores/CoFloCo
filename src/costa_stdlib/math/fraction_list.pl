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

:- module(fraction_list,[
    decompose_frl/3,
    numerators/2,
    denominators/2,
    negate_frl/2,
    sum_frl/2,
    product_frl/2,
    multiply_frl/3,
    divide_frl/3, 
    naturalize_frl/3,
    max_frl/2,
    min_frl/2,
    parse_frl/2, 
    filter_frl/3,
    zip_sum_frl/3,
    zip_product_frl/3
]).

/** <module> Functions and operations over lists of fractios. 

@author Diego Alonso.
@license GPL
*/

:- use_module(fraction).
:- use_module(arithmetic_utils,[lcm_list/2]).
:- use_module(stdlib(pair_list),[zip/3]).


/*
decompose_frl( 
    + Fracs:list<fraction>, - Numers:list<integer>, - Denoms:list<integer>
) is det. 

Decomposes each fraction in Fractions into its Numerator and Denominator.                
*/
decompose_frl( [], [], [] ). 
decompose_frl( [Frac|Fracs], [Numer|Numers], [Denom|Denoms] ) :- 
    decompose_fr( Frac, Numer, Denom), 
    decompose_frl( Fracs, Numers, Denoms). 

/*
numerators( + Fracs : list<fraction> , - Numers : list<integer) is det. 

Nums is the list of the numerators of Fracs. 

In functional terms, numerators = map numerator
*/
numerators( [], [] ). 
numerators( [Frac|Fracs], [Numer|Numers] ) :- 
    numerator( Frac,Numer ), 
    numerators( Fracs, Numers ). 

/*
denominators( + Fracs : list<fraction> , - Denoms : list<integer) is det. 

Denoms is the list of the denominators of Fracs. 

In functional terms, denominators = map denominators
*/
denominators( [], [] ). 
denominators( [Frac|Fracs], [Denom|Denoms] ) :- 
    denominator( Frac, Denom ), 
    denominators( Fracs, Denoms ). 

/*
  negate_frl( 
*/
negate_frl( [],[]).
negate_frl( [Fr|Frs],[NFr|NFrs]) :-
    negate_fr( Fr, NFr),
    negate_frl( Frs, NFrs). 

/*
sum_frl( + Fracs : list<fraction>, - Sum : fraction) is det.

Sum is the sum of all the fractions in Fracs.
The sum of  an empty list is the integer value zero.
*/
sum_frl( Fracs, Sum ) :- sum_frl_x( Fracs, 0, Sum).

sum_frl_x( [], S, S ).
sum_frl_x( [Frac|Fracs], Acc, Sum ) :-
    sum_fr( Acc, Frac, NAcc ),
    sum_frl_x( Fracs, NAcc, Sum ).

/*
product_frl( + Fracs : list<fraction>, - Prod : fraction) is det.

Prod is the product of all the fractions in Fracs. 
The product of an empty list is the integer value 1. 
*/
product_frl( Fracs, Prod ) :- product_frl_x( Fracs, 1, Prod ).

product_frl_x( _L, 0, 0 ) :- ! .
product_frl_x( [], Prod, Prod ).
product_frl_x( [Frac|Fracs], Acc, Prod ) :-
    multiply_fr( Frac, Acc, NAcc ), 
    product_frl_x( Fracs, NAcc, Prod ).

/*
zip_sum_frl( AFracs, BFracs, Sum_Fracs) 
*/
zip_sum_frl( AFracs, BFracs, Prod_Fracs ) :- 
    zip( AFracs, BFracs, Pairs), 
    zip_sum_x( Pairs, Prod_Fracs). 
    
zip_sum_x( [], []). 
zip_sum_x( [(A,B)|Pairs], [P|Prods]) :- 
    sum_fr( A,B,P),
    zip_sum_x( Pairs, Prods). 

/*
scalar_product_frl( AFracs, BFracs, Prod). 

*/
zip_product_frl( AFracs, BFracs, Prod_Fracs ) :- 
    zip( AFracs, BFracs, Pairs), 
    zip_product_x( Pairs, Prod_Fracs). 
    
zip_product_x( [], []). 
zip_product_x( [(A,B)|Pairs], [P|Prods]) :- 
    multiply_fr( A,B,P),
    zip_product_x( Pairs, Prods). 
	 

/*
max_frl( + Fracs : list<fraction> , - Max : fraction ) is det. 

Max is the maximum value of the list.
The predicate fails if Fracs is an empty list.
*/
max_frl( [Frac|Fracs], Max )  :- max_frl_x( Fracs, Frac, Max ).
max_frl_x( [], Max, Max ).
max_frl_x( [Frac|Fracs], Acc, Max ) :-
    max_fr( Acc, Frac, NAcc ),
    max_frl_x( Fracs, NAcc, Max ). 

/*
min_frl( + Fracs : list<fraction> , - Max : fraction) is det. 

Min is the minimum value of the list.
The predicate fails if Fracs is empty.
*/
min_frl( [Frac|Fracs], Min )  :- min_frl_x( Fracs, Frac, Min ).
min_frl_x( [], Min, Min ).
min_frl_x( [Frac|Fracs], Acc, Min ) :-
    min_fr( Acc, Frac, NAcc ),
    min_frl_x( Fracs, NAcc, Min ). 

/*
multiply_frl( 
    + Fracs : list<fraction>, + Scalar : fraction, - NFracs : list<fraction>
) is det.

NFracs is the result of multiplying each fraction of Fracs by Scalar. 
forall i: NFracs[i] = Fracs[i] * Scalar
*/
multiply_frl( Fracs, 1, Fracs) :- !. 
multiply_frl( Fracs, Scalar, NFracs) :- 
    multiply_frl_x(Fracs,Scalar, NFracs). 

multiply_frl_x( [], _Scalar, []) :- !.
multiply_frl_x( [Frac|Fracs], Scalar, [NFrac|NFracs] ) :-
    multiply_fr( Frac, Scalar, NFrac ),
    multiply_frl_x( Fracs, Scalar, NFracs ).

/*
divide_frl( 
    + Fracs : list<fraction>, + Scalar : fraction, - NFracs : list<fraction>
) is det.

NFracs is the result of dividing each fraction of Fracs by Scalar. 
forall i: NFracs[i] = Fracs[i] * Scalar
*/
divide_frl( Fracs, 1, Fracs) :- !.
divide_frl( Fracs, Scalar, NFracs) :-
    divide_frl_x(Fracs,Scalar, NFracs).

divide_frl_x( [], _Scalar, []) :- !.
divide_frl_x( [Frac|Fracs], Scalar, [NFrac|NFracs] ) :-
    divide_fr( Frac, Scalar, NFrac ),
    divide_frl_x( Fracs, Scalar, NFracs ).

/*
naturalize_frl( 
    + Fracs : list<fraction>, - Nums : list<int>, - Den : int
) is det.

Transforms a list of fractions into a list of numbers Nums and a common 
denominator Den, with the property that 
 forall i: Fracs[i] = Nums[i] / Den
*/
naturalize_frl( [], [],0).
naturalize_frl( Fracs, Nums, Den ) :- 
    denominators( Fracs, Denoms ), 
    lcm_list( Denoms, Den ), 
    multiply_frl( Fracs, Den, Nums ). 

/*
parse_frl( + Exps: list<_> , - Fracs : list<fraction> ) is det. 

Parses a list of fractions, following this grammar: 
FracList ::=    [] 
FracList ::=    [ Frac | FracList]

*/
parse_frl( [],[]).
parse_frl( [Exp|Exps], [Frac|Fracs] ) :- 
    parse_fr( Exp, Frac ), 
    parse_frl( Exps, Fracs ).

/*
filter_frl( 
    + Exps : list<term>, - Frs : list<fraction>, - Rems : list<term> 
) is det. 

*/
filter_frl( [], [], [] ).
filter_frl( [Exp|Exps], Frs, Rems ) :-
    filter_frl_x( Exp, Frs1, Rems1, Frs, Rems ), 
    filter_frl( Exps, Frs1, Rems1 ).

filter_frl_x( Exp, Frs, Rems, [Fr|Frs], Rems) :- 
    parse_fr( Exp, Fr),
    !.
filter_frl_x( Exp, Frs, Rems, Frs, [Exp|Rems]).
	
