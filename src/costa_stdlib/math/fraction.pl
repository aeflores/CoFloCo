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

:- module(fraction,[
    fraction/3,
    decompose_fr/3,
    numerator/2,
    denominator/2,
    greater_fr/2,
    geq_fr/2,
    lesser_fr/2,
    leq_fr/2,
    compare_fr/3,
    negate_fr/2,
    abs_fr/2,
    sign_fr/2,
    non_zero_fr/2,
    sum_fr/3,
    subtract_fr/3,
    multiply_fr/3,
    inverse_fr/2,
    divide_fr/3,
    power_fr/3,
    max_fr/3,
    min_fr/3,
    gcd_fr/3,
    lcm_fr/3,   
    floor_fr/2,
    ceil_fr/2,
    trunk_fr/2,
    parse_fr/2
]).

/** <module> Predicates for operating with rational numbers, defined as 
integer values or canonical fractions of integer values.

type fraction = integer | quotient 
type quotient = '/'(Num,Den) where 
 * Num:integer, Num \= 0, 
 * Den:integer, Den >= 2, 
 * gcd(Num,Den) = 1

@author Diego Alonso.
@license GPL
*/

:- use_module(arithmetic_utils,[gcd/3,	lcm/3]).
:- use_module(stdlib(list_utils),[contains_lu/2]).


/*
fraction( + Numer : int, + Denom : int, - Frac : fraction) is det. 

Frac is the fraction with numerator Num and denominator Den.
*/
fraction( _Num, 0, _Frac ) :- throw('Fraction Exception: Zero denominator').
fraction( 0, _Den, 0) :- !. 
fraction( Num, 1, Num) :- !.
fraction( Num, -1, NNum) :- !, NNum is - Num.
fraction( Num, Den, Frac) :-
    Den >= 2,
    !,
    fraction_x( Num, Den, Frac). 
fraction( Num, Den, Frac ) :-
    % Cut-implicit: Den =< -2,
    NNum is - Num,
    NDen is - Den,
    fraction_x( NNum, NDen, Frac ).

fraction_x( Num, Den, Frac) :- 
    gcd( Num, Den, Gcd), 
    NNum is Num // Gcd,
    NDen is Den // Gcd,
    fraction_xx( NNum, NDen, Frac).

fraction_xx( Num, 1, Num) :- !.
fraction_xx( Num, Den, Num/Den). 
    % Context and Cut implicit: Den >= 2.    

/*
decompose_fr( + Frac : fraction, - Numer : int , - Denom : int) is det. 

Obtains from a rational number its numerator and denominator. If the 
Fraction is an integer, then Numer is the value and Denom is 1.

Examples:
 * decompose_fr( 1/2 , Num, Den )   ?       Num = 1, Den = 2.
 * decompose_fr( 1 , Num, Den )     ?       Num = 1, Den = 1.
 * decompose_fr( -3/4 , Num, Den )  ?       Num =-3, Den = 4.
*/
decompose_fr( Numer / Denom , Numer, Denom) :- !.
decompose_fr( Frac, Frac, 1).

/*
numerator( + Frac : fraction, - Numer : int) is det. 

Numer is the numerator of the rational number Frac. 
If Frac is an integer, then the numerator is Frac itself.
*/
numerator( Frac, Numer ) :- decompose_fr( Frac, Numer, _Denom ). 
    
/*
denominator( + Frac : fraction, - Denom : int) is det. 

Den is the denominator of the rational number Frac. 
If Frac is an integer, then Denom is 1.

Property: denominator(A,D) -->  D >= 1
*/
denominator( Frac, Denom ) :-  decompose_fr( Frac, _Numer, Denom ). 

/*
greater_fr( + FracA : fraction, + FracB : fraction ) is semidet.

Returns true is FracA represents a rational number greater than FracB.
*/
greater_fr( FracA, FracB ) :- compare_fr( '>', FracA, FracB).

/*
geq_fr( + FracA : fraction, + FracB : fraction ) is semidet.

Returns true is FracA represents a rational number greater or equal than FracB.
*/
geq_fr( FracA, FracB ) :- 
    compare_fr( Comp, FracA, FracB),
    ( Comp = '=' ; Comp = '>' ), 
    !. 

/*
leq_fr( + Small : fraction, + Big : fraction ) is semidet.

Returns true is FracA represents a rational number lesser or equal than FracB.

Examples: 
 * leq_fr( 0, 1)        ?       true.
 * leq_fr( 1/2,1/3)     ?       false.
 * leq_fr( 1,1)         ?       true.
 
*/
leq_fr( Small , Big ) :- geq_fr( Big , Small ).

/*
lesser_fr( + Small : fraction, + Big : fraction) is semidet.

Returns true is FracA represents a rational number lesser to FracB.
*/
lesser_fr( FracA , FracB ) :- greater_fr( FracB , FracA ).


compare_fr( Comp, FracA, FracB) :- 
    decompose_fr( FracA, NumA, DenA),
    decompose_fr( FracB, NumB, DenB),
    N1 is NumA * DenB, 
    N2 is NumB * DenA, 
    compare( Comp, N1, N2). 
    
/*
real_value( + Frac:fraction , - Val : number) is det.

Val is the numeric value of Frac
*/
real_value(Frac,Val) :- Val is Frac.

/*
negate_fr( + Frac : fraction, - Negate : frac) is det. 

NFrac is the opposite fraction of Frac.
<LaTeX> NF = - F </LaTeX>
*/
negate_fr( Frac , Negate ) :-
	decompose_fr( Frac, Num, Den),
	NNum is -Num,
	fraction( NNum, Den, Negate ).

/*
abs_fr( + Frac : fraction, - Abs : fraction ) is det. 

NFrac is the absolute value of Frac
*/
abs_fr( Frac, Abs ) :-
    decompose_fr( Frac, Num, Den ),
	NNum is abs(Num),
	fraction( NNum, Den, Abs ).

/*
sign_fr( + Frac : fraction, - Sign : int) is det. 

Sign is the sign value of Frac, which is 
 * -1 if Frac < 0
 * 0 if Frac = 0 
 * 1 if Frac > 0 ,

Examples: 
 * sign( -1/2, S)       ?   S = -1.
 * sign( 0, S)          ?   S = 0.
 * sign( 2, S)          ?   S = 1.
*/
sign_fr( Frac, Sign ) :-
	numerator( Frac, Num ),
	Sign is sign(Num).

/*
non_zero_fr( + Frac : fraction, - Res:{0|1} ) is det.
*/
non_zero_fr( 0, 0) :- !. 
non_zero_fr(_F, 1). 

/*
sum_fr( + FracA : fraction, + FracB : fraction, - Sum : fraction)  is det.

Sum = FracA + FracB. 
*/
sum_fr( FracA, FracB, Sum) :-
    decompose_fr( FracA, NumA, DenA),
    decompose_fr( FracB, NumB, DenB),
    NNum is NumA * DenB + NumB * DenA ,
    NDen is DenA * DenB,
	fraction( NNum, NDen, Sum).

/*
subtract_fr( + FracA : fraction, + FracB : fraction, - Diff : fraction)  is det.

Diff = FracA - FracB.
*/
subtract_fr( FracA, FracB, Diff ) :-
    decompose_fr( FracA, NumA, DenA ),
    decompose_fr( FracB, NumB, DenB ),
    NNum is NumA * DenB - NumB * DenA ,
    NDen is DenA * DenB,
	fraction( NNum, NDen, Diff ).

/*
multiply_fr( + FracA : fraction, + FracB : fraction, - Prod : fraction) is det.

NFrac = FracA * FracB
*/
multiply_fr( FracA, FracB, Prod) :-
    decompose_fr( FracA, NumA, DenA),
    decompose_fr( FracB, NumB, DenB), 
    NNum is NumA * NumB, 
    NDen is DenA * DenB, 
	fraction( NNum, NDen, Prod).

/*
divide_fr( + FracA : fraction, + FracB : fraction, - Quot : fraction)  is det.

<LaTeX>
NFrac = \frac{FracA}{FracB} .
</LaTeX>
*/
divide_fr( FracA, FracB, Quot) :-
	FracB \== 0, 
    decompose_fr( FracA, NumA, DenA),
    decompose_fr( FracB, NumB, DenB), 
    NNum is NumA * DenB, 
    NDen is DenA * NumB, 
	fraction( NNum, NDen, Quot ).

/*
inverse_fr( + Frac : fraction, - Invers : fraction ) is det. 

<LaTeX> NFrac = Frac ^{-1} </LaTeX>
*/
inverse_fr( Frac, Invers ) :-
	Frac \== 0,
	decompose_fr( Frac, Num, Den ),
	fraction( Den, Num, Invers ).

/*
max_fr( + FracA : fraction, + FracB : fraction, - Max : fraction ) is det.

*/
max_fr( Frac, Frac, Frac) :- !.
max_fr( FracA, FracB, FracA) :-  greater_fr( FracA, FracB), !. 
max_fr( FracA, FracB, FracB) :-  lesser_fr( FracA, FracB), !. 

/*
min_fr( + FracA : fraction, + FracB : fraction, - Min : fraction ) is det.

*/
min_fr( Frac, Frac, Frac) :- !.
min_fr( FracA, FracB, FracA) :-  lesser_fr( FracA, FracB), !. 
min_fr( FracA, FracB, FracB) :-  greater_fr( FracA, FracB), !. 

/*
gcd_fr( + FracA : fraction , + FracB : fraction , - Gcd : fraction ) is det. 

*/
gcd_fr( FracA, FracB, Gcd ) :- 
    decompose_fr( FracA, NumA, DenA ),
    decompose_fr( FracB, NumB, DenB ), 
    gcd( NumA, NumB, GNum ),
    gcd( DenA, DenB, GDen ),
    fraction( GNum, GDen, Gcd ).

/*
lcm_fr( + FracA : fraction , + FracB : fraction , - Lcm: fraction ) is det. 

*/
lcm_fr( FracA, FracB, Lcm) :- 
    decompose_fr( FracA, NumA, DenA ),
    decompose_fr( FracB, NumB, DenB ), 
    lcm( NumA, NumB, LNum ), 
    lcm( DenA, DenB, LDen ), 
    fraction( LNum, LDen, Lcm ). 

/*
power_fr( + Base : fraction , + Expon : integer, - Power : fraction) is det. 

*/
power_fr( 0, _, 0) :- !. 
power_fr( _Base,0, 1 ) :- !. 
power_fr( Base, 1, Base ) :- !.
power_fr( Base, Expon, Power ) :-
    decompose_fr( Base, Numer, Denom), 
    AExp is abs(Expon),     
    NumPow is round( Numer ** AExp ),
    DenPow is round( Denom ** AExp ), 
    compare( Comp, 0, Expon), 
    power_x( Comp, NumPow, DenPow, PNum, PDen), 
    fraction( PNum, PDen, Power).

power_x( '<', NumPow, DenPow, NumPow, DenPow ). 
power_x( '>', NumPow, DenPow, DenPow, NumPow ).

/*
floor_fr( + Frac : fraction , - Floor : int ) is det.

Floor is the floor of Frac, that is to say Floor is the maximum int value such
that Floor =< Frac. 
*/
floor_fr( Numer / Denom, Floor) :- 
    !,
    F1 is Numer // Denom, 
    floor_x( F1, Numer, Floor). 
floor_fr( Frac, Frac).
    % Cut-implicit: Frac is an integer 
    
floor_x( Floor, Numer, Floor ) :- 
    Numer > 0,
    !.
floor_x( F, _Numer, Floor ) :- 
    % Cut - Implicit:     Numer > 0, 
    Floor is F - 1. 

/*
ceil_fr( + Frac : fraction , - Ceil : int) is det. 

Ceil is the ceiling of Frac, that is to say Ceil is the minimal integet I 
such that Frac =< Ceil.
*/
ceil_fr( Numer/Denom, Ceil ) :- 
    !, 
    C is Numer // Denom, 
    ceil_x( Numer, C, Ceil ). 
ceil_fr( Frac, Frac ). 
    
ceil_x( Numer, Ceil, Ceil ) :- 
    Numer < 0,
    !.
ceil_x( _Numer, C, Ceil ) :- 
    % Cut-implicit: Numer > 0, 
    Ceil is C + 1.     

/*
trunk_fr( + Frac : fraction, - Trunk : integer )  is det. 

Trunk is the maximum integer positive value such that Trunk =< abs(Frac). 
*/
trunk_fr( Numer/Denom, Trunk ) :- 
    !, 
    Trunk is Numer // Denom.
trunk_fr( Frac, Frac ). 

/*
parse_fr( + Exp : expression, - Frac : fraction ) is det.

Fraction is the canonical fraction obtained after parsing Exp, which is an 
arithmetic expression following this grammar: 

Fraction::= integer
	|	+ Fraction              |	- Fraction             |   abs(Fraction)
	|	Fraction  + Fraction	|	Fraction - Fraction 
	|	Fraction * Fraction		|	Fraction / Fraction
    |   Fraction ** Integer 
*/
parse_fr( Exp, Frac) :-
	parse_x( Exp, Num, Den ), 
	fraction( Num, Den, Frac ).

% Design pattern: immersion with synthetized attributes.

% Rule: Fraction ::= integer
parse_x( Exp, Exp, 1) :-
	integer(Exp),
	!.
% Rule: Fraction ::= + Fraction | - Fraction  | abs(Fraction) 
parse_x( Exp, Num, Den ) :-
    compound( Exp ),
    Exp =.. [F, Exp1], 
    contains_lu( [ '+' , '-' , abs ], F), 
    !,
    parse_x( Exp1, Num1, Den), 
    NumE =.. [F,Num1], 
    Num is NumE.
% Rules: Frac ::= Frac ** Int 
parse_x( Exp, Num, Den ) :-
    compound( Exp ),
    Exp = Base ** Expon,
    !,
    integer( Expon ),
    parse_x( Base, Num1, Den1),
    parse_x3( Expon, Num1, Den1, Num, Den ).
% Rules: Frac ::= Frac + Frac | Frac - Frac | Frac*Frac | Frac / Frac 
parse_x( Exp, Num, Den ) :-
	compound( Exp ),
	Exp =.. [F , Exp1 , Exp2],
	!,
	% Not really necessary: mere matter of eficiency. 
	contains_lu( [ '+','-','*','/',max,min], F), 
	parse_x( Exp1, Num1, Den1),
	parse_x( Exp2, Num2, Den2),
	parse_x2( F, Num1, Num2, Den1, Den2, Num, Den ).
% Rule: Fraction ::= Fraction + Fraction
parse_x2( '+', Num1, Num2, Den1, Den2, Num, Den ) :-
    Num is Num1 * Den2 + Den1 * Num2, 
    Den is Den1 * Den2.
% Rule: Fraction ::= Fraction - Fraction
parse_x2( '-', Num1, Num2, Den1, Den2, Num, Den ) :-
    Num is Num1 * Den2 - Num2 * Den1 ,
    Den is Den1 * Den2.
% Rule: Fraction ::= Fraction * Fraction
parse_x2( '*', Num1, Num2, Den1, Den2, Num, Den ) :-
    Num is Num1 * Num2,
    Den is Den1 * Den2.
% Rule: Fraction ::= Fraction / Fraction
parse_x2( '/', Num1, Num2, Den1, Den2, Num, Den ) :-
    Num is Num1 * Den2,
    Den is Num2 * Den1.
% Rule: Fraction ::= max(Fraction,Fraction).
parse_x2( max, NumA, NumB, DenA, DenB, Num, Den ) :-
    N1 is NumA * DenB, 
    N2 is NumB * DenA, 
    ( N1 >= N2 
    ->  Num = NumA, Den = DenA
    ;   Num = NumB, Den = DenB
    ).
% Rule: Fraction ::= min(Fraction,Fraction).
parse_x2( min, NumA, NumB, DenA, DenB, Num, Den ) :-
    N1 is NumA * DenB, 
    N2 is NumB * DenA, 
    ( N1 =< N2 
    ->  Num = NumA, Den = DenA
    ;   Num = NumB, Den = DenB
    ).

parse_x3( 0, _Num1, _Den1, 1, 1 ) :- !.
parse_x3( 1, Num, Den, Num, Den ) :- !.
parse_x3( -1, Num, Den, Den, Num ) :- !.
parse_x3( Exp, Num1, Den1, Num, Den ) :-
    Exp > 0,
    !,
    Num is round( Num1 ** Exp ),
    Den is round( Den1 ** Exp ).
parse_x3( Exp, Num1, Den1, Num, Den) :-
    Exp < 0,
    !,
    AExp is abs( Exp ),
    Den is round( Num1 ** AExp ),
    Num is round( Den1 ** AExp ).
