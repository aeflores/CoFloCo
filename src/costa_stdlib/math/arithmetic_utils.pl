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

:- module(arithmetic_utils,[
	max/3,
	min/3,
	max_list/2,
	min_list/2,
	sum_list/2,
	product_list/2,
	increment/3,
	increment_step/4,
	decrement/3,
	decrement_step/4,
	divides/2,
	gcd/3,
	lcm/3,
	gcd_list/2,
	lcm_list/2,
	log_base/3,
	divisor/2,
	divisor_lesser_than/3,
	maximal_divisor/3, 
	polinomial_decomposition/3,
    exact_divide_list/3,
    divide_list/3
]).

/** <module> Arithmetic predicates and functions for numbers and lists of
numbers. These predicates are tailored for being used in with integer values, 
but some of the predicates also work with floating point values, or even with
arguments of mixed-type.

@author Diego Alonso
@license GPL
*/

/*
max( +A:number,+B:number,-Max:number) is det. 
max( +A:int,   +B:int,   -Max:int   ) is det. 

Max is the maximum value of A and B, which means that one of these holds: 
 * A >= B, Max = A. 
 * B >= A, Max = B. 

The max operation has the following properties:
 * Commutative: max(A,B,C) <--> max (B,A,C).
 * Associative: max(A,B,D),max(D1,C,E) <--> max(B,C,D2),max(A,D2,E).

Examples:
 * max(0,1,Max)     ?       Max = 1. 
 * max(0,-1,Max)    ?       Max = 0.    
*/
max(A,B,A) :- A >= B, !.
max(A,B,B) :- A < B, !.

/*
min( +A:number,+B:number,-Max:number) is det. 
min( +A:int,   +B:int,   -Max:int   ) is det. 

Min is the minimum value of A and B, which means that one of these holds: 
 * B >= A, Min = A. 
 * A >= B, Min = B. 

The min operation has the following properties:
 * Commutative: min(A,B,M) <==> min(B,A,M).
 * Associative: min(A,B,D),min(D1,C,E) <==> min(B,C,D2),min(A,D2,E).

Examples:
 * max(0, 1,Max) ?  Max = 1. 
 * max(0,-1,Max) ?  Max = 0.    

*/
min(A,B,A) :- A =< B, !.
min(A,B,B) :- A > B, !.

/*
max_list( + Nums: non_empty list<number>, -Max:number) is det. 
max_list( + Nums: non_empty list<int>   , -Max:int) is det. 
 
Max is the maximum of the numbers of the list.

The max_list operation has the following properties: 
 * Commutative: max_list(L, M), permutation(L,P) => max_list(P,M). 
 * Projective:  max_list(L,M) => element(L,M).

Examples: 
 * max_list( [1,2,3] , X)  ?    X = 3. 
 * max_list( [0,-1] , X)  ?    X = 0. 
*/
max_list(  [ Num | Nums] ,Max) :- max_list_x(Nums,Num,Max).

max_list_x([],Max,Max).
max_list_x([N|Ns],Num,Max) :-
    max(N,Num,NNum),
    max_list_x(Ns,NNum,Max).

/*
min_list( + Nums: non_empty list<number>, -Min:number) is det. 
min_list( + Nums: non_empty list<int>   , -Min:int) is det. 

Min is the minimum value of the numbers of the list.

The min_list operation has the following properties: 
 * Commutative: min_list(L, M), permutation(L,P) => min_list(P,M). 
 * Projective:  min_list(L,M) => element(L,M).

Examples: 
 * min_list( [1,2,3] , X)  ?    X = 1. 
 * min_list( [0,-1] , X)  ?    X = -1. 

*/
min_list( [ Num | NNums] ,Min) :- min_list_x(NNums,Num,Min).

min_list_x([],Min,Min).
min_list_x([N|Ns],Num,Min) :-
	min(N,Num,NNum) , 
	min_list_x(Ns,NNum,Min).

/*
sum_list( + Nums: list<number>, -Sum:number) is det. 
sum_list( + Nums: list<int>, -Sum:int) is det. 

Sum is the sum of all the numbers of the list Nums.

Examples:
 * sum_list( [], S)      ?       S = 0.
 * sum_list( [1,2,3], S) ?       S = 6.
 * sum_list( [-1,2] , S) ?       S = 1.

*/
sum_list(Nums,Sum) :- sum_list_x(Nums,0,Sum).

sum_list_x([],Sum,Sum):-!.
sum_list_x([Num|Nums],Accum,Sum):-
    NAccum is Accum + Num,
    sum_list_x(Nums,NAccum,Sum).

/*
product_list( + Nums: list<number>, -Max:number) is det. 
product_list( + Nums: list<int>, -Max:int) is det. 

Prod is the product of all the numbers in the list Nums. 

Examples:
 * product_list( [], S)      ?      S = 1.
 * product_list( [1,2,3], S) ?      S = 6.
 * product_list( [-1,2] , S) ?      S = -2.
 * product_list( [0,3,2], S) ?      S = 0.
*/
product_list(Nums, Prod) :- product_list_x(Nums, 1, Prod).

product_list_x([],Sum,Sum):- !.
product_list_x( _Nums,Accum,0):- Accum =:= 0, !.
product_list_x([Num|Nums],Accum,Prod):-
	% implicit: Accum =\= 0, 
	NAccum is Accum * Num,
	product_list_x(Nums,NAccum,Prod).

/*
increment( + From:int , +To:int , - Val:int) is nondet.

Returns in Val, in an increasing order, all integer values Val such that 
From =< Val =< To. If To < From, then the predicate fails. 

Examples: 
 * increment(0,4,X)     ?       X = 0 ; X=1 ; X=2 ; X=3; X=4. 
 * increment(0,0,X)     ?       X = 0. 
 * increment(0,-1,X)    ?       false.
*/
increment(From , To, Val) :- increment_step(From, To, 1, Val). 

/*
increment_step( +From:int , +To:int, +Step:int, -Val:int) is det.

Gives in val, in an increasing order, all integer values Val such that 
From =< Val =< To , Val = From + N * Step for some N >= 0.

If To > From, then the predicate fails. 

Examples: 
 * increment_step(0,3,2,X) ?            X = 0 ; X = 2.
 * increment_step(0,4,2,X) ?            X = 0 ; X = 2 ; X = 4.
 * increment_step(0,5,2,X) ?            X = 0 ; X = 2 ; X = 4. 
*/
increment_step(From, To, _Step, From) :- From =< To.	
increment_step(From , To, Step , Val) :-
	NFrom is From + Step, 
	NFrom =< To,
	increment_step(NFrom, To, Step, Val).

/*
decrement( +From:int , +To:int, -Val:int) is nondet.

Returns in Val, in a decreasing order, all integer values Val such that 
From >= Val >= To. 
If To > From, then the predicate fails. 
*/
decrement(From , To, Val) :- decrement_step(From, To, 1, Val). 

/*
decrement_step(+From:int,+To:int,+Step:int,-Val:int) is nondet.

Returns in Val, in a decreasing order, all values Val such that 
From >= Val >= To  and Val = From - N* Step for some N >= 0.
If To > From, then the predicate fails. 

*/
decrement_step(From, To, _Step, From) :- From >= To.
	
decrement_step(From , To, Step , Val) :-
	Step >= 1, 
	NFrom is From - Step, 
	NFrom >= To, 
	decrement_step(NFrom, To, Step, Val).

/*
log_base( +Base:number , +Exp:number, -Log:number) is det.

Log is the logarithm with respect to Base of Exp. 

Preconditions: Base > 1.0, Exp > 0.  
 
Examples: 
 * log( 2.0,1.0,L) ?        L = 0.0. 
 * log( 2.0,4.0,L) ?        L = 2.0. 
*/
log_base(Base,Exp,Log) :- Log is log(Exp) / log(Base).

/*
gcd( +A:int, +B:int, -Gcd:int) is det.

Gcd is the greatest common divisor of X,Y. More formally, 
if A = 0, B = 0 then Gcd = 0 else Gcd is the greatest integer such that
G >= 1, divides(G,A), divides(G,B). 

Examples: 
 * gcd( 3,4,X)  ?       X = 1. 
 * gcd( 3,0,X)  ?       X = 3. 
 * gcd( 0,0,X)  ?       X = 0.
 
Properties of the gcd operation: 
 * Commotative:         gcd(A,B,G) <==> gcd(B,A,G). 
 * Asociative:          gcd(A,B,G1),gcd(G1,C,G) <==> gcd(B,C,G2),gcd(A,G2,G). 
 * Neutral element:     gcd(A,0,A).
*/
gcd(X,Y,G) :-
	X_x is abs(X),
	Y_x is abs(Y),
    gcd_x(X_x,Y_x,G).

gcd_x(X,X,X) :- !.
gcd_x(0,Y,Y) :- !.
gcd_x(X,0,X) :- !.

gcd_x(X,Y,Z) :- 
    ( X > Y 
    ->  NX = Y, NY is X mod Y 
    ;   NX = X, NY is Y mod X
    ), 
	gcd_x(NX,NY,Z).

/*
lcm( +A:int, +B:int, -Lcm:int) is det.

L is the least common multiple of A and B. That is to say, 
 * If A=0 or B=0 then Lcm=0, else Lcm is the smallest integer such that
   Lcm >= 1, divides(A,Lcm), divides(B,Lcm). 

Properties of the lcm operation: 
 * Commotative:         lcm(A,B,L) <==> lcm(B,A,L). 
 * Asociative:          lcm(A,B,G1),lcm(G1,C,G) <==> lcm(B,C,G2),lcm(A,G2,G). 
 * Neutral element:     lcm(A,0,A).

*/
lcm(0,_B,0) :- !.
lcm(_A,0,0) :- !.
	
lcm(A,B,L) :- 
	% Implicit by cut: A \== 0,	B \== 0, 
	NA is abs(A),
	NB is abs(B),
	gcd_x(NA,NB,G),
	L is NA * NB // G.

/*
gcd_list( +Nums:list<int>, -Gcd:int) is det.

Gcd is the Greatest common divisor of all numbers in the list Nums. 
The gcd of an empty list is zero.
*/
gcd_list( [],0).
gcd_list( [Num|Nums], Gcd) :- gcd_list_x(Nums,Num,Gcd). 

gcd_list_x([],Gcd,Gcd).
gcd_list_x([_|_],1,1) :- !. % One is an atractor. 
gcd_list_x([Num|Nums],Gcd1,Gcd) :- 
    gcd(Num,Gcd1,Gcd2), 
    gcd_list_x(Nums,Gcd2,Gcd). 

/*
lcm_list(  + Nums:list<int>, - Lcm: int) is det.

Lcm is the least common multiple of all the numbers in the list Nums.
The lcm of an empty list is one. 
*/	
lcm_list( [],1).
lcm_list( [Num|Nums], Lcm) :- lcm_list_x(Nums,Num,Lcm).

lcm_list_x([],Lcm,Lcm) :- !.
lcm_list_x(_Nums,0,0) :- !.
lcm_list_x([Num|Nums],Lcm1,Lcm) :-
    lcm(Num,Lcm1,Lcm2), 
    lcm_list_x(Nums,Lcm2,Lcm). 

/*
divides( +A:int,+B:int) is semidet.

True if A divides B. A number X divides the number Y if there exist some 
number C such that B = A*C. 

Under this definition, 0 is divisable from any integer value, including zero. 

*/
divides(_A,0) :- !.
divides(A,B) :- 
    B =\= 0,
    A =\= 0,
    B mod A =:= 0.

/*
divisor ( + Number:integer, - Divisor:integer)  is nondet. 

This predicate gives, in a decreasing order, all natural numbers N such that 
1 =< N =< abs(Number) && divides(N,Number).

Examples: 
 * divisor(0,D) ?      false. 
 * divisor(1,D) ?      D = 1. 
 * divisor(2,D) ?      D = 2 ; D = 1. 
 * divisor(6,D) ?      D = 6 ; D = 3 ; D = 2 ; D = 1.
*/
divisor(Number, Divisor) :- 
	NNum is abs(Number), 
	decrement(NNum, 1, Divisor),
	divides(Divisor, Number).

/*
divisor_lesser_than( +Number:int, +Max:int, -Divisor:int) is nondet.

Returns in Divisor all Natural Numbers between 1 and Max that divide Number.
If Number is Zero, the predicate fails.
*/
divisor_lesser_than(Number, Max, Divisor) :-
    NMax is abs(Max), 
    decrement(NMax, 1, Divisor),
    divides(Divisor, Number).

/*
common_divisor( +NumA:int, +NumB:int, -Div:int) is nondet.

Returns in Div all numbers that are common divisors of NumA and NumB. 
*/
common_divisor(NumA,NumB,Div) :- 
    gcd(NumA,NumB,Gcd),
    divisor(Gcd,Div).

/*
maximal_divisor( +Number:int, +Max:int, -Divisor:int) is nondet.

Preconditions : Number >= 0 , Max >= 0 

Returns in Divisor all the maximal divisors of Number smaller or equal to Max.
The meaning of maximal divisors means that, for the given Number and Max,
if A and B are two answers of the predicate then they hold that : 
 * They are divisors of Number:
 * A =< Max, B =< Max.
 * Neither A divides B nor B divides A.

Examples:
 * maximal_divisor( 1 , 1, X) ?     X = 1.
 * maximal_divisor( 2 , 1, X) ?     X = 1.
 * maximal_divisor( 3 , 2, X) ?     X = 1. 
 * maximal_divisor( 4 , 3, X) ?     X = 2. 
 * maximal_divisor( 4 , 2, X) ?     X = 2. 
 * maximal_divisor( 12 ,5, X) ?     X = 4 ; X = 3. 


*/
maximal_divisor(Num,Max,Div) :-  maxdivisor_x(Num,Max,[],Div).

maxdivisor_x(Number,I,Divs,Div) :- 
    ( divides(I,Number),
     \+ divides_any(Divs,I)  
        ->  S = yes 
        ;   S = no 
    ),
    (   S = yes, 
        Div = I
    ;   I >= 1,
        NI is I - 1,
        ( S = yes 
        ->  NDivs = [I|Divs]
        ;   NDivs = Divs), 
        maxdivisor_x( Number, NI, NDivs, Div)
    ).


divides_any([Div|Divs],Num) :- divides(Num,Div), ! ; divides_any(Divs,Num).


/*
polinomial_decomposition( + Number: int, + Base:int , - Code:list<int>) is det. 

Obtains the polinomial decomposition of Number in the Base. 

Preconditions: Number >= 0, Base >= 2, 
*/
polinomial_decomposition( 0, _Base, []) :- !.
polinomial_decomposition( Number, Base, [ Code | Codes] ) :-
    % Implicit by precondition, cut: Number >= 1,
    Code is Number mod Base,
    NNum is Number //  Base,
    polinomial_decomposition(NNum, Base, Codes).


/*
knapshack( 
    + Weights : list<int> , Max : int , - Knapshack : list<int> 
) is nondet. 

For non-negative weights, generates all knapshacks such that 
Knapshack · Weight =< Max
*/
knapshack( [], _Max , [] ). 
knapshack( [W|Ws], Max, [K|Ks] ) :- 
    knapshack_x( W, Max, K, Max1),
    knapshack( Ws, Max1, Ks). 

knapshack_x( 0, Max, 0, Max) :- !. 
knapshack_x( W, Max, 0, Max) :- W > Max, !. 
knapshack_x( W, Max, K, NMax ) :- 
    MaxK is Max // W, 
    increment( 0, MaxK, K), 
    NMax is Max - W * K. 

/*
divide_number_list( + Weights, + Num, - Maxes ) 

divide_number_list Ws Num = map ( Num / ) ws
*/
divide_number_list( [], _Num , [] ). 
divide_number_list( [W|Ws], Num, [M|Ms] ) :- 
    divide_number_list_x( W, Num, M), 
    divide_number_list( Ws, Num, Ms ). 

divide_number_list_x( 0, _Num, 0) :- !. 
divide_number_list_x( W, Num, 0) :- W > Num, !. 
divide_number_list_x( W, Num, M) :- M is Num // W. 

/*
exact_divide_list( Nums, Divisor, Quots ) 
*/
exact_divide_list( Nums, 1, Nums ) :- !.
exact_divide_list( [], _Divisor, [] ).
exact_divide_list( [Num|Nums], Divisor, [Quot|Quots] ) :- 
    exact_divide( Num, Divisor, Quot ), 
    exact_divide_list( Nums, Divisor, Quots ).

exact_divide( Num, Div, Quot ) :- 
    Num rem Div =:= 0, 
    Quot is Num // Div.    

/*
divide_list
*/
divide_list( Nums, 1, Nums ) :- !.
divide_list( [], _Divisor, [] ).
divide_list( [Num|Nums], Divisor, [Quot|Quots] ) :- 
    divide_x( Num, Divisor, Quot ), 
    divide_list( Nums, Divisor, Quots ).

divide_x( Num, Div, Quot ) :-  Quot is Num // Div.    
