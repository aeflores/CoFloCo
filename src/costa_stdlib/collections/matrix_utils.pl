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

:- module( matrix_utils,[
    get_column_mu/3,    transpose_mu/2,
    horizontal_append_mu/3, vertical_append_mu/3,
    heads_mu/2,  tails_mu/2,  heads_tails_mu/3, 
    pick_by_rows_mu/3,
    matrix_product_mu/3
]).

/** <module> 

@author Diego Alonso.
@license GPL
*/

:- use_module( list_utils).
:- use_module( stdlib(pair_list),[zip/3]).

/*
horizontal_append_mu( LeftM, RightM, AppM). 
*/
horizontal_append_mu( [], [], []). 
horizontal_append_mu( [LRow|LMat], [RRow|RMat], [NRow|NMat]) :- 
    append_lu( LRow, RRow, NRow), 
    horizontal_append_mu( LMat, RMat, NMat). 

/*

*/
vertical_append_mu( UpMat, DownMat, AppMat) :- 
    append_lu( UpMat, DownMat, AppMat). 
    
/*
get_column_mu( Mat, Num, Col) 
*/
get_column_mu( [], _Num, []).
get_column_mu( [Row|Rows], Num, [Cell|Column] ) :- 
    get_lu( Row, Num, Cell), 
    get_column_mu( Rows, Num, Column ).

/*
heads_mu( + Lists: list<list<A>>, - Heads:list<A>) is det. 

heads = map head
*/
heads_mu( [],[]).
heads_mu( [List|Lists],[Head|Heads]) :- 
    List = [Head|_Tail],
    heads_mu( Lists, Heads). 

/*
empties_mu( Lists: + list< + list<A>>) is semidet.

True if each List in Lists is an empty List. False otherwise.
*/
empties_mu( []).
empties_mu( [ [] | Ls]) :- empties_mu(Ls).

/*
tails_mu( + Lists: list<list<A>>, - Heads:list<A>) is det. 

tails = map tail
*/
tails_mu( [],[]).
tails_mu( [List|Lists], [Tail|Tails]) :- 
    List = [_Head|Tail],
    tails_mu( Lists, Tails). 

/*
heads_tails_mu( 
    + Lists: list<list<A>>, - Heads: list<A>, - Tails:list<list<A>>
) is det.
*/
heads_tails_mu( [],[],[]).
heads_tails_mu( [List|Lists],[Head|Heads],[Tail|Tails]) :- 
    List = [Head|Tail],
    heads_tails_mu( Lists, Heads, Tails).

/*
transpose_mu( + Matrix:list<list<A>>, - NMatrix:list<list<A>>) is det.

Example: 
 * transpose( [ ], [ ] ). 
 * transpose( [ [],[] ], [ ] ). 
 * transpose( [ [a,b],[c,d] ], [ [a,c],[b,d] ] ).
 
 * 
*/
transpose_mu( A,B) :- transpose_matrix(A,B). 

%% matrix transpose
%%
transpose_matrix(A,B) :-  transpose_matrix_x(A,[],B).

transpose_matrix_x([], X, X).
transpose_matrix_x([R|Rs],_,[C|Cs]) :-
	row2col(R,[C|Cs],Cols1,[],Accm),
	transpose_matrix_x(Rs,Accm,Cols1).

row2col([],[],[],A,A).
row2col([X|Xs],[[X|Ys]|Cols],[Ys|Cols1],A,B) :-
	row2col(Xs,Cols,Cols1,[[]|A],B).

/*
pick_by_rows_mu( Rows, Ices, Elems ) 


pick_by_rows_mu Matrix Ices = zipWith (!!) Ices Mat
*/
pick_by_rows_mu( [], [], []). 
pick_by_rows_mu( [Row|Rows], [Ix|Ices], Elems) :-  
    pick_by_rows_x( Ix, Row, Elems_x, Elems), 
    pick_by_rows_mu( Rows, Ices,  Elems_x).

pick_by_rows_x( 0, _List, Elems, Elems) :- !. 
pick_by_rows_x( Ix, List, Elems, [Elem|Elems]) :- get_lu( List, Ix, Elem).


/*
  matrix_product_mu(
  + AsM : list<list<A>> , + BsM: list<list<B>> , - ProdM: list<list< list<(A,B)> >>
  )  is det

  Precondition: AsM and BsM are not empty matrixes.
*/
matrix_product_mu( AsM , BsM , ProdM ) :-
    transpose_matrix( BsM , BsTm),
    matrix_product_1( AsM, BsTm, ProdM ).

% map matrix_product_2 AsM
matrix_product_1( [], _BsTm, [] ). 
matrix_product_1( [ARow|AsMat], BsTm, [ProdRow|ProdMat] ) :- 
    matrix_product_2( BsTm , ARow, ProdRow), 
    matrix_product_1( AsMat, BsTm, ProdMat ). 

% matrix_product_2 = map zip 
matrix_product_2( [], _ARow, []).
matrix_product_2( [BCol|BsTm], ARow , [ProdCell|ProdRow]) :-
    zip( ARow, BCol, ProdCell ), 
    matrix_product_2( BsTm, ARow , ProdRow). 

/*
matrix_product :: [[a]] -> [[b]] -> [[ [(a,b)] ]]
matrix_product as bs = flip map as (`prod_row` transpose bs) 
     
prod_row :: [a] -> [[b]] -> [ [(a,b)] ]  -- row in the product
prod_row xs = map (zip xs) 
*/
