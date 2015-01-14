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

:- module(matrix_constraint,[
    decompose_mrep/4,
    mrep_to_constraints/3,
    constraints_to_mrep/4,
    from_constraints_mrep/4,
    get_entailment_cone_mrep/3,
    constraints_entailed_cone/5
]).

/** <module>

  A Matrix Constraint System, or rather the matrix representation of a
  linear constraint system, is one of the following:
  
  mrep(NVars, AsM      =< Bs)        % leq 
  mrep(NVars, AsM      >= Bs)        % geq
  mrep(NVars, AsM + Bs =< 0 )        % leq_plus
  mrep(NVars, AsM + Bs >= 0 )        % geq_plus

  gives the matrix representation of a conjunction of M (hidden) linear constraints:

  * N is the number of variables
  * A is a M * N matrix (implicit length)
  * B is a M*1 list of constants  

  The matrix representation is independent of the chosen set of N variables X,
  2*X+Y-Z+1 >= 0 is almost the same as 2*A+B-C+1 >= 0

  The four possible mrep meanings are called 
  @author XXXX 
*/

:- use_module(stdlib(utils),[ut_length/2]).
:- use_module(stdlib(list_utils),[length_lu/2]).
:- use_module(stdlib(pair_list),[zip/3]). 
:- use_module(stdlib(matrix_utils),[matrix_product_mu/3]). 
:- use_module(stdlib(parsing_writing),[write_sum/2,write_biproduct/3]).
:- use_module(stdlib(fraction),[multiply_fr/3]).
:- use_module(stdlib(fraction_list), [
    naturalize_frl/3,negate_frl/2,multiply_frl/3,divide_frl/3]).
:- use_module(stdlib(coefficients_sum),[coeffs_cs/3]).
:- use_module(stdlib(linear_expression), [parse_le/2]).
:- use_module(stdlib(linear_constraint_system)).
:- use_module(stdlib(numvars_util),[to_numbervars_nu/4]).
%:- use_module(pubs(pubs_constraints_utilities)).


decompose_mrep( A+B >= 0, geq_plus, A, B) :- !.
decompose_mrep( A+B =< 0, leq_plus, A, B) :- !.
decompose_mrep( A   >= B, geq, A, B). 
decompose_mrep( A   =< B, leq, A, B). 


%%
%   mrep_to_constraints
% 
mrep_to_constraints(mrep(N, MCs),Vs,Cs) :-
    ut_length( Vs, N), 
    decompose_mrep( MCs, Mode, A, B), 
	matrix_to_constraints(A,B,Mode,Vs,Cs).

matrix_to_constraints([],[],_Mode,_Vs,[]).
matrix_to_constraints([Row|Rows],[B|Bs],Mode,Vs,[C|Cs]) :-
    row_to_constraint(Row,B,Mode,Vs, C), 
	matrix_to_constraints(Rows,Bs,Mode,Vs,Cs).

row_to_constraint( Row, B, Mode,Vs, Cstr ) :-
    naturalize_frl( [B|Row] , [NB| NRow], _ ),
    write_biproduct( NRow, Vs, E),
    row_to_constraint_x( Mode, E, NB, Cstr).

row_to_constraint_x( leq, E, B, E =< B).
row_to_constraint_x( geq, E, B, E >= B).
row_to_constraint_x( leq_plus, E, B, E + B =< 0).
row_to_constraint_x( geq_plus, E, B, E + B >= 0).


%%
%  constraints_to_mrep
%
%  Note : this predicate assumes all constraints in the (A*X $ b) form,
%  with the constant at a different side. 
%
constraints_to_mrep(PPL_Cs,N,Vs,Cs) :-
	constraints_to_rows(PPL_Cs,Vs,A,B),
	Cs = mrep(N,A =< B).

constraints_to_rows([],_,[],[]).
constraints_to_rows([C|Cs],Vs,HRs,HBs) :-
	constraint_to_row(C,Vs,HRs-TRs1,HBs-TBs1),
	constraints_to_rows(Cs,Vs,TRs1,TBs1).

constraint_to_row(C,Vs,HRows-TRows,HBs-TBs) :-
    C =.. [Op, E, B],
    lexp_to_vars_coeffs( E, Vs, Row_x),
	constraint_to_row_1(Op, Row_x, B, HRows-TRows,HBs-TBs).

constraint_to_row_1( =< , Row, B, [Row|TRs]-TRs,[B|TBs]-TBs).
constraint_to_row_1( >= , Row, B, [NRow|TRs]-TRs,[NB|TBs]-TBs) :-
    NB is - 1* B,
    multiply_frl( Row, -1, NRow). 
constraint_to_row_1( =  , Row, B, [Row,NRow|TRs]-TRs,[B,NB|TBs]-TBs) :-
    NB is - 1* B,
    multiply_frl( Row, -1, NRow). 

lexp_to_vars_coeffs( E, Vs, Ps) :-
    parse_le( E, Cs+0),
    coeffs_cs( Cs, Vs,Ps).

/*
*/
from_constraints_mrep( Cs, Vs, Mode, MRep) :- 
    parse_lcs( Cs, Lcs),
    % no need to be leq_plus: others work fine
    from_lcs_mrep( Lcs, Vs, Mode, MRep). 

/*
  matrix_rep_lcs( + Lcs:, + Elems , + Mat_Mode, - MRep ) si det. 

  converts the Lcs into the matrix representation
 
  mrep( N, AsM, Bs), of the implicit inequalities. 

  AsM * Elems =< Bs

*/
from_lcs_mrep( Lcs, Elems, Mode, MRep) :- matrix_rep_x( Mode, Lcs, Elems, MRep).

matrix_rep_x( leq_plus, Lcs, Elems,  MRep) :-
    to_geqs_lcs( Lcs, Leqs), 
    coeffs_matrices_lcs(Leqs,  Elems, AsM, Bs),
    length_lu( Elems, N),
    MRep = mrep( N, AsM + Bs =< 0).
matrix_rep_x( geq_plus , Lcs, Elems, MRep) :-
    to_geqs_lcs( Lcs, Leqs), 
    coeffs_matrices_lcs(Leqs,  Elems, AsM, Bs),
    length_lu( Elems, N),
    MRep = mrep( N, AsM + Bs >= 0).
matrix_rep_x( leq, Lcs, Elems, MRep) :-
    to_leqs_lcs( Lcs, Leqs), 
    coeffs_matrices_lcs(Leqs,  Elems, AsM, Bs_x),
    negate_frl( Bs_x , Bs),
    length_lu( Elems, N),
    MRep = mrep( N, AsM =< Bs).
matrix_rep_x( geq, Lcs, Elems, MRep) :-
    to_geqs_lcs( Lcs, Leqs), 
    coeffs_matrices_lcs(Leqs,  Elems, AsM, Bs_x),
    negate_frl( Bs_x , Bs),
    length_lu( Elems, N),
    MRep = mrep( N, AsM >= Bs).


/*
  
*/
get_entailment_cone_mrep( MRep, Params, Psi) :- 
    MRep = mrep( N, MCs), 
    ut_length( Coeffs, N),
    Params = [Const|Coeffs],
    decompose_mrep( MCs, Mode, AsM, Bs),
    ut_length( AsM ,M),
    ut_length( Bs  ,M),
    ut_length( Lambda, M),
    map_oper_const( Lambda, >=, 0, Psi - Psi_1 ),
    % Lambda[1,M] * AsM[M,N] = Cs[1,N]
    matrix_product_mu( [Lambda], AsM , LamProdAs),   
    prodmat_to_lexps( LamProdAs, [LExps_Coeffs] ),
    zip_equals( Coeffs, LExps_Coeffs, Psi_1 - Psi_2 ),   
    % Lambda[1,M] * Bs[M,1] + Mu[1,1] = D[1,1]
    zip( Lambda, Bs, LamProdBs),
    prodcell_to_lexp( LamProdBs, LExp_Const),
    % Const = Mu + LExp_Const , Mu >= 0   <===>  Const >= LExp_Const
    const_entailed_constraint( Mode, Const, LExp_Const, Const_Cs), 
    Psi_2 = [Const_Cs ].
    % AND NOW, TO PROJECT PSI ONTO CONST, COEFFS. 

const_entailed_constraint( geq_plus, Const, LConst, Const >= LConst).
const_entailed_constraint( leq_plus, Const, LConst, Const =< LConst).
const_entailed_constraint( geq, Const, LConst, Const =< LConst).
const_entailed_constraint( leq, Const, LConst, Const >= LConst).


prodmat_to_lexps( [], []).
prodmat_to_lexps( [R|Rs], [NR|NRs]) :-
    prodrow_to_lexps( R, NR),
    prodmat_to_lexps( Rs, NRs).

prodrow_to_lexps( [],[]).
prodrow_to_lexps( [C|Cs],[NC|NCs]) :-
    prodcell_to_lexp( C, NC) ,
    prodrow_to_lexps( Cs, NCs).

prodcell_to_lexp( C, NC) :-
    filter_zeros( C, C_1),
    write_sum( C_1, NC). 

filter_zeros( [],[]).
filter_zeros( [T|Ts], NTs) :-
    filter_zero_x( T, NTs-NTs_x),
    filter_zeros( Ts, NTs_x). 
    
filter_zero_x( (_L,0) , NTs-NTs) :- !.
filter_zero_x( (L,N) , [N*L|NTs]-NTs). 

%%%%%
%   constraints_entailed_cone( Cs, Vars, Mode, Params, Psi). 
%
%
constraints_entailed_cone( Cs, Vars, Mode, Params, Psi) :-
    to_numbervars_nu( f(Vars,Cs), _Vars, f(Vs_x,Cs_x), _Dim),
    from_constraints_mrep( Cs_x, Vs_x, Mode, MRep),
    get_entailment_cone_mrep( MRep, Params, Psi). 


test_1 :-
    MR = mrep( 3, [ [1,1,1], [1,0,-1] , [-1,-1,0] ] >= [2,-3,4] ),
    get_entailment_cone_mrep( MR, Params, Psi),
    numbervars( f(Params, Psi), 0 , _),
    format( '~n~p~n~p~n',[Params, Psi]).


map_oper_const( [], _Op,_B, H-H).
map_oper_const( [A|As], Op,B, [C|H]-T) :-
    C =.. [Op, A, B],
    map_oper_const( As, Op,B,H-T).
zip_equals( [], [], H-H).
zip_equals( [A|As],[B|Bs] , [C|H]-T) :-
    C = (A=B), 
    zip_equals( As,Bs,H-T).
