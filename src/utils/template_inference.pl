/** <module> template_inference

This module generates constraints that express an upper bound of the summatory of a linear expression.
It uses linear programming to infer linear expressions that satisfy a property given a template.

    
@author Antonio Flores Montoya

@copyright Copyright (C) 2014,2015 Antonio Flores Montoya

@license This file is part of CoFloCo. 
    CoFloCo is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    any later version.

    CoFloCo is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with CoFloCo.  If not, see <http://www.gnu.org/licenses/>.
*/


:- module(template_inference,[
		difference_constraint2_farkas_dmatrix/5

	]).

:- use_module('cofloco_utils',[repeat_n_times/3,sort_with/3,
			normalize_constraint/2,zip_with_op/4,
			write_sum/2]).
:- use_module('cost_expressions',[normalize_le/2]).
			
:- use_module(stdlib(polyhedra_ppl),[
    get_generators/4,ppl_maximize_with_point/5,ppl_minimize_with_point/5
]).

:- use_module(stdlib(matrix_constraint),[
    decompose_mrep/4,
    mrep_to_constraints/3,
    constraints_to_mrep/4,
    from_constraints_mrep/4,
    get_entailment_cone_mrep/3,
    constraints_entailed_cone/5
]).
:- use_module(stdlib(numeric_abstract_domains),[nad_project/3,nad_minimize/3,nad_maximize/3,
						nad_consistent_constraints/1,
						nad_entails/3, nad_lub/6,nad_list_lub/2,
						nad_widen/5, nad_false/1,
						nad_all_ranking_functions_PR/4,
						nad_glb/3]).
:- use_module(stdlib(set_list),[from_list_sl/2,contains_sl/2]).		
:- use_module(stdlib(list_map),[lookup_lm/3]).						
:- use_module(stdlib(fraction),[
	leq_fr/2,
	negate_fr/2,
	multiply_fr/3,
	sum_fr/3,
	subtract_fr/3]).	
:- use_module(stdlib(fraction_list), [naturalize_frl/3]).
:- use_module(stdlib(utils),[ut_flat_list/2]).   
:- use_module(stdlib(linear_expression), [
	parse_le_fast/2,
	parse_le/2,
	multiply_le/3,
	write_le/2,
	integrate_le/3]).


max_min_linear_expression_template(Linear_Expr_to_Maximize,Vars, Vars_of_Interest, Context, Maxs):-
	length(Vars,N),
	length(Unknowns_1,N),
	from_list_sl(Vars_of_Interest,Vars_of_Interest_set),
	foldl(zero_if_not_in_set(Vars_of_Interest_set),Vars,Unknowns_1,[],Characterizing_constraints),
	get_lin_expr_dmatrix(Vars,Linear_Expr_to_Maximize,Coeffs),
	multiply_by_factor_dmatrix(Coeffs,-1,Coeffs_minus),
	get_symbolic_dmatrix(Unknowns,Template),
	add_dmatrix_symbolically(Template,Coeffs_minus,Expression_vector),
	append(Unknowns_1,[_],Unknowns),
	generalized_farkas_property_dmatrix(Vars,Context,Expression_vector,Characterizing_constraints,system(Complete_system,Ys)),
	append(Ys,Unknowns,All_new_vars),
	get_generators(c,All_new_vars,Complete_system,Generators),
	(member(point(Exp),Generators);member(point(Exp1,Div),Generators),Exp=Exp1/Div),!,
	maplist(=(0),Ys),
	copy_term((Unknowns,Exp),([1|Vars],Exp2)),
	parse_le(Exp2,Lin_exp_out),
	Maxs=[Lin_exp_out].

max_min_linear_expression_template(_Linear_Expr_to_Maximize,_Vars, _Vars_of_Interest, _Context,[]).	
	
	
difference_constraint2_farkas_dmatrix(Head,Call,Phi,Lin_exp,Lin_exp_list_set):-
	Head=..[_|EVars],
	Call=..[_|CVars],
	length(EVars,N1),
	append(EVars,CVars,Vars),
	length(Unknowns1,N1),
	length(Unknowns2,N1),
	length(Unknowns3,N1),
	maplist(negation_constr,Unknowns1,Unknowns2,Characterizing_constraints),
	get_lin_expr_dmatrix(Vars,Lin_exp,Coeffs),
	multiply_by_factor_dmatrix(Coeffs,-1,Coeffs_minus),
	append([Coeff_0|Unknowns1],Unknowns2,Unknowns),
	get_symbolic_dmatrix(Unknowns,Template),
	add_dmatrix_symbolically(Template,Coeffs_minus,Expression_vector),
	generalized_farkas_property_dmatrix(Vars,Phi,Expression_vector,Characterizing_constraints,system(Complete_system,Ys)),
	
	append(Ys,Unknowns,All_new_vars),
	get_generators(c,All_new_vars,Complete_system,Generators),
	
	append([Coeff_0|Unknowns1],Unknowns3,Unknowns4),
	get_symbolic_dmatrix(Unknowns4,Template2),
	maplist(is_zero,Unknowns3,Characterizing_constraints2),
	generalized_farkas_property_dmatrix(Vars,Phi,Template2,Characterizing_constraints2,system(Complete_system2,Ys2)),
	append(All_new_vars,Ys2,All_new_vars2),
	append(All_new_vars2,Unknowns3,All_new_vars3),

	append(Complete_system,Complete_system2,Complete_system_joined),
	get_generators(c,All_new_vars3,Complete_system_joined,Generators2),
	maplist(=(0),Ys),
	maplist(=(0),Ys2),
	maplist(=(0),Unknowns3),
	get_expressions_from_points(Generators,Lin_exp_list),
	copy_term(([Coeff_0|Unknowns1],Unknowns2,Generators2),([Coeff_0_c|Unknowns1_c],Unknowns2_c,Generators2_c)),
	maplist(=(0),Unknowns2_c),
	get_expressions_from_points(Generators2_c,Lin_exp_list2),
	copy_term((Unknowns,Lin_exp_list),([1|Vars],Lin_exp_list_copy)),
	copy_term(([Coeff_0_c|Unknowns1_c],Lin_exp_list2),([1|EVars],Lin_exp_list_copy2)),
	
	append(Lin_exp_list_copy,Lin_exp_list_copy2,Lin_exp_list_out),
	from_list_sl(Lin_exp_list_out,Lin_exp_list_set),
	Lin_exp_list_set\=[].	


generalized_farkas_property_dmatrix(Vars,Phi,Expression_vector,Characterizing_constraints,system(Complete_system,Ys)):-
	constraints_to_dmatrix(Phi,Vars,A),
	transpose_dmatrix(A,At),
	get_dmatrix_y_dimension(At,M),
	length(Ys,M),	
	dmatrix_to_constraints( At,Ys,'=', Expression_vector,Cs),
	maplist(greater_zero,Ys,Cs_extra),
	ut_flat_list([Cs_extra,Cs,Characterizing_constraints],Complete_system),!.
	

get_expressions_from_points([],[]).	
get_expressions_from_points([point(Exp)|Generators],[Lin_exp|Lin_exps]):-!,
		parse_le(Exp,Lin_exp),
		get_expressions_from_points(Generators,Lin_exps).
get_expressions_from_points([point(Exp,Div)|Generators],[Lin_exp|Lin_exps]):-!,
		parse_le(Exp/Div,Lin_exp),
		get_expressions_from_points(Generators,Lin_exps).		
get_expressions_from_points([_|Generators],Lin_exps):-
		get_expressions_from_points(Generators,Lin_exps).			
		
get_symbolic_dmatrix(Unknowns,dmatrix(1,X,[(1,List)])):-
	length(Unknowns,X),
	get_symbolic_dmatrix_1(Unknowns,1,List).
	
get_symbolic_dmatrix_1([],_,[]).
get_symbolic_dmatrix_1([U|Unknowns],N,[(N,U)|List]):-
	N1 is N+1,
	get_symbolic_dmatrix_1(Unknowns,N1,List).
	
add_dmatrix_symbolically(dmatrix(X,Y,Matrix1),dmatrix(X,Y,Matrix2),dmatrix(X,Y,Matrix_sum)):-
	add_dmatrix_symbolically_1(Matrix1,Matrix2,Matrix_sum).

add_dmatrix_symbolically_1([],Matrix2,Matrix2):-!.
add_dmatrix_symbolically_1(Matrix1,[],Matrix1):-!.
add_dmatrix_symbolically_1([(N1,Line1)|Matrix1],[(N1,Line2)|Matrix2],[(N1,Line_sum)|Matrix_sum]):-
	add_dline_symbolically(Line1,Line2,Line_sum),
	add_dmatrix_symbolically_1(Matrix1,Matrix2,Matrix_sum).
	
add_dmatrix_symbolically_1([(N1,Line1)|Matrix1],[(N2,Line2)|Matrix2],[(N1,Line1)|Matrix_sum]):-
	N1<N2,
	add_dmatrix_symbolically_1(Matrix1,[(N2,Line2)|Matrix2],Matrix_sum).	
add_dmatrix_symbolically_1([(N1,Line1)|Matrix1],[(N2,Line2)|Matrix2],[(N2,Line2)|Matrix_sum]):-
	N2<N1,
	add_dmatrix_symbolically_1([(N1,Line1)|Matrix1],Matrix2,Matrix_sum).	
	
add_dline_symbolically([],Line2,Line2):-!.
add_dline_symbolically(Line1,[],Line1):-!.	

add_dline_symbolically([(N1,Elem1)|Line1],[(N1,Elem2)|Line2],[(N1,Elem1+Elem2)|Line_sum]):-
	add_dline_symbolically(Line1,Line2,Line_sum).
	
add_dline_symbolically([(N1,Elem1)|Line1],[(N2,Elem2)|Line2],[(N1,Elem1)|Line_sum]):-
	N1<N2,
	add_dline_symbolically(Line1,[(N2,Elem2)|Line2],Line_sum).	
add_dline_symbolically([(N1,Elem1)|Line1],[(N2,Elem2)|Line2],[(N2,Elem2)|Line_sum]):-
	N2<N1,
	add_dline_symbolically([(N1,Elem1)|Line1],Line2,Line_sum).
	
	
%X=-Y
negation_constr(X,Y,(1*X+1*Y=0)).

get_line_product(Vars,Mult,Line,Sum):-
	maplist(multiply_line_by_factor(Mult),Line,Line1),
	get_line_product_1(Vars,1,Line1,Factors),
	(Factors=[]-> 
	Sum=0
	;
	write_sum(Factors,Sum)
	).

multiply_line_by_factor(F,(I,Val),(I,Val2)):-
	multiply_fr(Val,F,Val2).
	
get_line_product_1([],_,_Line1,[]):-!.
get_line_product_1(_,_,[],[]).
get_line_product_1([Var|Vars],N,[(N,Val)|Line],[Val*Var|Factors]):-
	N1 is N+1,
	get_line_product_1(Vars,N1,Line,Factors).
get_line_product_1([_Var|Vars],N,[(N2,Val)|Line],Factors):-
	N2 > N,
	N1 is N+1,
	get_line_product_1(Vars,N1,[(N2,Val)|Line],Factors).
	

expand_dmatrix_y_dimension(dmatrix(X,Y,Vals),N,dmatrix(X,Y2,Vals)):-
		N>0,
		Y2 is Y+N.
expand_dmatrix_x_dimension(dmatrix(X,Y,Vals),N,dmatrix(X2,Y,Vals)):-
		N>0,
		X2 is X+N.	
		
dmatrix_to_constraints(dmatrix(X,Y,Vals),Vars,Op, dmatrix(1,X,[(1,Constants)]),[C|Cs]):-
	length(Vars,Y),
	Vals=[(1,Line)|Vals_rest],
	Constants=[(1,Constant)|Constants_rest],	
	parse_le(Constant,Lin_exp_right),
	integrate_le(Lin_exp_right,Den,Lin_exp_right_int),
	write_le(Lin_exp_right_int,Cnt),
	get_line_product(Vars,Den,Line,Lin_exp),
	C=..[=<,Lin_exp,Cnt],
	get_constraints(Vals_rest,Constants_rest,2,Vars,Op,Cs).
	
get_constraints([],[],_N,_Vars,_Op,[]).

get_constraints([(N,Line)|Lines],[],N,Vars,Op,[C|Cs]):-
	get_line_product(Vars,1,Line,Lin_exp),
	C=..[Op,Lin_exp,0],
	N1 is N+1,
	get_constraints(Lines,[],N1,Vars,Op,Cs).

get_constraints([(N_diff,Line)|Lines],[],N,Vars,Op,Cs):-
	N_diff>N,!,
	N1 is N+1,
	get_constraints([(N_diff,Line)|Lines],[],N1,Vars,Op,Cs).	
	
get_constraints([(N,Line)|Lines],[(N,Constant)|Constants],N,Vars,Op,[C|Cs]):-!,
	parse_le(Constant,Lin_exp_right),
	integrate_le(Lin_exp_right,Den,Lin_exp_right_int),
	write_le(Lin_exp_right_int,Cnt),
	get_line_product(Vars,Den,Line,Lin_exp),
	C=..[Op,Lin_exp,Cnt],
	N1 is N+1,
	get_constraints(Lines,Constants,N1,Vars,Op,Cs).
	
get_constraints([(N,Line)|Lines],[(N_diff,Constant)|Constants],N,Vars,Op,[C|Cs]):-
	N_diff > N,!,
	get_line_product(Vars,1,Line,Lin_exp),
	C=..[Op,Lin_exp,0],
	N1 is N+1,
	get_constraints(Lines,[(N_diff,Constant)|Constants],N1,Vars,Op,Cs).
	
get_constraints([(N_diff,Line)|Lines],[(N,Constant)|Constants],N,Vars,Op,[C|Cs]):-
	N_diff > N,!,
	parse_le(Constant,Lin_exp_right),
	integrate_le(Lin_exp_right,_Den,Lin_exp_right_int),
	write_le(Lin_exp_right_int,Cnt),
	C=..[Op,0,Cnt],
	N1 is N+1,
	get_constraints([(N_diff,Line)|Lines],Constants,N1,Vars,Op,Cs).	
	
get_constraints([(N_diff1,Line)|Lines],[(N_diff2,Constant)|Constants],N,Vars,Op,Cs):-
	N_diff1 > N,
	N_diff2 > N,
	N1 is N+1,
	get_constraints([(N_diff1,Line)|Lines],[(N_diff2,Constant)|Constants],N1,Vars,Op,Cs).		

get_lin_exp_from_line(Line,Vars,Lin_exp):-
	get_lin_exp_from_line_1(Line,1,Vars,Coeffs),
	write_le(Coeffs+0,Lin_exp).
	
get_lin_exp_from_line_1([],_,_Vars,[]).
get_lin_exp_from_line_1([(N,Val)|Line],N,[V|Vars],[(V,Val)|Coeffs]):-!,
	N1 is N+1,
	get_lin_exp_from_line_1(Line,N1,Vars,Coeffs).
get_lin_exp_from_line_1([(N_diff,Val)|Line],N,Vars,Coeffs):-
	N_diff > N,
	N1 is N+1,
	get_lin_exp_from_line_1([(N_diff,Val)|Line],N1,Vars,Coeffs).
	

get_dmatrix_y_dimension(dmatrix(_X,Y,_Vals),Y).

transpose_dmatrix(dmatrix(X,Y,Vals),dmatrix(Y,X,Vals_transposed)):-
	get_columns(1,Y,Vals,Vals_transposed).

get_columns(Y1,Y,_Vals,[]):-Y1>Y.
get_columns(N,Y,Vals,Columns_out):-
	N =< Y,
	get_column(N,Vals,Column,Vals2),
	(Column\=[]-> 
	    Columns_out=[(N,Column)|Columns]
	    ;
	    Columns_out=Columns
	),
	N1 is N+1,
	get_columns(N1,Y,Vals2,Columns).
	
get_column(N,Vals,Column,Vals2):-
	maplist(get_n_element(N),Vals,Column_non_flat,Vals2),
	ut_flat_list(Column_non_flat,Column).
get_n_element(N,(X,[(N,Val)|Vals2]),(X,Val),(X,Vals2)):-!.
get_n_element(_N,(X,Vals2),[],(X,Vals2)).


multiply_by_factor_dmatrix(dmatrix(X,Y,Vals),Factor,dmatrix(X,Y,Vals2)):-
	maplist(multiply_dline(Factor),Vals,Vals2).

multiply_dline(Factor,(X,Line),(X,Line2)):-
	maplist(multiply_delement(Factor),Line,Line2).
multiply_delement(Factor,(Y,Val),(Y,Val2)):-
	multiply_fr(Factor,Val,Val2).


	

constraints_to_dmatrix(Cons,Vars,dmatrix(X,Y1,Vals2)):-
	length(Vars,Y),
	Y1 is Y+1,
	copy_term((Cons,Vars),(Cons1,Vars2)),
	constraints_to_dmatrix_1(Cons1,1,X,Vals),
	number_list(Vars2,2),
	maplist(sort_line,Vals,Vals2).

sort_line((X,Map),(X,Sorted_map)):-
	sort_with(Map,greater_integer_map,Sorted_map).

greater_integer_map((I1,_),(I2,_)):-
	I1 > I2.
	
number_list([],_).
number_list([N|Ns],N):-
	N1 is N+1,	
	number_list(Ns,N1).

constraints_to_dmatrix_1([],N,N1,[]):-N1 is N-1.

constraints_to_dmatrix_1([Expr>=C|Phi],N,N_out,[(N,Line_1)|Lines]):-
	negate_fr(C,C_neg),
	parse_le_fast(Expr+C_neg,Le_aux),
	integrate_le(Le_aux,_Denom,Line+Constant),
	N1 is N+1,
	(Constant==0->
		Line_1=Line
	   ;
	   	Line_1=[(1,Constant)|Line]
	),
	constraints_to_dmatrix_1(Phi,N1,N_out,Lines).
	
constraints_to_dmatrix_1([Expr=< C|Phi],N,N_out,[(N,Line_1)|Lines]):-
	negate_fr(C,C_neg),
	parse_le_fast(Expr+C_neg,Le_aux),
	integrate_le(Le_aux,_Denom,Lin_exp),
	multiply_le(Lin_exp,-1,Line+Constant),
	N1 is N+1,
	(Constant==0->
		Line_1=Line
	   ;
	   	Line_1=[(1,Constant)|Line]
	),
	constraints_to_dmatrix_1(Phi,N1,N_out,Lines).	

constraints_to_dmatrix_1([Expr= C|Phi],N,N_out,Lines):-
	constraints_to_dmatrix_1([Expr=<C, Expr>= C|Phi],N,N_out,Lines).	


get_lin_expr_dmatrix(Vars,List+Coeff_0,dmatrix(1,Y1,[(1,Coeffs)])):-
	length(Vars,Y),
	Y1 is Y+1,
	copy_term((Vars,List),(Vars2,List2)),
	number_list(Vars2,2),
	(Coeff_0=0->
		List2=Coeffs
		;
		[(1,Coeff_0)|List2]=Coeffs
	).

	
zero_if_not_in_set(Important_vars,Var,Un_var,Cs,[Un_var=0|Cs]):-
	\+contains_sl(Important_vars,Var),!.
zero_if_not_in_set(_Important_vars,_Var,_Un_var,Cs,Cs).	
	
greater_zero(Y,1*Y>=0).
is_zero(Y,1*Y=0).

	