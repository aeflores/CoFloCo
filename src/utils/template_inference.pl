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
		difference_constraint/5,difference_constraint2/5,
		max_min_linear_expression_template/5
	]).

:- use_module('cofloco_utils',[repeat_n_times/3,
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
:- use_module(stdlib(fraction),[leq_fr/2,negate_fr/2,multiply_fr/3]).	
:- use_module(stdlib(fraction_list), [naturalize_frl/3]).
:- use_module(stdlib(utils),[ut_flat_list/2]).   
:- use_module(stdlib(linear_expression), [parse_le_fast/2,parse_le/2]).





max_min_linear_expression_template(Linear_Expr_to_Maximize,Vars, Vars_of_Interest, Context, Maxs):-
	length(Vars,N),
	length(Unknowns_1,N),
	from_list_sl(Vars_of_Interest,Vars_of_Interest_set),
	foldl(zero_if_not_in_set(Vars_of_Interest_set),Vars,Unknowns_1,[],Characterizing_constraints),
	get_lin_expr_coeffs(Vars,Linear_Expr_to_Maximize,Coeffs),
	multiply_by_factor([Coeffs],-1,[Coeffs_minus]),
	append(Unknowns_1,[_],Unknowns),
	(generalized_property(Vars,Context,Unknowns,Coeffs_minus,Characterizing_constraints,Exp)->
		parse_le_fast(Exp,Lin_exp),
		
		Maxs=[Lin_exp]
	;
		Maxs=[]
	).
	

difference_constraint2(Head,Call,Phi,Lin_exp,Lin_exp_out):-
	Head=..[_|EVars],
	Call=..[_|CVars],
	length(EVars,N1),
	append(EVars,CVars,Vars),
	length(Unknowns1,N1),
	length(Unknowns2,N1),
	maplist(negation_constr,Unknowns1,Unknowns2,Characterizing_constraints),
	get_lin_expr_coeffs(Vars,Lin_exp,Coeffs),

	multiply_by_factor([Coeffs],-1,[Coeffs_minus]),

	ut_flat_list([Unknowns1,Unknowns2,_],Unknowns),
	generalized_property(Vars,Phi,Unknowns,Coeffs_minus,Characterizing_constraints,system(Complete_system,Ys,Objective_function)),
	ppl_maximize_with_point(c,Complete_system,Objective_function,_Res,Point),
	maplist(=(0),Ys),
	(Point=point(Exp);Point=point(Exp1,Div),Exp=Exp1/Div),
	copy_term((Unknowns,Exp),(Vars_extra,Exp2)),
	append(Vars,[1],Vars_extra),
	parse_le(Exp2,Lin_exp_out).

difference_constraint(Head,Call,Phi,Lin_exp,Lin_exp_out):-
	Head=..[_|EVars],
	Call=..[_|CVars],
	length(EVars,N1),
	append(EVars,CVars,Vars),
	length(Unknowns1,N1),
	length(Unknowns2,N1),
	length(Unknowns3,N1),
	maplist(negation_constr,Unknowns1,Unknowns2,Characterizing_constraints),
	get_lin_expr_coeffs(Vars,Lin_exp,Coeffs),

	multiply_by_factor([Coeffs],-1,[Coeffs_minus]),

	ut_flat_list([Unknowns1,Unknowns2,Alpha_0],Unknowns),
	ut_flat_list([Unknowns1,Unknowns3,Alpha_0],Unknowns_p),
	generalized_property(Vars,Phi,Unknowns,Coeffs_minus,Characterizing_constraints,system(Complete_system,Ys,Objective_function)),
	generalized_property(Vars,Phi,Unknowns_p,Coeffs_minus,[],system(Complete_system2,Ys2,Objective_function2)),
	append(Complete_system,Complete_system2,Complete_system_final),
	%nad_consistent_constraints(Complete_system_final),!,	

	maplist(zip_with_op('=',0),Unknowns3,Cons_better),
	append(Cons_better,Complete_system_final,Complete_system_final2),
	normalize_le(Objective_function+Objective_function2,Objective_function3),
	ppl_maximize_with_point(c,Complete_system_final2,Objective_function3,_,Point),
	!,
	
		%nad_project(Unknowns,Complete_system,Projected),
	%get_generators(c,Unknowns,Projected,Generators),
	%(member(point(Exp),Generators);member(point(Exp1,Div),Generators),Exp=Exp1/Div),
	(Point=point(Exp);Point=point(Exp1,Div),Exp=Exp1/Div),
	maplist(=(0),Ys),
	maplist(=(0),Ys2),
	
	copy_term((Unknowns1,Unknowns2,Unknowns3,Alpha_0,Exp),(Unknowns11,Unknowns21,Unknowns31,Alpha_01,Exp2)),
	maplist(=(0),Unknowns21),
	append(Unknowns11,Unknowns31,Vars),
	Alpha_01=1,
	parse_le(Exp2,Lin_exp_out).
	
generalized_property(Vars,Phi,Unknowns,Expression_vector,Characterizing_constraints,system(Complete_system,Ys,Objective_function)):-
	length(Vars,N),
	constraints_to_mrep_1(Phi,Vars,A, B),
	length(A,M),
	transpose_matrix(A,At),
	
	N1 is N+1,
	identity_matrix(N1,Id),
	multiply_by_factor(Id,-1,Id_minus),
	n_zeros(M,Zeros),
	append(At,[Zeros],At_extra),
	concatenate_matrix(At_extra,Id_minus,At_id),
	
	length(Unknowns,N1),
	length(Ys,M),
	append(Ys,Unknowns,Total_new_vars),
	mrep_eq_to_constraints( At_id,Total_new_vars,'=', Expression_vector,Cs),
	mrep_eq_to_constraints( [B],Ys,'>=', [0],[Extra_constr]),

	maplist(greater_zero,Ys,Cs_extra),
	ut_flat_list([Cs_extra,Extra_constr,Cs,Characterizing_constraints],Complete_system),!,
%	nad_consistent_constraints(Complete_system),!,	
	maplist(negate_fr,B,B_minus),
	generate_objective_function(B_minus,Ys,Objective_function).
	
%X=-Y
negation_constr(X,Y,(1*X+1*Y=0)).

	
constraints_to_mrep_1([],_Vars,[],[]).
constraints_to_mrep_1([Expr>=C|Phi],Vars,[Line|A],[Coeff_0|B]):-
	negate_fr(C,C_neg),
	parse_le_fast(Expr+C_neg,Lin_exp),
	get_lin_expr_coeffs(Vars,Lin_exp,Coeffs),
	append(Line,[Last],Coeffs),
	negate_fr(Last,Coeff_0),
	constraints_to_mrep_1(Phi,Vars,A,B).	
constraints_to_mrep_1([Expr=< C|Phi],Vars,[Line_neg|A],[Coeff_0|B]):-
	negate_fr(C,C_neg),
	parse_le_fast(Expr+C_neg,Lin_exp),
	get_lin_expr_coeffs(Vars,Lin_exp,Coeffs),
	append(Line,[Coeff_0],Coeffs),
	maplist(negate_fr,Line,Line_neg),
	constraints_to_mrep_1(Phi,Vars,A,B).	
constraints_to_mrep_1([Lin_exp= C|Phi],Vars,A,B):-
	constraints_to_mrep_1([Lin_exp=< C,Lin_exp>= C| Phi],Vars,A,B).	

	
get_lin_expr_coeffs(Vars,List+Coeff_0,Coeffs):-
	get_lin_expr_coeffs_aux(Vars,List,Coeff_0,Coeffs).



get_lin_expr_coeffs_aux([],_List,Coeff_0,[Coeff_0]).
get_lin_expr_coeffs_aux([Var|Vars],List,Coeff_0,[Coeff_1|Coeffs]):-
	lookup_lm(List,Var,Coeff_1),!,
	get_lin_expr_coeffs_aux(Vars,List,Coeff_0,Coeffs).
get_lin_expr_coeffs_aux([_Var|Vars],List,Coeff_0,[0|Coeffs]):-
	get_lin_expr_coeffs_aux(Vars,List,Coeff_0,Coeffs).	
	
zero_if_not_in_set(Important_vars,Var,Un_var,Cs,[Un_var=0|Cs]):-
	\+contains_sl(Important_vars,Var),!.
zero_if_not_in_set(_Important_vars,_Var,_Un_var,Cs,Cs).	
	
mrep_eq_to_constraints([],_Vars,_Op,[],[]).
mrep_eq_to_constraints([Line|Matrix],Vars,Op,[B|Bs],[C|Cs]):-	
	naturalize_frl([B|Line],[B_1|Line_1],_),	
	maplist(zip_with_op(*),Line_1,Vars,Coeffs),
	exclude(zero_coeff,Coeffs,Coeffs1),
	write_sum(Coeffs1,Sum),
	C=..[Op,Sum,B_1],
	mrep_eq_to_constraints(Matrix,Vars,Op,Bs,Cs).	
		
zero_coeff(0*_).
		
generate_objective_function(B,Ys,Objective_function):-
	maplist(mult,B,Ys,Factors),
	write_sum(Factors,Objective_function).
	
mult(B,Y,B*Y).


greater_zero(Y,1*Y>=0).
identity_matrix(1,[[1]]).
identity_matrix(N,[[1|Zeros]|Id3]):-N2 is N-1,
	identity_matrix(N2,Id2),
	maplist(append([0]),Id2,Id3),
	n_zeros(N2,Zeros).
multiply_by_factor(Matrix,Factor,Matrix1):-
		maplist(maplist(multiply_fr(Factor)),Matrix,Matrix1).
n_zeros(N,Zeros):-
	repeat_n_times(N,0,Zeros).

transpose_matrix([[]|_],[]).
transpose_matrix(A,[Column1|At_aux]):-	
	maplist(get_head_tail,A,Column1,Rest),
	transpose_matrix(Rest,At_aux).
get_head_tail([H|T],H,T).

concatenate_matrix(A,B,AB):-
	maplist(append,A,B,AB).		
	
	