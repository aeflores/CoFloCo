/** <module> template_inference

This module generates constraints that express an upper bound of the sum of a linear expression.
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
	difference_constraint_farkas_ub/6,
	difference_constraint_farkas_lb/5,
	max_min_linear_expression_list_all/6,
	difference_constraint_farkas_multiple_ub/5,
	farkas_leave_ub_candidate/5
	]).

:- use_module('cofloco_utils',[
			sort_with/3,write_le_internal/2,	
			write_sum/2]).
:- use_module('polyhedra_optimizations',[
			nad_normalize_polyhedron/2]).			
			
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
	sum_le/3,
	multiply_le/3,
	negate_le/2,
	write_le/2,
	subtract_le/3,
	is_constant_le/1,
	integrate_le/3]).
:-use_module(library(apply_macros)).
:-use_module(library(lists)).

%! difference_constraint_farkas_ub(Head:term,Call:term,Phi:polyhedron,Lin_exp:nlinexp,Lin_exp_list:list(nlinexp),Lin_exp_list2:list(nlinexp))
% generate a set of Head-tail upper bound candidates Lin_exp_list2 and Head upper bound candidates Lin_exp_list
% for the linear expression Lin_exp in the loop defined as Phi
difference_constraint_farkas_ub(Head,Call,Phi,Lin_exp,Lin_exp_list,Lin_exp_list2):-
	Head=..[_|EVars],
	Call=..[_|CVars],
	length(EVars,N1),
	append(EVars,CVars,Vars),
	length(Unknowns1,N1),
	length(Unknowns2,N1),
	length(Unknowns3,N1),
	% the call coefficients are the opposite of the head coefficients
	maplist(negation_constr,Unknowns1,Unknowns2,Characterizing_constraints),
	% the negative version of the linear expression
	get_lin_expr_dmatrix(Vars,Lin_exp,Coeffs),
	multiply_by_factor_dmatrix(Coeffs,-1,Coeffs_minus),
	append([Coeff_0|Unknowns1],Unknowns2,Unknowns),
	% l(x)-l(x')
	get_symbolic_dmatrix(Unknowns,Template),
	% l(x)-l(x')-Lin_exp(xx')
	add_dmatrix_symbolically(Template,Coeffs_minus,Expression_vector),
	
	append([Coeff_0|Unknowns1],Unknowns3,Unknowns4),
	% l(x)+0
	get_symbolic_dmatrix(Unknowns4,Template2),
	% l(x)-Lin_exp(xx')
	add_dmatrix_symbolically(Template2,Coeffs_minus,Expression_vector2),
	
	le_print_int(Lin_exp,Exp,_Den),
	%generate constraints for head tail candidates
	generalized_farkas_property_dmatrix(Vars,[Exp>=0|Phi],Expression_vector,[Coeff_0=0|Characterizing_constraints],system(Complete_system1,Ys1)),
	%generate constraints for head candidates
	generalized_farkas_property_dmatrix(Vars,[Exp>=0|Phi],Expression_vector2,[],system(Complete_system3,Ys3)),
	%if feasible consider the case where Lin_exp is negative
	(\+nad_entails(Vars,Phi,[Exp>=0])->
	  generalized_farkas_property_dmatrix(Vars,[Exp=<0|Phi],Template,[],system(Complete_system2,Ys2)),
	  generalized_farkas_property_dmatrix(Vars,[Exp=<0|Phi],Template2,[],system(Complete_system4,Ys4))
	  ;
	  system(Complete_system2,Ys2)=system([],[]),
	  system(Complete_system4,Ys4)=system([],[])
	),
	%simplify constraints in Complete_system2 to avoid having too many variables
	nad_project(Unknowns1,Complete_system2,Projected2),
	% put together the constraints corresponding to Exp>=0 and Exp=<0
	nad_glb(Complete_system1,Projected2,Complete_system_part1),
	Ys1=[Var|_],!,
	%obtain a point of the resulting polyhedron
	(ppl_minimize_with_point(c,Complete_system_part1,Var,_,Point1)->
		%set the call coefficients of the template to 0
		maplist(=(0),Unknowns3),
		%join the constraints sets
		nad_project(Unknowns1,Complete_system4,Projected4),
    	nad_glb(Complete_system3,Projected4,Complete_system_part2),
		nad_glb(Complete_system_part1,Complete_system_part2,Complete_system_joined),
		Generators=[Point1],
		%obtain a point of the resulting polyhedron
		(ppl_minimize_with_point(c,Complete_system_joined,Var,_,Point2)->
		Generators2=[Point2]
		;
		Generators2=[]
		)
		;
	Generators=[],
	Generators2=[]
	),
	%once we have the point, we can set all the coefficients variables to 0 and obtain the point in terms of Unknowns
	maplist(=(0),Ys1),
	maplist(=(0),Ys2),
	maplist(=(0),Ys3),
	maplist(=(0),Ys4),
	
	%extract the linear expressions from the points
	maplist(=(0),Unknowns2),
	copy_term(([Coeff_0|Unknowns1],Generators),([1|EVars],Generators_copy)),
	copy_term(([Coeff_0|Unknowns1],Generators2),([1|EVars],Generators_copy2)),
	
	get_expressions_from_points(Generators_copy,Lin_exp_list),
	get_expressions_from_points(Generators_copy2,Lin_exp_list2),
	append(Lin_exp_list,Lin_exp_list2,Lin_exp_list_total),
	Lin_exp_list_total\=[].

%! difference_constraint_farkas_lb(Head:term,Call:term,Phi:polyhedron,Lin_exp:nlinexp,Lin_exps_non_constant:list(nlinexp))
% generate a set of Head-tail lower bound candidates Lin_exps_non_constant 
% for the linear expression Lin_exp in the loop defined as Phi
difference_constraint_farkas_lb(Head,Call,Phi,Lin_exp,Lin_exps_non_constant):-
	Head=..[_|EVars],
	Call=..[_|CVars],
	length(EVars,N1),
	append(EVars,CVars,Vars),
	length(Unknowns1,N1),
	length(Unknowns2,N1),
	maplist(negation_constr,Unknowns1,Unknowns2,Characterizing_constraints),
	% lin_exp
	get_lin_expr_dmatrix(Vars,Lin_exp,Coeffs),
	append([Coeff_0|Unknowns1],Unknowns2,Unknowns),
	% -le(xx')
	get_symbolic_dmatrix_negated(Unknowns,Template_neg),
	% lin_exp(xx')-le(xx')
	add_dmatrix_symbolically(Template_neg,Coeffs,Expression_vector),
	le_print_int(Lin_exp,Exp,_Den),
	% lin_exp(xx')-le(xx')>=0
	generalized_farkas_property_dmatrix(Vars,[Exp>=0|Phi],Expression_vector,[Coeff_0=0|Characterizing_constraints],system(Complete_system,Ys)),
	(\+nad_entails(Vars,Phi,[Exp>=0])->
		generalized_farkas_property_dmatrix(Vars,[Exp=<0|Phi],Template_neg,[],system(Complete_system2,Ys2))
		;
		system(Complete_system2,Ys2)=system([],[])
	),

	ut_flat_list([Ys,Unknowns,Ys2],All_new_vars),
	append(Complete_system,Complete_system2,Complete_system_final),
	% here we get multiple candidates
	get_generators(c,All_new_vars,Complete_system_final,Generators),
	maplist(=(0),Ys),
	maplist(=(0),Ys2),
	maplist(=(0),Unknowns2),
	%obtain linear expressions form the candidates
	copy_term(([Coeff_0|Unknowns1],Generators),([1|EVars],Generators_copy)),	
	get_expressions_from_points(Generators_copy,Lin_exp_list),
	from_list_sl(Lin_exp_list,Lin_exp_list_set),
	exclude(is_constant_le,Lin_exp_list_set,Lin_exps_non_constant),
	Lin_exps_non_constant\=[].	

get_negated_unknowns([],_,[],[]).
get_negated_unknowns([_Call|Calls],Unknowns_head,Vars1,Characterizing_constraints1):-
	get_negated_unknowns(Calls,Unknowns_head,Vars,Characterizing_constraints),
	length(Unknowns_head,N),
	length(Unknowns_call,N),
	maplist(negation_constr,Unknowns_head,Unknowns_call,Characterizing_constraints_new),
	append(Unknowns_call,Vars,Vars1),
	append(Characterizing_constraints_new,Characterizing_constraints,Characterizing_constraints1).
	
difference_constraint_farkas_multiple_ub(Head,Calls,Phi_1,Lin_exp,Lin_exp_list):-
	nad_normalize_polyhedron(Phi_1,Phi),
	Head=..[_|EVars],
	term_variables(Calls,CVars),
	length(EVars,N1),
	append(EVars,CVars,Vars),
	length(Unknowns_head,N1),
	get_negated_unknowns(Calls,Unknowns_head,Unknown_calls,Characterizing_constraints),

	% the negative version of the linear expression
	get_lin_expr_dmatrix(Vars,Lin_exp,Coeffs),
	multiply_by_factor_dmatrix(Coeffs,-1,Coeffs_minus),
	append([Coeff_0|Unknowns_head],Unknown_calls,Unknowns),
	% l(x)-l(x')
	get_symbolic_dmatrix(Unknowns,Template),
	% l(x)-l(x')-Lin_exp(xx')
	add_dmatrix_symbolically(Template,Coeffs_minus,Expression_vector),
	
	get_negated_unknowns(Calls,Unknowns_head,Unknown_calls2,_),
	append([Coeff_1|Unknowns_head],Unknown_calls2,Unknowns2),
	% l(x)+Coeff_1
	get_symbolic_dmatrix(Unknowns2,Template2),
	% l(x)_coeff_1-Lin_exp(xx')
	%add_dmatrix_symbolically(Template2,Coeffs_minus,Expression_vector2),
	
	% l(x)_coeff_1 must be positive
	Expression_vector2=Template2,
	
	%generate constraints for head tail candidates
	generalized_farkas_property_dmatrix(Vars,Phi,Expression_vector,[Coeff_0=0|Characterizing_constraints],system(Complete_system1,Ys1)),
	generalized_farkas_property_dmatrix(Vars,Phi,Expression_vector2,[Coeff_1>=0],system(Complete_system2,Ys3)),
	maplist(=(0),Unknown_calls2),	
	ut_flat_list([Complete_system1,Complete_system2],Complete_system_final),
	nad_project(Unknowns,Complete_system_final,Complete_system_proy),
	% here we get multiple candidates
	get_generators(c,Unknowns,Complete_system_proy,Generators),
	%once we have the point, we can set all the coefficients variables to 0 and obtain the point in terms of Unknowns
	maplist(=(0),Ys1),
	maplist(=(0),Ys3),
	
	%extract the linear expressions from the points
	copy_term(([Coeff_1|Unknowns_head],Unknown_calls,Generators),([Coeff_0_c2|Unknowns1_c2],Unknowns_calls_c2,Generators_c)),
	maplist(=(0),Unknowns_calls_c2),
	copy_term(([Coeff_0_c2|Unknowns1_c2],Generators_c),([1|EVars],Generators_copy)),
	
	get_expressions_from_points(Generators_copy,Lin_exp_list).

farkas_leave_ub_candidate(Head,Calls,Cs,Lin_exp,Lin_exp_list):-
	Head=..[_|EVars],
	term_variables(Calls,CVars),
	length(EVars,N1),
	append(EVars,CVars,Vars),
	length(Unknowns_head,N1),
	get_negated_unknowns(Calls,Unknowns_head,Unknown_calls,Characterizing_constraints),
    copy_term(Unknown_calls,Unknown_calls2),
	% the negative version of the linear expression
	append([Coeff_0|Unknowns_head],Unknown_calls,Unknowns),
	% l(x)-l(x')
	get_symbolic_dmatrix(Unknowns,Template),
	Expression_vector=Template,
	
	append([Coeff_0|Unknowns_head],Unknown_calls2,Unknowns2),
	get_symbolic_dmatrix(Unknowns2,Template2),
	% l(x)_coeff_1-Lin_exp(xx')
	foldl(get_sum_exp_calls(Head,Lin_exp),Calls,[]+0,Lin_exp_calls),
	
	get_lin_expr_dmatrix(Vars,Lin_exp_calls,Coeffs),
	multiply_by_factor_dmatrix(Coeffs,-1,Coeffs_minus),
	add_dmatrix_symbolically(Template2,Coeffs_minus,Expression_vector2),
%	Expression_vector2=Template2,
	%generate constraints for head tail candidates
	generalized_farkas_property_dmatrix(Vars,Cs,Expression_vector,[Coeff_0=0|Characterizing_constraints],system(Complete_system1,Ys1)),
	generalized_farkas_property_dmatrix(Vars,Cs,Expression_vector2,[],system(Complete_system2,Ys3)),
	ut_flat_list([Complete_system1,Complete_system2],Complete_system_final),
	maplist(=(0),Unknown_calls2),
	nad_project(Unknowns,Complete_system_final,Complete_system_proy),
	% here we get multiple candidates
	get_generators(c,Unknowns,Complete_system_proy,Generators),
	%once we have the point, we can set all the coefficients variables to 0 and obtain the point in terms of Unknowns
	maplist(=(0),Ys1),
	maplist(=(0),Ys3),
	
	%extract the linear expressions from the points
	copy_term(([Coeff_0|Unknowns_head],Unknown_calls,Generators),([Coeff_0_c2|Unknowns1_c2],Unknowns_calls_c2,Generators_c)),
	maplist(=(0),Unknowns_calls_c2),
	copy_term(([Coeff_0_c2|Unknowns1_c2],Generators_c),([1|EVars],Generators_copy)),
	get_expressions_from_points(Generators_copy,Lin_exp_list).

get_sum_exp_calls(Head,Lin_exp,Call,Accum,Accum2):-
	copy_term((Head,Lin_exp),(Call,Lin_exp2)),
	sum_le(Accum,Lin_exp2,Accum2).
	
max_min_linear_expression_list_all(Lin_exps,Vars,Vars_of_interest,Phi_1,max,Lin_exp_list):-
	trace,
	from_list_sl(Vars_of_interest,Vars_of_interest_set),
	nad_normalize_polyhedron(Phi_1,Phi),
	maplist(get_max_polyhedron(Vars,Vars_of_interest_set,Phi,max,Coeff_0),Lin_exps,Css),
	nad_list_glb(Css,Cs),
	term_variables(Cs,Vars),
	get_generators(c,Vars,Cs,Generators),
	Coeff_0=1,
	get_expressions_from_points(Generators,Lin_exp_list).
%HERE
	
get_max_polyhedron(Vars,Vars_of_interest_set,Phi,Coeff_0_c,max,Lin_exp,Cs):-
	copy_term((Vars,Vars_of_interest_set),(Unknowns1,Coeffs_of_interest)),
	from_list_sl(Coeffs_of_interest,Coeffs_of_interest_set),
	from_list_sl(Unknowns1,Unknowns1_set),
	difference_sl(Unknowns1_set,Coeffs_of_interest_set,Zero_coeffs),
	Unknowns=[Coeff_0|Unknowns1],
	% l(x)
	get_symbolic_dmatrix(Unknowns,Template),
	% the negative version of the linear expression
	get_lin_expr_dmatrix(Vars,Lin_exp,Coeffs),
	multiply_by_factor_dmatrix(Coeffs,-1,Coeffs_minus),	
	% l(x)-Lin_exp(xx')
	add_dmatrix_symbolically(Template,Coeffs_minus,Expression_vector),
	%generate constraints for head tail candidates
	generalized_farkas_property_dmatrix(Vars,Phi,Expression_vector,[],system(Complete_system1,_Ys1)),

	maplist(=(0),Zero_coeffs),	
	nad_project(Unknowns,Complete_system1,Complete_system_proy),
	copy_term((Coeff_0,Coeffs_of_interest,Complete_system_proy),(Coeff_0_c,Vars_of_interest_set,Cs)).


le_print_int(Lin_exp,Exp,Den):-
		integrate_le(Lin_exp,Den,Lin_exp_nat),
		write_le_internal(Lin_exp_nat,Exp).

%! generalized_farkas_property_dmatrix(Vars:list(var),Phi:polyhedron,Expression_vector:dvector,Characterizing_constraints:polyhedron,System:system(polyhedron,list(var)))
% given a polyhedron Phi and a property Expressions_vector>=0 generate a polyhedron
% that represent the linear combinations of the constraints of Phi to obtain Expression_vector
% Characterizing_constraints are additional constraints that are included in the result
% The variables Ys are the coefficients that multiply the constraints of Phi
generalized_farkas_property_dmatrix(Vars,Phi,Expression_vector,Characterizing_constraints,system(Complete_system,Ys)):-
	constraints_to_dmatrix(Phi,Vars,A),
	transpose_dmatrix(A,At),
	get_dmatrix_y_dimension(At,M),
	length(Ys,M),	
	dmatrix_to_constraints( At,Ys,'=', Expression_vector,Cs),
	maplist(greater_zero,Ys,Cs_extra),
	ut_flat_list([Cs_extra,Cs,Characterizing_constraints],Complete_system),!.
	
%check_obtained_constraints(Exp2,Vars,Cs,Exp_diff):-%
%		subtract_le(Exp_diff,Exp2,Exp_diff2),
%		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
%		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]).

%! get_expressions_from_points(Generators:list(generator),Lin_exps:list(nlinexp))	
% obtain a list of linear expressions from the points of a polyhedron generator system
get_expressions_from_points([],[]).	
get_expressions_from_points([point(Exp)|Generators],[Lin_exp|Lin_exps]):-!,
		parse_le(Exp,Lin_exp),
		get_expressions_from_points(Generators,Lin_exps).
get_expressions_from_points([point(Exp,Div)|Generators],[Lin_exp|Lin_exps]):-!,
		parse_le(Exp/Div,Lin_exp),
		get_expressions_from_points(Generators,Lin_exps).		
get_expressions_from_points([_|Generators],Lin_exps):-
		get_expressions_from_points(Generators,Lin_exps).			

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% predicates to deal with dmatrix (disperse matrix)
% maybe we should put it in a separate module at some point

%! get_symbolic_dmatrix(Unknowns,Dmatrix:dmatrix)
% given a list of variables, obtain a disperse vector (disperse matrix with one line) of those variables
get_symbolic_dmatrix(Unknowns,dmatrix(1,X,[(1,List)])):-
	length(Unknowns,X),
	get_symbolic_dmatrix_1(Unknowns,1,List).
	
get_symbolic_dmatrix_1([],_,[]).
get_symbolic_dmatrix_1([U|Unknowns],N,[(N,U)|List]):-
	N1 is N+1,
	get_symbolic_dmatrix_1(Unknowns,N1,List).

%! get_symbolic_dmatrix_negated(Unknowns,Dmatrix:dmatrix)
% given a list of variables, obtain a disperse vector (disperse matrix with one line) of those variables multiplied by -1			
get_symbolic_dmatrix_negated(Unknowns,dmatrix(1,X,[(1,List)])):-
	length(Unknowns,X),
	get_symbolic_dmatrix_negated_1(Unknowns,1,List).
	
get_symbolic_dmatrix_negated_1([],_,[]).
get_symbolic_dmatrix_negated_1([U|Unknowns],N,[(N,-1*U)|List]):-
	N1 is N+1,
	get_symbolic_dmatrix_negated_1(Unknowns,N1,List).



%! add_dmatrix_symbolically(Dmatrix1:dmatrix,Dmatrix2:dmatrix,Dmatrix_sum:dmatrix)
%compute the sum of two matrix simbolically
% instead of adding the values x_ij and y_ij we obtain the term: x_ij+y_ij
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


	

%! dmatrix_to_constraints(Matrix1:dmatrix,Vars:list(var),Op:operator, Matrix2:dmatrix,Cs:polyhedron)
% generate a constraint set Cs that represents
% Matrix1*Vars Op Matrix2
% with the exception of the first line that has =< operator		
dmatrix_to_constraints(dmatrix(X,Y,Vals),Vars,Op, dmatrix(1,X,[(1,Constants)]),[C|Cs]):-
	length(Vars,Y),
	(Vals=[(1,Line)|Vals_rest]->
		true;
	   Vals_rest=Vals,
	   Line=[]
	),  
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
	

get_constraints([],[(N,Constant)|Constants],N,Vars,Op,[C|Cs]):-
	parse_le(Constant,Lin_exp_right),
	integrate_le(Lin_exp_right,_Den,Lin_exp_right_int),
	write_le(Lin_exp_right_int,Cnt),
	C=..[Op,0,Cnt],
	N1 is N+1,
	get_constraints([],Constants,N1,Vars,Op,Cs).	

get_constraints([],[(N_diff,Constant)|Constants],N,Vars,Op,Cs):-
	N_diff>N,!,
	N1 is N+1,
	get_constraints([],[(N_diff,Constant)|Constants],N1,Vars,Op,Cs).			
	
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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
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

	
greater_zero(Y,1*Y>=0).
		