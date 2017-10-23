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
	difference_constraint_farkas_ub/5,
	difference_constraint_farkas_ub_leaf/6,
	difference_constraint_farkas_lb/5,
	max_min_linear_expression_list_all/6
	%difference_constraint_farkas_multiple_ub/5,
	%farkas_leaf_ub_candidate/4
	]).

:- use_module('../db',[get_input_output_vars/3]).	
:- use_module('cofloco_utils',[
			sort_with/3,
			write_le_internal/2,	
			normalize_constraint/2,
			write_sum/2]).
:- use_module('polyhedra_optimizations',[
			nad_normalize_polyhedron/2]).			
			
:- use_module(stdlib(polyhedra_ppl),[
    get_generators/4,ppl_maximize_with_point/5,ppl_minimize_with_point/5
]).

:- use_module(stdlib(numeric_abstract_domains),[nad_project/3,nad_minimize/3,nad_maximize/3,
						nad_consistent_constraints/1,
						nad_entails/3, nad_lub/6,nad_list_lub/2,
						nad_widen/5, nad_false/1,
						nad_all_ranking_functions_PR/4,
						nad_glb/3,
						nad_list_glb/2]).
:- use_module(stdlib(set_list),[from_list_sl/2,contains_sl/2,difference_sl/3]).		
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

	
difference_constraint_farkas_ub_leaf(Head,Calls,Phi,Lin_exp,(Calls2,Phi2),Lin_exp_list):-
	%get_input_output_vars(Head,Ivars,_),
	Head=..[_F|EVars],
	term_variables(Calls2,CVars),
	length(Calls2,N_calls2),
	N_calls2p is 1-N_calls2,
	obtain_entailed_cone_with_lin_exp(Phi2,[]+0,EVars,CVars,Eparams,Cparams,Cnt_param_p,Cone12,_Ys12),
	get_negated_unknowns(Calls2,Eparams,Cparams,Extra_cs),
	append(Extra_cs,Cone12,Cone12_complete),
	nad_project([Cnt_param|Eparams],[N_calls2p*Cnt_param=Cnt_param_p|Cone12_complete],Cone12_projected),
	difference_constraint_farkas_ub_with_extra_cone(Head,Calls,Phi,Lin_exp,(Eparams,Cnt_param,Cone12_projected),Lin_exp_list).
	
difference_constraint_farkas_ub(Head,Calls,Phi,Lin_exp,Lin_exp_list):-
	difference_constraint_farkas_ub_with_extra_cone(Head,Calls,Phi,Lin_exp,(_,_,[]),Lin_exp_list).

% this is the generic predicate for upper bound candidates
difference_constraint_farkas_ub_with_extra_cone(Head,Calls,Phi,Lin_exp,(Eparams,Cnt_param,Cone3),Lin_exp_list):-
	get_input_output_vars(Head,Ivars,_),
	Head=..[F|EVars],
	term_variables(Calls,CVars),
	length(Calls,N_calls),
	N_calls1 is 1-N_calls,
	append(EVars,CVars,Vars),
	le_print_int(Lin_exp,Exp,_Den),
	negate_le(Lin_exp,Lin_exp_neg),
	(N_calls=0->
	    Cone11=[],Ys11=[],Cparams=[],Extra_cs=[]
	    ;
		obtain_entailed_cone_with_lin_exp([Exp>=0|Phi],Lin_exp_neg,EVars,CVars,Eparams,Cparams,Cnt_param_p,Cone11,Ys11),
		get_negated_unknowns(Calls,Eparams,Cparams,Extra_cs)
	),
    % if we have x+c >= (x'+c)+(x''+c) the constant factor is Cnt_param_p=c*(1-n) where n is the number of recursive calls
    % and c=Cnt_param, the real constant factor

    nad_glb([N_calls1*Cnt_param=Cnt_param_p,Cnt_param2=Cnt_param|Cone11],Extra_cs,Cone11_extra),
	obtain_entailed_cone_with_lin_exp(Phi,Lin_exp_neg,EVars,CVars,Eparams,Cparams2,Cnt_param2,Cone2,Ys2),
	
	(\+nad_entails(Vars,Phi,[Exp>=0])->
		obtain_entailed_cone_with_lin_exp([Exp=<0|Phi],[]+0,EVars,CVars,Eparams,Cparams,Cnt_param_p,Cone12,Ys12),
		append([N_calls1*Cnt_param=Cnt_param_p|Extra_cs],Cone12,Cone12_complete),
		nad_project([Cnt_param|Eparams],Cone12_complete,Cone12_projected),
		nad_glb(Cone11_extra,Cone12_projected,Cone1)
	;
	  	Cone1=Cone11_extra,
	  	Ys12=[]
	),
	Head_params=..[F|Eparams],
	get_input_output_vars(Head_params,IEparams,OEparams),
	maplist('='(0),OEparams),
	maplist('='(0),Cparams2),
	nad_glb(Cone1,Cone2,Cone_joint),
	nad_glb(Cone_joint,Cone3,Cone_total),
	ut_flat_list([Cnt_param_p,Cnt_param2,Ys11,Ys12,Ys2],Extra_params),
	ut_flat_list([IEparams,Cparams,Cnt_param,Extra_params],All_vars),
	(nad_consistent_constraints(Cone_total)->
		get_generators(c,All_vars,Cone_total,Generators)
		;
		get_generators(c,All_vars,Cone_joint,Generators)
	),
	%once we have the point, we can set all the coefficients variables to 0 and obtain the point in terms of Unknowns
	maplist(=(0),Extra_params),
	maplist(=(0),Cparams),
	Cnt_param=1,
	%extract the linear expressions from the points
	%copy_term((Head_params,Generators),(Head,Generators_copy)),	
	copy_term((IEparams,Generators),(Ivars,Generators_copy)),	
	get_expressions_from_points(Generators_copy,Lin_exp_list).
 
 difference_constraint_farkas_lb(Head,Calls,Phi,Lin_exp,Lin_exp_list_final):-
	get_input_output_vars(Head,Ivars,_),
	Head=..[F|EVars],
	term_variables(Calls,CVars),
	length(Calls,N_calls),
	N_calls1 is 1-N_calls,
	append(EVars,CVars,Vars),
	le_print_int(Lin_exp,Exp,_Den),
	obtain_entailed_cone_with_lin_exp([Exp>=0|Phi],Lin_exp,EVars,CVars,Eparams,Cparams,Cnt_param_p,Cone11,Ys11),
	get_negated_unknowns(Calls,Eparams,Cparams,Extra_cs),
    % if we have x+c >= (x'+c)+(x''+c) the constant factor is Cnt_param_p=c*(1-n) where n is the number of recursive calls
    % and c=Cnt_param, the real constant factor
    nad_glb([N_calls1*Cnt_param=Cnt_param_p,Cnt_param2=Cnt_param|Cone11],Extra_cs,Cone11_extra),	
	(\+nad_entails(Vars,Phi,[Exp>=0])->
		obtain_entailed_cone_with_lin_exp([Exp=<0|Phi],[]+0,EVars,CVars,Eparams,Cparams,Cnt_param_p,Cone12,Ys12),
		append([N_calls1*Cnt_param=Cnt_param_p|Extra_cs],Cone12,Cone12_complete),
		nad_project([Cnt_param|Eparams],Cone12_complete,Cone12_projected),
		nad_glb(Cone11_extra,Cone12_projected,Cone1)
	;
	  	Cone1=Cone11_extra,
	  	Ys12=[]
	),
	Head_params=..[F|Eparams],
	get_input_output_vars(Head_params,IEparams,OEparams),
	maplist('='(0),OEparams),
	ut_flat_list([Cnt_param_p,Cnt_param2,Ys11,Ys12],Extra_params),
	%ut_flat_list([IEparams,Cparams,Cnt_param,Extra_params],All_vars),
	nad_project([Cnt_param|Eparams],Cone1,Cone1_proj),
	get_generators(c,[Cnt_param|Eparams],Cone1_proj,Generators),
	%once we have the point, we can set all the coefficients variables to 0 and obtain the point in terms of Unknowns
	maplist(=(0),Extra_params),
	maplist(=(0),Cparams),
	Cnt_param= 1,
	%extract the linear expressions from the points
	%copy_term((Head_params,Generators),(Head,Generators_copy)),	
	copy_term((IEparams,Generators),(Ivars,Generators_copy)),	
	get_expressions_from_points(Generators_copy,Lin_exp_list),
	maplist(negate_le,Lin_exp_list,Lin_exp_list_final).
	
get_sum_exp_calls(Head,Lin_exp,Call,Accum,Accum2):-
	copy_term((Head,Lin_exp),(Call,Lin_exp2)),
	sum_le(Accum,Lin_exp2,Accum2).
	
max_min_linear_expression_list_all(Lin_exps,Vars,Vars_of_interest,Phi_1,max,Lin_exp_set):-
	nad_normalize_polyhedron(Phi_1,Phi),
	maplist(negate_le,Lin_exps,Lin_exps_neg),
	maplist(get_max_cone(Phi,Vars,Params,Cnt_param),Lin_exps_neg,Cones,Yss),
	nad_list_glb(Cones,Cs),
	ut_flat_list(Yss,Extra_params),
	copy_term((Vars,Vars_of_interest),(Params,Params_of_interest)),
	from_list_sl(Params,Params_set),
	from_list_sl(Params_of_interest,Params_of_interest_set),
	difference_sl(Params_set,Params_of_interest_set,Zero_coeffs),
	maplist(=(0),Zero_coeffs),	
	append([Cnt_param|Params],Extra_params,All_vars),
	get_generators(c,All_vars,Cs,Generators),
	Cnt_param=1,
	maplist(=(0),Extra_params),	
	copy_term((Params_of_interest,Generators),(Vars_of_interest,Generators_copy)),	
	get_expressions_from_points(Generators_copy,Lin_exp_list),
	from_list_sl(Lin_exp_list,Lin_exp_set).

get_max_cone(Phi,Vars,Params,Cnt_param,Lin_exp,Cone,Ys):-	
	obtain_entailed_cone_with_lin_exp(Phi,Lin_exp,Vars,[],Params,[],Cnt_param,Cone,Ys).
	

le_print_int(Lin_exp,Exp,Den):-
		integrate_le(Lin_exp,Den,Lin_exp_nat),
		write_le_internal(Lin_exp_nat,Exp).

get_negated_unknowns([],_,[],[]).
get_negated_unknowns([_Call|Calls],Unknowns_head,Vars1,Characterizing_constraints1):-
	get_negated_unknowns(Calls,Unknowns_head,Vars,Characterizing_constraints),
	length(Unknowns_head,N),
	length(Unknowns_call,N),
	maplist(negation_constr,Unknowns_head,Unknowns_call,Characterizing_constraints_new),
	append(Unknowns_call,Vars,Vars1),
	append(Characterizing_constraints_new,Characterizing_constraints,Characterizing_constraints1).

obtain_entailed_cone_with_lin_exp(Phi,Lin_exp,EVars,CVars,Eparams,Cparams,Cnt_param,Cone,Ys):-
	append(EVars,CVars,Vars),
	copy_term(EVars,Eparams),
	copy_term(CVars,Cparams),
	append([Cnt_param|Eparams],Cparams,Params),
	get_symbolic_dmatrix(Params,Template),
	get_lin_expr_dmatrix(Vars,Lin_exp,Coeffs),
	add_dmatrix_symbolically(Template,Coeffs,Expression_vector),
	generalized_farkas_property_dmatrix(Vars,Phi,Expression_vector,system(Cone,Ys)).
	
%! generalized_farkas_property_dmatrix(Vars:list(var),Phi:polyhedron,Expression_vector:dvector,System:system(polyhedron,list(var)))
% given a polyhedron Phi and a property Expressions_vector>=0 generate a polyhedron
% that represent the linear combinations of the constraints of Phi to obtain Expression_vector
% The variables Ys are the coefficients that multiply the constraints of Phi
generalized_farkas_property_dmatrix(Vars,Phi,Expression_vector,system(Complete_system,Ys)):-
	constraints_to_dmatrix(Phi,Vars,A),
	transpose_dmatrix(A,At),
	get_dmatrix_y_dimension(At,M),
	length(Ys,M),	
	dmatrix_to_constraints( At,Ys,'=', Expression_vector,Cs),
	maplist(greater_zero,Ys,Cs_extra),
	append(Cs_extra,Cs,Complete_system),!.
	
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
		