/** <module> constraints_maximization

This module implements algorithms to maximize sets of constraints 
according to a polyhedron describing the relations between variables.
The module includes predicates to compress sets of constraints
 at the same time they are maximized. 
 
It is used in  cost_equation_solver.pl and chain_solver.pl.

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

:- module(constraints_maximization,[
				  max_min_constrs_in_cost_equation/6,
				  max_min_top_exprs_in_chain/6,
				  max_min_linear_expression_all/5]).
				  
:- use_module('../IO/params',[get_param/2]).
:- use_module('../db',[phase_loop/5]).
:- use_module('../utils/cofloco_utils',[
			tuple/3,
			sort_with/3,
			repeat_n_times/3,
			normalize_constraint/2,
			normalize_constraint_wrt_var/3,	
			normalize_constraint_wrt_vars/3,	    
			write_sum/2]).
		
:- use_module('../utils/polyhedra_optimizations',[
			nad_entails_aux/3,nad_normalize_polyhedron/2,
			slice_relevant_constraints_and_vars/5]).			

:- use_module('../utils/cost_structures',[
			cstr_generate_top_exp/4]).			
					
:- use_module(stdlib(linear_expression),[
	is_constant_le/1,
	integrate_le/3,
	write_le/2,
	parse_le_fast/2,
	elements_le/2,
	constant_le/2]).
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map)).
:- use_module(stdlib(numeric_abstract_domains),[nad_project/3,nad_entails/3]).								
:- use_module(stdlib(fraction),[greater_fr/2]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).		
	

%! max_min_constrs_in_cost_equation(+FCons_list:list(list(final_constr)),+Base_calls:list(term),Phi:polyhedron,TVars:list(Var),FCons_out:list(final_cons),ICons_out:list(inter_cons)) is det
% transform a list of lists of final constraints from a cost equation
% into a simple list of final constraints expressed in terms of TVars using max_min_constrs/4
%
% It is prepared to originate intermediate constraints as well but not used yet
max_min_constrs_in_cost_equation(Top_exps_list,_Base_calls,Phi,TVars,Final_tops,[]):-
	ut_flat_list(Top_exps_list,Top_exps),
	max_min_constrs(Top_exps,Phi,TVars,Final_tops).
	
%! max_min_constrs_in_cost_equation(+FCons:list(final_constr),+Chain:chain,Phi:polyhedron,TVars:list(Var),FCons_out:list(final_cons),ICons_out:list(inter_cons)) is det
% transform a list of final constraints from two phases
% into a simple list of final constraints expressed in terms of TVars using max_min_constrs/4	
%
% It is prepared to originate intermediate constraints as well but not used yet
max_min_top_exprs_in_chain(Top_exps,_Chain,Phi,Head,Final_tops,[]):-
	term_variables(Head,TVars),
	max_min_constrs(Top_exps,Phi,TVars,Final_tops).
	
%! max_min_constrs(+FCons_list:list(final_constr),Phi:polyhedron,TVars:list(Var),FCons_out:list(final_cons)) is det
% transform a list of final constraints into a simple list of final constraints expressed in terms of TVars using the information in Phi
% * The final_cons that are guaranteed to be positive are transformed together
% * The rest (the insecure constraints) are transformed one by one			
max_min_constrs(Top_exps,Phi,TVars,Final_tops):-
	(Top_exps=[bound(ub,_,_)|_]-> Max_min=max;Max_min=min),	
	% separate positive constraints and insecure constraints
	generate_constraints(Top_exps,Phi,[],Constraints,Insecure_constraints,Dicc),
	% combine positive constraints
	maplist(tuple,_Names_set,Extra_vars,Dicc),
	from_list_sl(Extra_vars,Extra_vars_set),
	foldl(inverse_map,Dicc,[],Dicc_inv),
	append(Constraints,Phi,Phi1),
	append(Extra_vars,TVars,Total_vars),
	nad_project(Total_vars,Phi1,Projected),
	cstr_generate_top_expr_from_poly(Projected,Max_min,Dicc_inv,Extra_vars_set,New_top_exps),
	% transform insecure constraints
	maplist(maximize_insecure_constraints(Total_vars,Phi,Max_min),Insecure_constraints,Extra_tops),
	% put the result together
	ut_flat_list([Extra_tops,New_top_exps],Final_tops).
	

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

generate_constraints([],_,Dicc,[],[],Dicc).
generate_constraints([bound(Op,Lin_exp,Bounded)|More],Phi,Dicc,Constraints2,Non_secure2,Dicc_out):-
	foldl(insert_in_dicc,Bounded,(Dicc,[]),(Dicc1,Var_list)),
	write_sum(Var_list,Sum),
	(Op=ub->
		(is_constant_le(Lin_exp)->
			Non_secure2=[Bounded =< Lin_exp|Non_secure],
			Constraints2=Constraints
		;
		term_variables((Phi,Lin_exp),Vars),
		integrate_le(Lin_exp,Den,Lin_exp_nat),
		write_le(Lin_exp_nat,Expression_nat),
		(\+nad_entails_aux(Vars,Phi,[Expression_nat >=0])->
			Non_secure2=[Bounded =< Lin_exp|Non_secure],
			Constraints2=Constraints
			;
			Non_secure2=Non_secure,		
			Constraints2=[Sum *Den=< Expression_nat|Constraints]
		)
		)
	;
	
	((is_constant_le(Lin_exp))->
			Non_secure2=[Bounded >= Lin_exp|Non_secure],
			Constraints2=Constraints
			;
			term_variables((Phi,Lin_exp),Vars),
			integrate_le(Lin_exp,Den,Lin_exp_nat),
			write_le(Lin_exp_nat,Expression_nat),
			(\+nad_entails_aux(Vars,Phi,[Expression_nat >=0])->	
			Non_secure2=[Bounded >= Lin_exp|Non_secure],
			Constraints2=Constraints
			;
			Non_secure2=Non_secure,		
			Constraints2=[Sum *Den>= Expression_nat|Constraints]
		)
	)
	),
	generate_constraints(More,Phi,Dicc1,Constraints,Non_secure,Dicc_out).
	

inverse_map((Name,Var),Dicc_inv,Dicc_inv1):-
	insert_lm(Dicc_inv,Var,Name,Dicc_inv1).

insert_in_dicc(Elem,(Dicc,Var_list),(Dicc,[Var|Var_list])):-
	lookup_lm(Dicc,Elem,Var),!.
insert_in_dicc(Elem,(Dicc,Var_list),(Dicc1,[Var|Var_list])):-
	insert_lm(Dicc,Elem,Var,Dicc1).
	
cstr_generate_top_expr_from_poly(Projected,Max_min,Dicc,Extra_vars,New_top_exps2):-
	get_linear_norms_from_constraints(Projected,Max_min,Extra_vars,Norms),
	maplist(get_top_exp_from_norm(Dicc,Max_min),Norms,New_top_exps),
	limit_top_expression_selection(New_top_exps,Max_min,Dicc,New_top_exps2).
	
limit_top_expression_selection(Top_exps,Max_min,Dicc,Top_exps2):-
	sort_with(Top_exps,worse_top_exp,Sorted_top_exps),
	(Max_min=max->
		Sorted_top_exps1=Sorted_top_exps
	;
		reverse(Sorted_top_exps,Sorted_top_exps1)
	),
	(get_param(maximize_fast,[N]);N=1),
	length(Dicc,N_vars),
	repeat_n_times(N_vars,N,Counters),
	maplist(tuple,_,Vars,Dicc),
	from_list_sl(Vars,Vars_set),
	maplist(tuple,Vars_set,Counters,Counters_dicc),
	get_filtered_top_exps(Sorted_top_exps1,Counters_dicc,Top_exps2).

%constant comparison
worse_top_exp(bound(_,Exp1,_),bound(_,Exp2,_)):-
	is_constant_le(Exp1),is_constant_le(Exp2),
	constant_le(Exp1,C1),constant_le(Exp2,C2),!,
	greater_fr(C1,C2),!.	
worse_top_exp(bound(_,Exp1,Bounded),bound(_,Exp2,Bounded2)):-
	is_constant_le(Exp1),is_constant_le(Exp2),
	constant_le(Exp1,C1),constant_le(Exp2,C2),!,
	C1=C2,!,
	length(Bounded,N1),
	length(Bounded2,N2),
	N2 > N1.	
%constant to non-constant	  
worse_top_exp(bound(_,Exp1,_),bound(_,Exp2,_)):-
	\+is_constant_le(Exp1),is_constant_le(Exp2),!.	
%non-costant comparison
worse_top_exp(bound(_,Exp1,Bounded),bound(_,Exp2,Bounded2)):-
	\+is_constant_le(Exp1),\+is_constant_le(Exp2),
	length(Bounded,N1),
	length(Bounded2,N2),
	N2 > N1.
	
update_ub_counters([],_,[],[]).
update_ub_counters(Counters,[],[],Counters):-!.
update_ub_counters([(Loop,N)|Cnts],[Loop|Loops],Excluded,Counters):-!,
	N1 is N-1,
	(N1 > 0-> 
	   Counters=[(Loop,N1)|Counters_aux],
	   Excluded=Excluded1
	   ;
	   Counters=Counters_aux,
	   Excluded=[Loop|Excluded1]
	   ),
	update_ub_counters(Cnts,Loops,Excluded1,Counters_aux).
update_ub_counters([(Loop,N)|Cnts],[Loop2|Loops],Excluded,[(Loop,N)|Counters_aux]):-
	Loop @< Loop2,!,
	update_ub_counters(Cnts,[Loop2|Loops],Excluded,Counters_aux).	
	
update_ub_counters([(Loop,N)|Cnts],[Loop2|Loops],Excluded,Counters_aux):-
	Loop @> Loop2,
	update_ub_counters([(Loop,N)|Cnts],Loops,Excluded,Counters_aux).		
	
get_filtered_top_exps([],_,[]):-!.
get_filtered_top_exps(_,[],[]):-!.
get_filtered_top_exps([bound(Op,Exp,Bounded)|Tops],Counters,[bound(Op,Exp,Bounded)|Selected]):-
		update_ub_counters(Counters,Bounded,Excluded,Counters2),
		from_list_sl(Excluded,Excluded_set),
		filter_tops_with_excluded(Tops,Excluded_set,Tops2),
		get_filtered_top_exps(Tops2,Counters2,Selected).

filter_tops_with_excluded([],_,[]).
filter_tops_with_excluded([bound(Op,Exp,Bounded)|Tops],Excluded,Tops1):-
	difference_sl(Bounded,Excluded,Bounded1),
	(Bounded1=[]->
	Tops1=Tops2
	;
	Tops1=[bound(Op,Exp,Bounded1)|Tops2]
	),
	filter_tops_with_excluded(Tops,Excluded,Tops2).
		
get_top_exp_from_norm(Dicc,max,norm(Its,Lin_exp),bound(ub,Lin_exp,Bounded)):-
	foldl(substitute_its_by_bounded(Dicc),Its,[],Bounded).	
get_top_exp_from_norm(Dicc,min,norm(Its,Lin_exp),bound(lb,Lin_exp,Bounded)):-
	foldl(substitute_its_by_bounded(Dicc),Its,[],Bounded).		

substitute_its_by_bounded(Dicc,It_var,Accum,[Elem|Accum]):-
	lookup_lm(Dicc,It_var,Elem).
	
get_linear_norms_from_constraints([],_Max_min,_,[]).
get_linear_norms_from_constraints([C|Cs],max,Its_total,Norms):-
	normalize_constraint_wrt_vars(C,Its_total,C1),!,
	(C1= (Its =< Exp)->
		parse_le_fast(Exp,Lin_exp),
		Norms=[norm(Its,Lin_exp)|Norms_aux]
		;
		Norms=Norms_aux
	),
	get_linear_norms_from_constraints(Cs,max,Its_total,Norms_aux).
	
get_linear_norms_from_constraints([C|Cs],min,Its_total,Norms):-
	normalize_constraint_wrt_vars(C,Its_total,C1),!,
	(C1= (Its >= Exp)->
		parse_le_fast(Exp,Lin_exp),
		Norms=[norm(Its,Lin_exp)|Norms_aux]
		;
		Norms=Norms_aux
	),
	get_linear_norms_from_constraints(Cs,min,Its_total,Norms_aux).	
	
get_linear_norms_from_constraints([_C|Cs],Max_min,Its_total,Norms):-
	get_linear_norms_from_constraints(Cs,Max_min,Its_total,Norms).
	
	
maximize_insecure_constraints(Vars,Phi,Max_Min,Bounded=<Linear_Expr_to_Maximize,Tops):-
	(Max_Min=max-> Op=ub;Op=lb),
	elements_le(Linear_Expr_to_Maximize,Relevant_vars_ini),
	slice_relevant_constraints_and_vars(Relevant_vars_ini,Vars,Phi,_Selected_vars,Selected_Cs),
	max_min_linear_expression_all(Linear_Expr_to_Maximize, Vars, Selected_Cs,Max_Min, Maxs),
	maplist(cstr_generate_top_exp(Bounded,Op),Maxs,Tops).
maximize_insecure_constraints(Vars,Phi,Max_Min,Bounded >= Linear_Expr_to_Maximize,Tops):-
	(Max_Min=max-> Op=ub;Op=lb),
	elements_le(Linear_Expr_to_Maximize,Relevant_vars_ini),
	slice_relevant_constraints_and_vars(Relevant_vars_ini,Vars,Phi,_Selected_vars,Selected_Cs),
	max_min_linear_expression_all(Linear_Expr_to_Maximize, Vars, Selected_Cs,Max_Min, Maxs),
	maplist(cstr_generate_top_exp(Bounded,Op),Maxs,Tops).
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
	
%! maximize_linear_expression_all(+Linear_Expr_to_Maximize:linear_expression,+Vars_of_Interest:list(var),+Context:polyhedron, -Maxs:list(linear_expression)) is det
% This predicate obtains a list of linear expressions Maxs that are an upper bound of Linear_Expr_to_Maximize
% according to Context and are only expressed in terms of Vars_of_Interest.
% The length of Maxs is limited by the input parameter -maximize_fast N.
% If no upper bound is found, the predicate returns an empty list.
max_min_linear_expression_all(Number,_,_,_, [Number]) :-
	is_constant_le(Number),!.

/*	
max_min_linear_expression_all(Linear_Expr_to_Maximize, Vars_of_Interest, Context,max, [Exp_diff_1]) :-
	copy_term((Vars_of_Interest,Linear_Expr_to_Maximize, Context),(Vars_of_Interest2,Linear_Expr_to_Maximize2, Context2)),
	term_variables((Vars_of_Interest2,Linear_Expr_to_Maximize2, Context2),Vars),
	max_min_linear_expression_template(Linear_Expr_to_Maximize2,Vars, Vars_of_Interest2, Context2, [Maxs_out]),
	Exp_diff_1=Maxs_out,
	Vars_of_Interest=Vars_of_Interest2,!.
*/		

max_min_linear_expression_all(Lin_exp, Vars_of_Interest, _Context,_Max_min, Lin_exp_out) :-
	term_variables(Lin_exp,Vars),
	from_list_sl(Vars_of_Interest,Interest_set),
	from_list_sl(Vars,Vars_set),
	difference_sl(Vars_set,Interest_set,[]),!,
	Lin_exp_out=[Lin_exp].
	

max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,Max_min, Lin_exp_out) :-
	(get_param(maximize_fast,[N])->
		true
		;
		N=1),
	integrate_le(Lin_exp,Den,Lin_exp_nat),
	write_le(Lin_exp_nat,Expression),
	Constraint= (Den*R = Expression),	
	max_min_linear_expression_all_n(N,R, Vars_of_Interest, [Constraint|Context],Max_min, Maxs_out),
	maplist(parse_le_fast,Maxs_out,Lin_exp_out).
	

max_min_linear_expression_all_n(N,R, Vars_of_Interest, Context,Max_Min,Maxs_out) :-
	% Polyhedral projection so Cs is expressed in terms of Vars_of_Interest and R
	nad_project([R|Vars_of_Interest],Context,Cs),
	% Extract upper bound sintactically
	extract_all_possible(Cs, R, Max_Exprs),
	get_right_sides(Max_Exprs,Max_Min,Maxs),
	from_list_sl(Maxs,Maxs_set),
	length(Maxs_set,Curr_length),
	Rest is N-Curr_length,
	% If we have not inferred enough upper bounds
	(Rest > 0 ->
	term_variables(Maxs,Used_vars),
	from_list_sl(Used_vars,Used_vars_set),
	from_list_sl(Vars_of_Interest,Vars_of_Interest_set),
	(Used_vars_set=[Elem|_]->
	%remove a variable from the variables of interest
	   difference_sl(Vars_of_Interest_set,[Elem],Vars_of_Interest1),
	%and try to obtain new expressions with a recursive call
	   max_min_linear_expression_all_n(Rest,R,Vars_of_Interest1,Cs,Max_Min,Maxs1),
	   union_sl(Maxs1,Maxs_set,Maxs_out)
	   ;
	   Maxs_out=Maxs_set
	 ),!
	 ;
	 %if we too many upper bounds, take the first N ones
	   ut_split_at_pos(Maxs_set,N,Maxs_out,_)
	 ).

%! extract_all_possible(+Cs:list(linear_constraint),+R:var,-M:list(linear_constraints)) is det
% express all the constraints in Cs that contain R as R rel_op	C0+C1*X1+...+CN*XN
% where rel_op in [=<,>=,=].
extract_all_possible([],_,[]).
extract_all_possible([C|Cs],R,Ms) :-
	( normalize_constraint_wrt_var(C,R,M) -> 
	    Ms = [M|Ms_aux] 
	    ; 
	    Ms = Ms_aux 
	),
	extract_all_possible(Cs,R,Ms_aux).
	
%! get_right_sides(+Es:list(linear_constraint),-Maxs:list(linear_expression)) is det
% collect all linear expressions Max such that _=<Max is in Es.
% If there is one constraint _=Max, we only get such linear expression.
get_right_sides(Es,_,[Max]):-
	member(_=Max,Es),!.
		
get_right_sides(Es,Max_Min,Maxs):-
	get_right_sides_1(Es,Max_Min,Maxs).
	
get_right_sides_1([],_,[]).
get_right_sides_1([_=<Max|Es],max,[Max|Maxs]):-!,
	get_right_sides_1(Es,max,Maxs).
get_right_sides_1([_>= Min|Es],min,[Min|Maxs]):-!,
	get_right_sides_1(Es,min,Maxs).	
	
get_right_sides_1([_|Es],Max_Min,Maxs):-
	get_right_sides_1(Es,Max_Min,Maxs).	
	

/*
% this in an alternative implementation to detect due to which calls the transformation loses information

maximize_top_expressions_in_cost_equation(Top_exps_list,Base_call_vars,Phi,TVars,New_tops,New_auxs):-
	from_list_sl(TVars,TVars_set),
	unions_sl([TVars_set|Base_call_vars],All_vars),
	incremental_maximization_cost_equation(Top_exps_list,Base_call_vars,carry_info([],[]),All_vars,Phi,New_tops,New_auxs).

incremental_maximization_cost_equation([],[],carry_info(Dicc_inv,Extra_vars_set),_Vars,Phi,New_top_exps,[]):-
	cstr_generate_top_expr_from_poly(Phi,Dicc_inv,Extra_vars_set,New_top_exps).

incremental_maximization_cost_equation([Top_exps|Top_exp_list],[Base_vars|Base_vars_list],
										Carry_info,Vars,Phi,New_top_exps,[]):-
	Carry_info=carry_info(Dicc_inv,Extra_vars_set),
	generate_constraints(Top_exps,[],Constraints,Dicc1),
	maplist(tuple,_Names_set1,Extra_vars1,Dicc1),
	from_list_sl(Extra_vars1,Extra_vars_set1),
	foldl(inverse_map,Dicc1,[],Dicc_inv1),
	append(Constraints,Phi,Phi1),
	difference_sl(Vars,Base_vars,Vars1),
	unions_sl([Extra_vars_set1,Extra_vars_set,Vars1],Total_vars),
	nad_project(Total_vars,Phi1,Projected),
	check_lost_bounds(Projected,Extra_vars_set,Lost_vars),
	(Lost_vars\=[]->
		throw(lost_expressions),
		%get_needed_expressions(Lost_vars,Phi,Base_vars,Expressions),
		writeln(lost_expressions(Lost_vars,Dicc_inv))
	;
		true
		),
	update_carry_info(Carry_info,Extra_vars_set1,Dicc_inv1,Carry_info1),
	incremental_maximization_cost_equation(Top_exp_list,Base_vars_list,Carry_info1,Vars1,Projected,New_top_exps,[]).

update_carry_info(carry_info(Dicc,Var_set),Var_set1,Dicc1,carry_info(Dicc2,Var_set2)):-
	union_sl(Var_set,Var_set1,Var_set2),
	join_lm(Dicc,Dicc1,Dicc2).

check_lost_bounds([],Lost_vars,Lost_vars):-!.
check_lost_bounds(_,[],[]):-!.
check_lost_bounds([C|Cs],Vars,Lost_vars):-
	normalize_constraint_wrt_vars(C,Vars,C1),!,
	(C1= (Its =< _Exp)->
		from_list_sl(Its,Its_set),
		difference_sl(Vars,Its_set,Vars1)
		;
		Vars1=Vars
	),
	check_lost_bounds(Cs,Vars1,Lost_vars).
	
check_lost_bounds([_C|Cs],Vars,Lost_vars):-
	check_lost_bounds(Cs,Vars,Lost_vars).
*/
