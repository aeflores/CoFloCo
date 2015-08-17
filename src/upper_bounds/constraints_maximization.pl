/** <module> constraints_maximization

This module implements algorithms to maximize sets of constraints 
according to a polyhedron describing the relations between variables.
The module includes predicates to compress sets of constraints
 at the same time they are maximized. 
 
It is used in the cost_equation_solver.pl, the phase_solver.pl
 and the chain_solver.pl.

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
				  max_min_costs_in_phase/6,
				  max_min_linear_expression_all/5]).
				  
:- use_module('../IO/params',[get_param/2]).
:- use_module('../db',[loop_ph/6,phase_loop/5]).
:- use_module('../utils/cofloco_utils',[
	        zip_with_op/4,
			tuple/3,
			sort_with/3,
			repeat_n_times/3,
			normalize_constraint/2,
			normalize_constraint_wrt_var/3,	
			normalize_constraint_wrt_vars/3,	    
			write_sum/2]).
				
:-use_module('../refinement/invariants',[backward_invariant/4,
			      phase_transitive_closure/5,
			      get_phase_star/4,
			      forward_invariant/4]).			
:- use_module('../utils/polyhedra_optimizations',[nad_entails_aux/3,
			slice_relevant_constraints_and_vars/5,nad_project_group/3,
			nad_consistent_constraints_group/2]).			

:- use_module('../utils/cost_expressions',[cexpr_maximize/4,
			get_le_without_constant/3,
			cexpr_substitute_lin_exp_by_vars/4,
			normalize_le/2,
			is_linear_exp/1]).
:- use_module('../utils/cost_structures',[
			cstr_remove_cycles/2,
			cstr_name_aux_var/1,
			cstr_get_it_name/2,
			cstr_propagate_summatory/4,
			cstr_generate_top_exp/4,
			cstr_generate_top_exp_inv/4,
			cstr_empty/1,
			cstr_get_lin_exp_from_tops/3,
			cstr_join/3]).			
:-use_module('../utils/template_inference',[difference_constraint/5,difference_constraint2/5]).			
:- use_module(constraints_generation,[add_phase_upper_bounds/6,add_phase_lower_bounds/6]).			
:- use_module(stdlib(counters),[counter_increase/3]).

:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map)).
:- use_module(stdlib(multimap)).
:- use_module(stdlib(numeric_abstract_domains),[nad_maximize/3,nad_minimize/3,
						nad_list_lub/2,
						nad_project/3,nad_entails/3,nad_normalize/2,
						nad_consistent_constraints/1]).
:- use_module(stdlib(linear_expression),[is_constant_le/1,
	integrate_le/3,
	write_le/2,
	parse_le_fast/2,
	elements_le/2,
	subtract_le/3,
	constant_le/2]).							
:- use_module(stdlib(fraction),[greater_fr/2,geq_fr/2,negate_fr/2,multiply_fr/3]).
:- use_module(stdlib(fraction_list),[max_frl/2,min_frl/2]).
				
%/*										
max_min_constrs_in_cost_equation(Top_exps_list,_Base_calls,Phi,TVars,Final_tops,[]):-
	ut_flat_list(Top_exps_list,Top_exps),
	(Top_exps=[bound(ub,_,_)|_]-> Max_min=max;Max_min=min),	
	generate_constraints(Top_exps,Phi,[],Constraints,Insecure_constraints,Dicc),
	maplist(tuple,_Names_set,Extra_vars,Dicc),
	from_list_sl(Extra_vars,Extra_vars_set),
	foldl(inverse_map,Dicc,[],Dicc_inv),
	append(Constraints,Phi,Phi1),
	append(Extra_vars,TVars,Total_vars),
	nad_project(Total_vars,Phi1,Projected),
	maplist(maximize_insecure_constraints(Total_vars,Phi,Max_min),Insecure_constraints,Extra_tops),
	cstr_generate_top_expr_from_poly(Projected,Max_min,Dicc_inv,Extra_vars_set,New_top_exps),
	ut_flat_list([Extra_tops,New_top_exps],Final_tops).
%*/

/*
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
	
max_min_top_exprs_in_chain(Top_exps,_Chain,Phi,Head,Final_tops,[]):-
	(Top_exps=[bound(ub,_,_)|_]-> Max_min=max;Max_min=min),	
	term_variables(Head,TVars),
	generate_constraints(Top_exps,Phi,[],Constraints,Insecure_constraints,Dicc),
	maplist(tuple,_Names,Extra_vars,Dicc),
	from_list_sl(Extra_vars,Extra_vars_set),
	foldl(inverse_map,Dicc,[],Dicc_inv),
	append(Constraints,Phi,Phi1),
	append(Extra_vars,TVars,Total_vars),	
	nad_project(Total_vars,Phi1,Projected),
	maplist(maximize_insecure_constraints(TVars,Phi,Max_min),Insecure_constraints,Extra_tops),
	cstr_generate_top_expr_from_poly(Projected,Max_min,Dicc_inv,Extra_vars_set,New_top_exps),
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
	
	(is_constant_le(Lin_exp)->
			Non_secure2=[Bounded >= Lin_exp|Non_secure],
			Constraints2=Constraints
			;
			integrate_le(Lin_exp,Den,Lin_exp_nat),
			write_le(Lin_exp_nat,Expression_nat),
			Constraints2=[Sum* Den>= Expression_nat|Constraints],
			Non_secure2=Non_secure
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

worse_top_exp(bound(_,Exp1,_),bound(_,Exp2,_)):-
	is_constant_le(Exp1),is_constant_le(Exp2),
	constant_le(Exp1,C1),constant_le(Exp2,C2),!,
	greater_fr(C1,C2).
worse_top_exp(bound(_,Exp1,_),bound(_,Exp2,_)):-
	\+is_constant_le(Exp1),is_constant_le(Exp2),!.	
worse_top_exp(bound(_,_Exp1,Bounded),bound(_,_Exp2,Bounded2)):-
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

maximize_insecure_constraints(_Vars,_Phi,Max_Min,Bounded >= []+Cnt,Tops):-
	(Max_Min=max-> Op=ub;Op=lb),
	maplist(cstr_generate_top_exp(Bounded,Op),[[]+Cnt],Tops).			
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
	
max_min_costs_in_phase(Costs,Head,Call,Forward_inv,Phase,Cost_final):-
	add_phase_upper_bounds(Head,Call,Phase,_,Top_exps_new,Aux_exps_new),
	add_phase_lower_bounds(Head,Call,Phase,_,LTop_exps_new,LAux_exps_new),
	

	maplist(cstr_remove_cycles,Costs,Costs_simple),
	maplist(cstr_propagate_summatory,Phase,Costs_simple,Costs_propagated,Summatories_pairs),
	maplist(tuple,Summatories,LSummatories,Summatories_pairs),
	maplist(max_min_top_expressions_in_loop(Head,Call,Phase,Forward_inv),Phase,Costs_propagated,Costs_maximized),
	compute_summatories(Head,Call,Phase,Forward_inv,Summatories,Top_exps2,Aux_exps2),
	compute_summatories(Head,Call,Phase,Forward_inv,LSummatories,LTop_exps2,LAux_exps2),
	cstr_empty(Empty_cost),
	foldl(cstr_join,Costs_maximized,Empty_cost,cost(Top_exps,LTop_exps,Aux_exps,Bases,Base)),
	ut_flat_list([Top_exps_new,Top_exps2,Top_exps],Top_exps_final),
	ut_flat_list([Aux_exps_new,Aux_exps2,LAux_exps_new,LAux_exps2,Aux_exps],Aux_exps_final),
	ut_flat_list([LTop_exps_new,LTop_exps2,LTop_exps],LTop_exps_final),
	cstr_remove_cycles(cost(Top_exps_final,LTop_exps_final,Aux_exps_final,Bases,Base),Cost_final).
		
	
compute_summatories(Head,Call,Phase,Forward_inv,Summatories,Top_exps2,Aux_exps2):-
	compute_sums(Head,Call,Phase,Forward_inv,Summatories,Top,Aux,Summatories_left),
	maplist(simple_multiplication_list(Head,Call,Phase,Forward_inv),Phase,Summatories_left,Tops,Auxs),
	ut_flat_list([Top,Tops],Top_exps2),
	ut_flat_list([Aux,Auxs],Aux_exps2).


simple_multiplication_list(Head,Call,Phase,Forward_inv,Loop,Sums,Tops,Auxs):-
	maplist(simple_multiplication(Head,Call,Phase,Forward_inv,Loop),Sums,Tops,Auxs).
	
simple_multiplication(Head,Call,Phase,Forward_inv,Loop,bound(Op,Exp,Bounded),Top_exps_new,Aux_exps_total):-
	cstr_name_aux_var(Aux_name),
	max_min_top_expression_in_loop(Head,Call,Phase,Forward_inv,Loop,bound(Op,Exp,[Aux_name]),Top_exps_new,Aux_exps_new),
	cstr_get_it_name(Loop,Loop_name),
	Internal_exp=exp([(Aux_name,Aux_var),(Loop_name,It_var)],[],add([mult([It_var,Aux_var])]),add([])),
    Aux_exp=bound(Op,Internal_exp,Bounded),
    append(Aux_exps_new,[Aux_exp],Aux_exps_total).

	
max_min_top_expressions_in_loop(Head,Call,Phase,Forward_inv,Loop,cost(Top_exps,LTop_exps,Aux,Bs,B),cost(Top_exps_new2,LTop_exps_new2,Aux2,Bs,B)):-
	maplist(max_min_top_expression_in_loop(Head,Call,Phase,Forward_inv,Loop),Top_exps,Top_exps_new,Aux_exps_new),
	maplist(max_min_top_expression_in_loop(Head,Call,Phase,Forward_inv,Loop),LTop_exps,LTop_exps_new,LAux_exps_new),
	ut_flat_list(Top_exps_new,Top_exps_new2),
	ut_flat_list(LTop_exps_new,LTop_exps_new2),
	ut_flat_list([Aux_exps_new,LAux_exps_new,Aux],Aux2).


max_min_top_expression_in_loop(Head,Call,Phase,Forward_inv,Loop,bound(Op,Lin_exp,Bounded),Top_exps_new,[]):-
	%get_phase_star(Head_total,Head,Phase,Cs_star_trans),
	phase_transitive_closure(Phase,_,Head_total,Head,Cs_star_trans),
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	ut_flat_list([Cs_star_trans,Cs,Forward_inv],Context),
	term_variables(Head_total,Vars_of_Interest),
	(Op=ub->
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,max, Maxs_out)
	;
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,min, Maxs_out)
	),
	Head_total=Head,
	maplist(cstr_generate_top_exp(Bounded,Op),Maxs_out,Top_exps_new).

compute_sums(Head,Call,Phase,_Forward_inv,Summatories,Top,Aux,Summatories_left):-
	maplist(get_difference_norms(Head,Call),Summatories,Phase,Summatories_non_diff,Summatories_diff),
	compress_differences(Head,Call,Phase,Summatories_diff,Top1,Aux1,Summatories_left1),
	compress_triangles(Head,Call,Summatories_non_diff,Top2,Aux2,Summatories_left2),
	append(Top1,Top2,Top),
	append(Aux1,Aux2,Aux),
	maplist(append,Summatories_left1,Summatories_left2,Summatories_left).
	
compress_differences(Head,Call,Phase,Summatories,Top,Aux,Summatories_left):-
	maplist(cstr_get_lin_exp_from_tops(Op),Summatories,Expressions_sets),
	(Op=ub->Max_min=max;Max_min=min),
	unions_sl(Expressions_sets,All_expressions),	
	maplist(get_expressions_map(Expressions_sets,Phase),All_expressions,Expressions_map),
	maplist(tuple,All_expressions,_Solutions,Pairs),
	maplist(tuple,Pairs,Expressions_map,Pairs1),
	include(try_inductive_compression(Head,Phase,Call,Max_min),Pairs1,Summed),
	maplist(tuple,Summed_map,_,Summed),
	generate_top_and_aux_from_compressed(Summed_map,Summatories,Top,Aux,Summatories_left).

compress_triangles(_Head,_Call,Summatories,[],[],Summatories).

get_difference_norms(_Head,_,[],_Loop,[],[]).
get_difference_norms(Head,Call,[bound(Op,Lin_exp,Bounded)|Tops],Loop,Summ_non_diff,Summ_diff2):-
	is_difference(Head,Call,Lin_exp,Loop,Exp_diff_list),!,
	maplist(cstr_generate_top_exp(Bounded,Op),Exp_diff_list,New_diffs),
	get_difference_norms(Head,Call,Tops,Loop,Summ_non_diff,Summ_diff),
	append(New_diffs,Summ_diff,Summ_diff2).
get_difference_norms(Head,Call,[bound(Op,Lin_exp,Bounded)|Tops],Loop,[bound(Op,Lin_exp,Bounded)|Summ_non_diff],Summ_diff):-
	get_difference_norms(Head,Call,Tops,Loop,Summ_non_diff,Summ_diff).	

is_difference(Head,Call,Lin_exp,Loop,Diff_list2):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	(difference_constraint2(Head,Call,Cs,Lin_exp,Exp_diff)->
	    Diff_list=[Exp_diff]
	    ;
	    Diff_list=[]
	    ),
	((difference_constraint(Head,Call,Cs,Lin_exp,Exp_diff2),Exp_diff2\==Exp_diff)->
	 Diff_list2=[Exp_diff2|Diff_list]
	    ;
	    Diff_list2=Diff_list
	    ),
	    Diff_list2\=[].


	
get_expressions_map(Ex_sets,Phase,Lin_exp,Map_set):-
	maplist(loop_contains_exp(Lin_exp),Ex_sets,Phase,Map),
	ut_flat_list(Map,Map_flat),
	from_list_sl(Map_flat,Map_set).
	
loop_contains_exp(Lin_exp,Set,Loop,[Loop]):-
		contains_sl(Set,Lin_exp),!.

loop_contains_exp(_Lin_exp,_Set,_Loop,[]).	


generate_top_and_aux_from_compressed([],Summatories,[],[],Summatories).
generate_top_and_aux_from_compressed([(Exp,(Bounded,Top1,Aux1))|Compressed_norms],Summatories,Top,Aux,Summatories_left):-
		remove_tops_with_exp(Summatories,[],Exp,Bounded,Summatories1),
		generate_top_and_aux_from_compressed(Compressed_norms,Summatories1,Top2,Aux2,Summatories_left),
		append(Top1,Top2,Top),
		append(Aux1,Aux2,Aux).
		
remove_tops_with_exp([],Bounded,_Exp,Bounded,[]).
remove_tops_with_exp([Summ|Summatories],Bounded_accum,Exp,Bounded,[Summ1|Summatories1]):-
	remove_tops_with_exp_1(Exp,Summ,Summ1,Bounded_aux),
	append(Bounded_aux,Bounded_accum,Bounded_accum1),
	remove_tops_with_exp(Summatories,Bounded_accum1,Exp,Bounded,Summatories1).
	
	
remove_tops_with_exp_1(Lin_exp,Tops,Tops1,Bounded):-
	partition(top_has_exp(Lin_exp),Tops,Tops_selected,Tops1),
	(
	Tops_selected=[bound(_,_,Bounded)]
	;
	(Tops_selected=[],Bounded=[])
	),!.
remove_tops_with_exp_1(_Lin_exp,Tops,_Tops1,_Bounded):-
	throw(implementation_error('failed assumption that a linear expression appears only once after substitution',Tops)).
	


top_has_exp(Lin_exp,bound(_Op,Lin_exp2,_)):-Lin_exp==Lin_exp2.

try_inductive_compression(Head,Phase,Call,Max_Min,((L,(Bounded_var,Tops,Auxs)),Expressions_map)):-
	L=Coeffs+Delta,
	L_wc=Coeffs+0,
	difference_sl(Phase,Expressions_map,Other_loops),
	(Max_Min=max->	
 	(greater_fr(Delta,0)->
 		maplist(generate_loop_info(Delta,max),Expressions_map,Same_loops_info)
    	;
    	Same_loops_info=[]
    	)
	;
    geq_fr(Delta,0),
    Same_loops_info=[]
	),
	maplist(is_not_negative(Head,Call,L_wc),Expressions_map),
	maplist(check_bad_loops(Head,Call,L_wc,Max_Min),Other_loops,Bad_loops_info),
	ut_flat_list([Same_loops_info,Bad_loops_info],Bad_loops_info_flat),!,	
	generate_top_and_aux(Bad_loops_info_flat,Max_Min,[L_wc],Bounded_var,Tops,Auxs).

/*
%triangular
try_inductive_compression(Head,Phase,Forward_inv,_Cs_star_trans,Call,Max_Min,((L2,(Bounded_var,Tops,Auxs)),Expressions_map)):-
	%phase_loop(Phase,_,Call,Call2,Phi),
	%trace,
	term_variables(L2,Vars_L),
	Vars_L\=[],
	Head=..[_|EVars],
	
%	from_list_sl(EVars,EVars_set),
%	difference_sl(Vars_l_set,EVars_set,[]),%only entry variables
	
	(Expressions_map=Phase->
		phase_loop(Phase,_,Head,Call,Phi)
		;
		maplist(get_loop_cs(Head,Call),Expressions_map,Css),
		nad_list_lub(Css,Phi)
	),
	max_min_linear_expression_all(L2,EVars,Phi,Max_Min,Lss),
	member(L,Lss),\+term_variables(L,[]),
	
	difference_sl(Phase,Expressions_map,Other_loops),

	copy_term((Head,L),(Call,Lp)),
	

	ut_flat_list([Phi,Forward_inv],Cs_comb),
	%term_variables(Cs_comb,Vars_constraint),
	%trace,
	normalize_constraint( D=(Lp-L) ,Inductive_constraint_aux),
	(Max_Min=max->	
    nad_maximize([Inductive_constraint_aux|Cs_comb],[D],[Delta])
    ,
    Delta\=0/1
	;
    nad_minimize([Inductive_constraint_aux|Cs_comb],[D],[Delta])
    ,
    Delta\=0/1
	),
	maplist(is_not_negative(Head,Call,L),Expressions_map),
	maplist(check_bad_loops(Head,Call,Forward_inv,L,Max_Min),Other_loops,Bad_loops_info),
	ut_flat_list(Bad_loops_info,Bad_loops_info_flat),
fail,
	generate_top_and_aux_triangular(Delta,Expressions_map,Bad_loops_info_flat,Max_Min,Lss,Bounded_var,Tops,Auxs).
	


generate_top_and_aux_triangular(Delta,[Loop],Info,Max_min,Maxs,Bounded,Tops,Auxs):-
	(Max_min=max-> Op=ub;Op=lb),
	multiply_fr(Delta,1/2,Delta_2),
	%we can always exclude min
	exclude(is_min,Info,Info2),
	maplist(get_factors_from_loop_info,Info2,Factors,Index),
	cstr_name_aux_var(Name_aux),
	cstr_get_it_name(Loop,Name_loop),
	(greater_fr(Delta,0)->
	Exp=exp([(Name_aux,Var_aux),(Name_loop,Var_loop_1),(Name_loop,Var_loop_2),(Name_loop,Var_loop_3),(Name_loop,Var_loop_4)|Index],
	[],
	add([mult([Var_loop_1,Var_aux]),mult([Var_loop_2,Var_loop_3,Delta_2]),mult([Var_loop_4,Delta_2])|Factors]),
	add([]))
	;
	negate_fr(Delta_2,Delta_3),
	Exp=exp([(Name_aux,Var_aux),(Name_loop,Var_loop_1)|Index],
	[(Name_loop,Var_loop_2),(Name_loop,Var_loop_3),(Name_loop,Var_loop_4)],
	add([mult([Var_loop_1,Var_aux])|Factors]),
	add([mult([Var_loop_2,Var_loop_3,Delta_3]),mult([Var_loop_4,Delta_3])]))
	),
	Auxs=[bound(Op,Exp,Bounded)],
	maplist(cstr_generate_top_exp([Name_aux],Op),Maxs,Tops).	

*/
%TODO stop excluding mins
generate_top_and_aux(Info,Max_min,Maxs,Bounded,Tops,Auxs):-
	(Max_min=max-> Op=ub;Op=lb),
	%we can always exclude min
	exclude(is_min,Info,Info2),
	(Info2=[]->
	maplist(cstr_generate_top_exp(Bounded,Op),Maxs,Tops),
	Auxs=[]
	;
	maplist(get_factors_from_loop_info,Info2,Factors,Index),
	cstr_name_aux_var(Name_aux),
	Internal_exp=exp([(Name_aux,Var_aux)|Index],[],add([mult([Var_aux])|Factors]),add([])),
	Auxs=[bound(Op,Internal_exp,Bounded)],
	maplist(cstr_generate_top_exp([Name_aux],Op),Maxs,Tops)
	).

is_min(	(min(_),_)).
	
get_factors_from_loop_info((max(Loop),1),mult([Var_aux]),(Loop_name,Var_aux)):-
	cstr_get_it_name(Loop,Loop_name),!.
get_factors_from_loop_info((max(Loop),N),mult([Var_aux,N]),(Loop_name,Var_aux)):-
	cstr_get_it_name(Loop,Loop_name).


get_loop_cs(Head,Call,Loop,Cs):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_).

generate_loop_info(Delta,Max_min,Loop,(Max_min_loop,Delta)):-
	Max_min_loop=..[Max_min,Loop].

is_not_negative(Head,Call,Lin_exp,Loop):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	integrate_le(Lin_exp,_,Lin_exp_nat),
	write_le(Lin_exp_nat,Expression_nat),
	term_variables(Cs,Vars_constraint),
	nad_entails(Vars_constraint,Cs,[Expression_nat>=0]).


check_bad_loops(Head,Call,Lin_exp,Max_Min,Loop,Info):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	elements_le(Lin_exp,Vars_exp_set),
	term_variables(Call,Vars_call),from_list_sl(Vars_call,Vars_call_set),
	(intersection_sl(Vars_exp_set,Vars_call_set,[])->
		copy_term((Lin_exp,Head),(Lin_exp_p,Call)),
		subtract_le(Lin_exp,Lin_exp_p,Lin_exp_diff),
		integrate_le(Lin_exp_diff,Den,Lin_exp_diff_nat),
		write_le(Lin_exp_diff_nat,Exp_diff),
		Constraint= (Den*D=Exp_diff)
		
		;
		integrate_le(Lin_exp,Den,Lin_exp_nat),
		write_le(Lin_exp_nat,Exp),
		Constraint= (Den*D=Exp)
	),
	Cs_1 = [ Constraint | Cs],
	(Max_Min=max->
	  (nad_minimize(Cs_1,[D],[Delta])->
	  Pos_loop=max(Loop),
	  Neg_loop=min(Loop)
	  ;
	%  term_variables(Head,Vars),
	%  max_min_linear_expression_all(Exp,Vars,Cs,min, MINS),
	  fail
	  )
	;
	  nad_maximize(Cs_1,[D],[Delta]),
	  Pos_loop=min(Loop),
	  Neg_loop=max(Loop)
	),
	negate_fr(Delta,Constant),
	(geq_fr(Constant,0)->
	   (Constant\==0 ->
	   	  Info=(Pos_loop,Constant)
	 	;
	   	  Info=[]
	   )
	 ;
	 Info=(Neg_loop,Constant)
	 ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	
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
	% If we have not iferred enough upper bounds
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