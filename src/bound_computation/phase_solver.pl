/** <module> phase_solver

This module computes the cost structure of a phase in terms of the variables 
at the beginning and the end of the phase.


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

:- module(phase_solver,[compute_phases_cost/5,init_phase_solver/0]).

					
:- use_module(cost_equation_solver,[get_equation_cost/5]).
:- use_module(constraints_maximization,[max_min_linear_expression_all/5]).		
				      
:- use_module('../db',[
			   phase_loop/5,
		       loop_ph/6]).

:- use_module('../IO/params',[get_param/2]).		
:- use_module('../IO/output',[print_phase_cost/4]).
:- use_module('../ranking_functions',[
				      ranking_function/4,
				      partial_ranking_function/7]).	
				      		
:-use_module('../refinement/invariants',[
			      phase_transitive_closure/5,
%			      get_phase_star/4,
			      forward_invariant/4]).			
	
:- use_module('../utils/cofloco_utils',[
			tuple/3,
			ground_copy/2,
			repeat_n_times/3,
			bagof_no_fail/3]).	
:- use_module('../utils/cost_structures',[
			cstr_extend_variables_names/3,
			cstr_extract_top_maxs/3,
		    cstr_extract_top_mins/3,
			cstr_remove_cycles/2,
			cstr_name_aux_var/1,
			cstr_get_it_name/2,
			cstr_propagate_summatory/4,
			cstr_generate_top_exp/4,
			cstr_empty/1,
			cstr_join/3]).			
:-use_module('../utils/template_inference',[
	difference_constraint_farkas_ub/6,
	difference_constraint_farkas_lb/5
	]).		
:-use_module('../utils/polyhedra_optimizations',[
	slice_relevant_constraints_and_vars/5
	]).						
:- use_module(stdlib(numeric_abstract_domains),[
						nad_maximize/3,
						nad_minimize/3,
						nad_entails/3,
						nad_consistent_constraints/1]).
:- use_module(stdlib(linear_expression),[
	integrate_le/3,
	write_le/2,
	multiply_le/3,
	semi_normalize_le/3,
	subtract_le/3,
	negate_le/2]).							
:- use_module(stdlib(fraction),[inverse_fr/2,greater_fr/2,geq_fr/2,divide_fr/3,negate_fr/2,multiply_fr/3,subtract_fr/3]).
:- use_module(stdlib(fraction_list),[max_frl/2]).

:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map)).
:- use_module(stdlib(multimap)).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_increase/3]).
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).

%! phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cost_structure)
% store the cost structure of a phase given a local invariant
% for cacheing purposes
:- dynamic  phase_cost/5.



%! init_phase_solver is det
% clear all the intermediate results
init_phase_solver:-
	retractall(phase_cost(_,_,_,_,_,_)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_phases_cost(+Phases:list(phase),+Chain:chain,+Head:term,+Call:term,-Costs:list(cost_structure)) is det
% compute cost structures for the phases Phases that belong to Chain.
% the internal parts of the cost structure are directly expressed in terms of the input variables of the chain
% the constraints of the cost structure are expressed in terms of the variables at the beginnig and end of the chain (Head and Call)
compute_phases_cost([],_,_,_,[]).
compute_phases_cost([Phase|More],Chain,Head,Call,[Cost|Costs]):-
	forward_invariant(Head,([Phase|More],_),Forward_inv_hash,Forward_inv),
	%obtain a cost structure in terms of the variables at the beginning and end of the phase
	compute_phase_cost(Phase,Head,Call,(Forward_inv_hash,Forward_inv),Cost),
	(get_param(debug,[])->print_phase_cost(Phase,Head,Call,Cost);true),
	compute_phases_cost(More,Chain,Head,Call,Costs).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! compute_phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cost_structure) is det
% Obtain the cost of a phase given a forward invariant.
% if the phase is non-iterative, the cost is the cost of the equation, otherwise:
% * get the cost of all the equations
% * put each cost into a new loop
% * try to take loops out by inductive compression
% * try to compress constraints from different loops
compute_phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost):-
	phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv2),Cost),
	Forward_inv2==Forward_inv,!,
	counter_increase(compressed_phases1,1,_).
% in a non-iterative phase, we just obtain the cost of the equation
compute_phase_cost(Non_it,Head,Call,(Forward_hash,Forward_inv),Cost):-
	number(Non_it),	
	profiling_start_timer(equation_cost),
	get_equation_cost(Head,Call1,(Forward_hash,Forward_inv),Non_it,Cost),
	(Call1\=none->Call1=Call;true),
	profiling_stop_timer_acum(equation_cost,_),
	assert(phase_cost(Non_it,Head,Call,(Forward_hash,Forward_inv),Cost)).

compute_phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost):-
    %get the cost of each iterative component of the phase	
	profiling_start_timer(equation_cost),
	maplist(get_equation_loop_cost(Head,Call,(Forward_hash,Forward_inv)),Phase,Costs),
	profiling_stop_timer_acum(equation_cost,_),
	max_min_costs_in_phase(Costs,Head,Call,Forward_inv,Phase,Cost),
	assert(phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost)).

get_equation_loop_cost(Head,Call,(Forward_hash,Forward_inv),Eq_id,Cost2):-
	get_equation_cost(Head,Call,(Forward_hash,Forward_inv),Eq_id,Cost),
	cstr_extend_variables_names(Cost,it(Eq_id),Cost2).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-dynamic new_phase_top/4.
:-dynamic new_phase_aux/4.
:-dynamic max_min_found/6,sum_found/9.

:-dynamic forward_invariant_temp/3.

max_min_costs_in_phase(Costs,Head,Call,Forward_inv,Phase,Cost_final):-
	assert(forward_invariant_temp(Head,Call,Forward_inv)),
	maplist(cstr_remove_cycles,Costs,Costs_simple),
	maplist(cstr_propagate_summatory,Phase,Costs_simple,Costs_propagated,Summatories_pairs),
	maplist(cstr_extract_top_maxs,Costs_propagated,Costs_propagated1,Maxs),
	maplist(cstr_extract_top_mins,Costs_propagated1,Costs_propagated2,Mins),
	maplist(tuple,Summatories_max,Summatories_min,Summatories_pairs),
%	(get_param(compute_ubs,[])->
	      maplist(get_it_sum_constraint(ub),Phase,It_cons_max)
%	      ;
%	      length(Phase,N_phase),
%	      repeat_n_times(N_phase,[],It_cons_max)
%	 )
	 , 
	(get_param(compute_lbs,[])->
	      maplist(get_it_sum_constraint(lb),Phase,It_cons_min)
	      ;
	      length(Phase,N_phase),
	      repeat_n_times(N_phase,[],It_cons_min)
	 ),    

	maplist(append,It_cons_max,Summatories_max,Summatories_max1),
	maplist(append,It_cons_min,Summatories_min,Summatories_min1),
	%
	cstr_empty(Empty_cost),
	foldl(cstr_join,Costs_propagated2,Empty_cost,cost([],[],Aux_exps,Bases,Base)),
	compute_sums_and_max_min_in_phase(Head,Call,Phase,Maxs,Mins,Summatories_max1,Summatories_min1,Final_top_max,Final_top_min,New_auxs),
	retractall(forward_invariant_temp(_,_,_)),
	append(New_auxs,Aux_exps,Aux_exps_final),
	cstr_remove_cycles(cost(Final_top_max,Final_top_min,Aux_exps_final,Bases,Base),Cost_final),!.
	
get_it_sum_constraint(ub,Loop,[bound(ub,[]+1,[Loop_name])]):-
	cstr_get_it_name(Loop,Loop_name).
get_it_sum_constraint(lb,Loop,[bound(lb,[]+1,[Loop_name])]):-
	cstr_get_it_name(Loop,Loop_name).	
	
	
compute_sums_and_max_min_in_phase(Head,Call,Phase,Maxs,Mins,Summatories_max,Summatories_min,Final_top_max,Final_top_min,New_auxs):-
	empty_pending(Empty_pending),
	retractall(max_min_found(_,_,_,_,_,_)),
	retractall(sum_found(_,_,_,_,_,_,_,_,_)),
	foldl(save_pending_list(max),Phase,Maxs,Empty_pending,Pending1),
	foldl(save_pending_list(min),Phase,Mins,Pending1,Pending2),
	foldl(save_pending_list(maxsum),Phase,Summatories_max,Pending2,Pending3),
	foldl(save_pending_list(minsum),Phase,Summatories_min,Pending3,Pending4),
	%special treatment of ranking functions of the whole phase
	add_general_ranking_functions(Head,Call,Phase),
	length(Phase,N),
	Max_pending is 40*N,
	compute_all_pending(Head,Call,Phase,Pending4,Max_pending),
	collect_phase_results(Head,Call,Phase,Final_top_max,Final_top_min,New_auxs).

add_general_ranking_functions(Head,Call,Phase):-
	rf_limit(Max),
%	(get_param(compute_ubs,[])->
	   get_ranking_functions_constraints(Max,Head,Call,Phase,_,Top),
	   maplist(save_new_phase_top(Head,Call,Phase),Top)
%	   ;
%	   true)
	   ,
	(get_param(compute_lbs,[])->
	   get_ranking_functions_lower_constraints(Max,Head,Call,Phase,_,LTop),
	   maplist(save_new_phase_top(Head,Call,Phase),LTop)
	   ;
	   true).
	
		
compute_all_pending(Head,Call,Phase,Pending,_Max_pending):-%Max_pending > 0,Max_pending1 is Max_pending-1,
	compute_pending(Head,Call,Phase,Pending,Pending_out),
	compute_all_pending(Head,Call,Phase,Pending_out,_Max_pending1).

compute_all_pending(_,_,_,_,_).

compute_pending(Head,Call,Phase,Pending,Pending_out):-
	get_one_pending(Pending,Type,(Lin_exp,Coeff_bounded),Pending1),
	(get_param(debug,[])->print_pending_info(Head,Call,Type,Lin_exp,Pending1);true),
	compute_pending_element(Type,Head,Call,Phase,Lin_exp,Coeff_bounded,New_tops,New_auxs,Pending1,Pending_out),
	maplist(save_new_phase_top(Head,Call,Phase),New_tops),
	maplist(save_new_phase_aux(Head,Call,Phase),New_auxs).


compute_pending_element(maxsum(Loop),Head,Call,Phase,Exp,Bounded,New_tops,New_auxs,Pending,Pending_out):-
	compute_sum(Head,Call,Phase,Loop,Exp,max,Bounded,New_tops,New_auxs,Pending,Pending_out).
compute_pending_element(minsum(Loop),Head,Call,Phase,Exp,Bounded,New_tops,New_auxs,Pending,Pending_out):-
	compute_sum(Head,Call,Phase,Loop,Exp,min,Bounded,New_tops,New_auxs,Pending,Pending_out).	
compute_pending_element(max,Head,Call,Phase,Exp,Bounded,New_tops,New_auxs,Pending,Pending_out):-
	compute_max_min(Head,Call,Phase,Exp,max,Bounded,New_tops,New_auxs,Pending,Pending_out).	
compute_pending_element(min,Head,Call,Phase,Exp,Bounded,New_tops,New_auxs,Pending,Pending_out):-
	compute_max_min(Head,Call,Phase,Exp,min,Bounded,New_tops,New_auxs,Pending,Pending_out).	

compute_sum(_Head,_Call,_Phase,_Loop,[]+0,Max_min,Bounded,[bound(Op,[]+0,Bounded)],[],Pending,Pending):-!,
	get_constr_op(Max_min,Op).
	
		
%maxsum: partial ranking function (a special case of linear sum)

compute_sum(Head,Call,Phase,Loop,[]+1,max,Bounded,New_tops,New_auxs,Pending,Pending_out):-!,
	bagof_no_fail(Rf,
	Deps^Deps_type^Loops^
	(
			partial_ranking_function(Head,_Chain,Phase,Loops,Rf,Deps,Deps_type),
			contains_sl(Loops,Loop)		
			),Rfs),
	maplist(get_difference_version(Head,Call),Rfs,Rfs_diff),
	append(Rfs,Rfs_diff,Rfs_all),
	maplist(check_loops_maxsum(Head,Call,Phase,Loop,Bounded,Pending),Rfs_all,New_tops_list,New_auxs_list,Pending_out_list),
	ut_flat_list(New_tops_list,New_tops),
	ut_flat_list(New_auxs_list,New_auxs),
	empty_pending(Empty_pending),
	foldl(union_pending,Pending_out_list,Empty_pending,Pending_out_aux),
	(empty_pending(Pending_out_aux)->
		Pending_out=Pending
		;
		Pending_out=Pending_out_aux
	).

% minsum: partial ranking function (a special case of linear sum)
%/*
compute_sum(Head,Call,Phase,Loop,[]+1,min,Bounded,New_tops,New_auxs,Pending,Pending_out):-
	bagof_no_fail(Lb,get_partial_lower_bound(Head,Call,_Chain,Loop,Lb),Lbs),
	maplist(check_loops_minsum(Head,Call,Phase,Loop,Bounded,Pending),Lbs,New_tops_list,New_auxs_list,Pending_out_list),
	ut_flat_list(New_tops_list,New_tops),
	ut_flat_list(New_auxs_list,New_auxs),
	New_tops\=[],!,
	empty_pending(Empty_pending),
	foldl(union_pending,Pending_out_list,Empty_pending,Pending_out_aux),
	(empty_pending(Pending_out_aux)->
		Pending_out=Pending
		;
		Pending_out=Pending_out_aux
	).		
%*/
% Stored solution
compute_sum(Head,Call,_Phase,Loop,Lin_exp,Max_min,Bounded,Tops1,[New_aux|Auxs1],Pending,Pending):-
	get_constr_op(Max_min,Op),
	semi_normalize_le(Lin_exp,Coeff2,Lin_exp_normalized2),
	ground_copy((Head,Call,Lin_exp_normalized2),(_,_,Lin_exp_norm_ground)),
	sum_found(Loop,Lin_exp_norm_ground,Max_min,Head,Call,Coeff,Aux_name,Tops1,Auxs1),!,
	divide_fr(Coeff2,Coeff,Coeff_final),
	cstr_name_aux_var(Aux_name),
	Internal_exp=exp([(Aux_name,Aux_var)],[],add([mult([Aux_var,Coeff_final])]),add([])),
	New_aux=bound(Op,Internal_exp,Bounded).


%triangle	
compute_sum(Head,Call,Phase,Loop,Lin_exp,min,Bounded_ini,New_tops,New_auxs,Pending,Pending_out):-
	Lin_exp\=[]+_,
	get_enriched_loop(Loop,Head,Call,Cs),
	(is_head_expression(Head,Lin_exp)->
		Exp=Lin_exp
	;
	 Head=..[_|Vars_head],
	 max_min_linear_expression_all(Lin_exp, Vars_head, Cs,min, Mins),
	 member(Exp,Mins)
	),
	get_difference_version(Head,Call,Exp,Exp_diff),	
	le_print_int(Exp_diff,Exp_diff_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_int=Exp_diff_denominator*D|Cs],[D],[Delta]),
	(
	(greater_fr(Delta,0),Dir=pos,Dir_neg=neg)
	;
	(greater_fr(0,Delta),Dir=neg,Dir_neg=pos)
	),	
	delete(Phase,Loop,Phase_rest),
	cstr_name_aux_var(Initial_name),
	check_loops_triangle_minsum(Phase_rest,Dir,Head,Call,Pending,Exp,Other_Bounded,Increments,Other_loops,Pending_aux),
	compute_max_min(Head,Call,Other_loops,Exp,min,[Initial_name],New_tops,New_auxs1,Pending_aux,Pending_out),
	get_bounded_exp([(Loop,Bounded_ini)|Other_Bounded],Involved_loops,Bounded_vars),
	get_it_sum_aux(Involved_loops,Aux_cons,All_iterations_name),
	max_frl([Delta|Increments],Min_increment),
	(Dir=pos->
		multiply_fr(Min_increment,1/2,Min_increment_scaled)
	;
		multiply_fr(Min_increment,-1/2,Min_increment_scaled)
	),
	Summands=[summand(Dir_neg,[(All_iterations_name,All_iterations_var2),(All_iterations_name,All_iterations_var3)],mult([All_iterations_var2,All_iterations_var3,Min_increment_scaled]))],
	cstr_name_aux_var(Aux_name_main_cost),
	Aux_cons2=bound(lb,exp([(Initial_name,Initial_var),(All_iterations_name,All_iterations_var)],[],add([mult([Initial_var,All_iterations_var])]),add([])),[Aux_name_main_cost]),
	
	cexpr_build_internal_exp(Summands,[Aux_name_main_cost],lb,Internal_exp),
	Main_aux=bound(lb,Internal_exp,Bounded_vars),
	ut_flat_list([New_auxs1,Aux_cons2,Aux_cons,Main_aux],New_auxs),!,
	save_sum_found(Head,Call,Loop,Lin_exp,min,Bounded_ini,New_tops,New_auxs).	
	

%linear sum
compute_sum(Head,Call,Phase,Loop,Lin_exp,Max_min,Bounded,New_tops,New_auxs2,Pending,Pending_out):-
	Lin_exp\=[]+_,
	is_difference(Head,Call,Lin_exp,Max_min,Loop,Exp_list),
	(Max_min=max->
	maplist(check_loops_maxsum(Head,Call,Phase,Loop,Bounded,Pending),Exp_list,New_tops_list,New_auxs_list,Pending_out_list)
	;
	maplist(check_loops_minsum(Head,Call,Phase,Loop,Bounded,Pending),Exp_list,New_tops_list,New_auxs_list,Pending_out_list)
	),
	ut_flat_list(New_tops_list,New_tops),
	%we stay with this option as long as one attempt succeeded 
	%otherwise go to simple multiplication
	New_tops\=[],
	ut_flat_list(New_auxs_list,New_auxs),
	empty_pending(Empty_pending),
	foldl(union_pending,Pending_out_list,Empty_pending,Pending_aux),
	((New_auxs\=[]; (Max_min=min,Lin_exp\=[]+_))->
	simple_multiplication(Head,Call,Loop,Lin_exp,Bounded,Aux_exp,Max_min,Pending_aux,Pending_out),
	New_auxs2=[Aux_exp|New_auxs]
	;
	Pending_aux=Pending_out,
	New_auxs2=New_auxs
	),
	save_sum_found(Head,Call,Loop,Lin_exp,Max_min,Bounded,New_tops,New_auxs2).


%simple multiplication
compute_sum(Head,Call,_Phase,Loop,Lin_exp,Max_min,Bounded,[],[Aux_exp],Pending,Pending_out):-
	Lin_exp\=[]+1,!,
	simple_multiplication(Head,Call,Loop,Lin_exp,Bounded,Aux_exp,Max_min,Pending,Pending_out),
	save_sum_found(Head,Call,Loop,Lin_exp,Max_min,Bounded,[],[Aux_exp]).
	
compute_sum(_Head,_Call,_Phase,_Loop,_,_Max_min,_Bounded,[],[],Pending,Pending).	
%/*

get_it_sum_aux(Involved_loops,Auxs,All_iterations_var):-
	cstr_name_aux_var(All_iterations_var),
	maplist(cstr_get_it_name,Involved_loops,Involved_it_vars),
	generate_index(Involved_it_vars,[],It_vars,Index),
	maplist(put_inside_mult,It_vars,It_summands),
	Internal_exp=exp(Index,[],add(It_summands),add([])),
	copy_term(Internal_exp,Internal_exp2),
	Auxs=[bound(lb,Internal_exp,[All_iterations_var]),bound(ub,Internal_exp2,[All_iterations_var])].
	
check_loops_triangle_minsum([],_Pos_neg,_Head,_Call,Pending,_Exp,[],[],[],Pending).
check_loops_triangle_minsum([Loop|Loops],Pos_neg,Head,Call,Pending,Exp,[Bounded_loop|Bounded],[Increment|Increments],Other_loops,Pending_out):-
	check_loop_triangle_minsum(Loop,Pos_neg,Head,Call,Pending,Exp,Bounded_loop,Increment,Pending_aux),!,
	check_loops_triangle_minsum(Loops,Pos_neg,Head,Call,Pending_aux,Exp,Bounded,Increments,Other_loops,Pending_out).
	
check_loops_triangle_minsum([Loop|Loops],Pos_neg,Head,Call,Pending,Exp,Bounded,Increments,[Loop|Other_loops],Pending_out):-
	check_loops_triangle_minsum(Loops,Pos_neg,Head,Call,Pending,Exp,Bounded,Increments,Other_loops,Pending_out).
	
check_loop_triangle_minsum(Loop,Pos_neg,Head,Call,Pending,Exp,Bounded,Delta,Pending1):-	
	get_enriched_loop(Loop,Head,Call,Cs),
	get_difference_version(Head,Call,Exp,Exp_diff),	
	le_print_int(Exp_diff,Exp_diff_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_int=Exp_diff_denominator*D|Cs],[D],[Delta]),
	(Pos_neg=pos->
		greater_fr(Delta,0)
	;
		greater_fr(0,Delta)
	),
%	term_variables((Head,Call),Vars),	
%	le_print_int(Exp_diff,Exp_diff_print_int,_),
%	nad_entails(Vars,Cs,[Exp_diff_print_int>=0]),!,
	find_minsum_constraint(Loop,Head,Call,Cs,Exp,New_bounded,Pending,Pending1),!,
	Bounded=(Loop,New_bounded),
	(get_param(debug,[])->format('Loop ~p is triangle collaborative with ~p ~n',[Loop,Delta]);true).
	
%*/


check_loops_maxsum(Head,Call,Phase,Loop,Bounded_ini,Pending,Exp,Tops,Auxs,Pending_out):-
	(get_param(debug,[])->print_lin_exp_in_phase(Head,Call,Exp);true),
	
	(is_head_expression(Head,Exp)->
			get_difference_version(Head,Call,Exp,Exp_diff),
			Flag=head(Exp)
			;
			Flag=diff,
			Exp=Coeffs+_Cnt,
			Exp_diff=Coeffs+0
	),
	check_loops_maxsum_1(Phase,Loop,Head,Call,Exp_diff,Flag,Summands,Bounded,Pending,Pending_out),!,
	get_bounded_exp([(Loop,Bounded_ini)|Bounded],_Bounded_loops,Bounded_vars),
	cond_add_same_loop_increment(Head,Loop,Exp,Summands,Summands1),
	(Summands1=[]->
		Tops=[bound(ub,Exp,Bounded_vars)],
		Auxs=[]
		;
		cstr_name_aux_var(Aux_name),
		cexpr_build_internal_exp(Summands1,[Aux_name],ub,Expression),
		Tops=[bound(ub,Exp,[Aux_name])],
		Auxs=[bound(ub,Expression,Bounded_vars)]
	).
check_loops_maxsum(_Head,_Call,_Phase,_Loop,_Bounded,_Pending,_Exp,[],[],Empty_pending):-
	empty_pending(Empty_pending).

check_loops_minsum(Head,Call,Phase,Loop,Bounded_ini,Pending,Exp,Tops,Auxs,Pending_out):-
	(get_param(debug,[])->print_lin_exp_in_phase(Head,Call,Exp);true),
	Exp=Coeffs+_Cnt,
	Exp_diff=Coeffs+0,
	check_loops_minsum_1(Phase,Loop,Head,Call,Exp_diff,Summands,Bounded,Pending,Pending_out),!,
	%FIXME add related to Cnt
	get_bounded_exp([(Loop,Bounded_ini)|Bounded],_Bounded_loops,Bounded_vars),
	(Summands=[]->
		Tops=[bound(lb,Exp,Bounded_vars)],
		Auxs=[]
		;
		cstr_name_aux_var(Aux_name),
		cstr_name_aux_var(Aux_name2),
		cexpr_build_internal_exp([summand(neg,[(Aux_name2,Aux_var2)],mult([Aux_var2]))|Summands],[Aux_name],lb,Expression),
		negate_le(Exp,Exp_neg),
		Tops=[bound(lb,Exp,[Aux_name]),bound(ub,Exp_neg,[Aux_name2])],
		Auxs=[bound(lb,Expression,Bounded_vars)]
	).
check_loops_minsum(_Head,_Call,_Phase,_Loop,_Bounded,_Pending,_Exp,[],[],Empty_pending):-
	empty_pending(Empty_pending).
	

check_loops_maxsum_1([],_,_,_,_,_Flag,[],[],Pending,Pending).		
%ignore the loop that we started from	
check_loops_maxsum_1([Loop|Loops],Loop,Head,Call,Exp,Flag,Summands,Bounded,Pending,Pending_out):-!,
		check_loops_maxsum_1(Loops,Loop,Head,Call,Exp,Flag,Summands,Bounded,Pending,Pending_out).
		
check_loops_maxsum_1([Loop2|Loops],Loop,Head,Call,Exp_diff,Flag,Summands,Bounded,Pending,Pending_out):-	
		check_loop_maxsum(Head,Call,Exp_diff,Flag,Loop2,Summands1,Bounded1,Pending,Pending1),!,
		check_loops_maxsum_1(Loops,Loop,Head,Call,Exp_diff,Flag,Summands2,Bounded2,Pending1,Pending_out),
		append(Summands1,Summands2,Summands),
		append(Bounded1,Bounded2,Bounded).
		
%collaborative loop		
check_loop_maxsum(Head,Call,Exp_diff,Flag,Loop,[],Bounded,Pending,Pending1):-
		get_enriched_loop(Loop,Head,Call,Cs),
		term_variables((Head,Call),Vars),	
		le_print_int(Exp_diff,Exp_diff_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff_print_int>=0]),!,
		(find_maxsum_constraint(Loop,Head,Call,Cs,Exp_diff,Flag,New_bounded,Pending,Pending1)->			
			Bounded=[(Loop,New_bounded)]
			;
			Pending1=Pending,
			Bounded=[]
		),
		(get_param(debug,[])->format('Loop ~p is collaborative~n',[Loop]);true).
		
%add a constant			
check_loop_maxsum(Head,Call,Exp_diff,_Flag,Loop,Summands,[],Pending,Pending):-	
	get_enriched_loop(Loop,Head,Call,Cs),
	negate_le(Exp_diff,Exp_diff_neg),
	le_print_int(Exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta]),!,
	cstr_get_it_name(Loop,Loop_name),
	Summands=[summand(pos,[(Loop_name,Loop_var)],mult([Loop_var,Delta]))],
	(get_param(debug,[])->format('Loop ~p adds a constant ~p ~n',[Loop,Delta]);true).
	

%add an expression	
check_loop_maxsum(Head,Call,Exp_diff,_Flag,Loop,Summands,[],Pending,Pending1):-	
	get_enriched_loop(Loop,Head,Call,Cs),
	negate_le(Exp_diff,Exp_diff_neg),
	term_variables(Head,Vars_head),from_list_sl(Vars_head,Vars_head_set),
	term_variables(Exp_diff_neg,Vars_exp),from_list_sl(Vars_exp,Vars_exp_set),
	difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest),
	max_min_linear_expression_all(Exp_diff_neg, Vars_of_Interest, Cs,max, Maxs),
	Maxs\=[],!,
	cstr_name_aux_var(Aux_name),
	Summands=[summand(pos,[(Aux_name,Aux_var)],mult([Aux_var]))],
	maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxsums),
	save_pending_list(maxsum,Loop,Maxsums,Pending,Pending1),
	(get_param(debug,[])->format('Loop ~p adds an expression ~p~n',[Loop,Maxs]);true).

%reset
check_loop_maxsum(Head,_Call,_Exp_diff,head(Exp),Loop,Summands,[],Pending,Pending1):-
	%get_head_expression_part(Head,Exp_diff,Exp),
	copy_term((Head,Exp),(Call,Exp_end)),	
	get_enriched_loop(Loop,Head,Call,Cs),
	term_variables(Head,Vars_head),%from_list_sl(Vars_head,Vars_head_set),
	%term_variables(Exp,Vars_exp),from_list_sl(Vars_exp,Vars_exp_set),
	%difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest),
	max_min_linear_expression_all(Exp_end, Vars_head, Cs,max, Maxs),
	Maxs\=[],!,
	cstr_name_aux_var(Aux_name),
	Summands=[summand(pos,[(Aux_name,Aux_var)],mult([Aux_var]))],
	maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxsums),
	save_pending_list(maxsum,Loop,Maxsums,Pending,Pending1),
	(get_param(debug,[])->format('Loop ~p has a reset to  ~p~n',[Loop,Maxs]);true).

check_loop_maxsum(_Head,_Call,_Exp_diff,_,Loop,[],[],_Pending,_Pending1):-	
	    (get_param(debug,[])->format('Loop ~p has undefined behavior ~n',[Loop]);true),
		fail.	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
check_loops_minsum_1([],_,_,_,_,[],[],Pending,Pending).		
%ignore the loop that we started from	
check_loops_minsum_1([Loop|Loops],Loop,Head,Call,Exp,Summands,Bounded,Pending,Pending_out):-!,
		check_loops_minsum_1(Loops,Loop,Head,Call,Exp,Summands,Bounded,Pending,Pending_out).
		
check_loops_minsum_1([Loop2|Loops],Loop,Head,Call,Exp_diff,Summands,Bounded,Pending,Pending_out):-	
		check_loop_minsum(Head,Call,Exp_diff,Loop2,Summands1,Bounded1,Pending,Pending1),!,
		check_loops_minsum_1(Loops,Loop,Head,Call,Exp_diff,Summands2,Bounded2,Pending1,Pending_out),
		append(Summands1,Summands2,Summands),
		append(Bounded1,Bounded2,Bounded).



%add a constant			
check_loop_minsum(Head,Call,Exp_diff,Loop,Summands,[],Pending,Pending):-	
	get_enriched_loop(Loop,Head,Call,Cs),
	term_variables((Head,Call),Vars),
	le_print_int(Exp_diff,Exp_diff_print_int,_),
	nad_entails(Vars,Cs,[Exp_diff_print_int=<0]),	
	negate_le(Exp_diff,Exp_diff_neg),
	le_print_int(Exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta]),!,
	(is_zero(Delta)->
		Summands=[]
	;
		cstr_get_it_name(Loop,Loop_name),
		Summands=[summand(pos,[(Loop_name,Loop_var)],mult([Loop_var,Delta]))]
	),
	(get_param(debug,[])->format('Loop ~p adds a constant ~p ~n',[Loop,Delta]);true).
	
%add an expression	
check_loop_minsum(Head,Call,Exp_diff,Loop,Summands,[],Pending,Pending1):-	
	get_enriched_loop(Loop,Head,Call,Cs),
	term_variables((Head,Call),Vars),
	le_print_int(Exp_diff,Exp_diff_print_int,_),
	nad_entails(Vars,Cs,[Exp_diff_print_int=<0]),	
	negate_le(Exp_diff,Exp_diff_neg),
	term_variables(Head,Vars_head),from_list_sl(Vars_head,Vars_head_set),
	term_variables(Exp_diff_neg,Vars_exp),from_list_sl(Vars_exp,Vars_exp_set),
	difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest),
	max_min_linear_expression_all(Exp_diff_neg, Vars_of_Interest, Cs,min, Maxs),
	Maxs\=[],!,
	cstr_name_aux_var(Aux_name),
	Summands=[summand(pos,[(Aux_name,Aux_var)],mult([Aux_var]))],
	maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxsums),
	save_pending_list(minsum,Loop,Maxsums,Pending,Pending1),
	(get_param(debug,[])->format('Loop ~p adds an expression ~p~n',[Loop,Maxs]);true).
		

%collaborative loop	with constraint
check_loop_minsum(Head,Call,Exp_diff,Loop,[],Bounded,Pending,Pending1):-
		get_enriched_loop(Loop,Head,Call,Cs),
%		term_variables((Head,Call),Vars),	
%		le_print_int(Exp_diff,Exp_diff_print_int,_),
%		nad_entails(Vars,Cs,[Exp_diff_print_int>=0]),
		find_minsum_constraint(Loop,Head,Call,Cs,Exp_diff,New_bounded,Pending,Pending1),!,
		Bounded=[(Loop,New_bounded)],
		(get_param(debug,[])->format('Loop ~p is collaborative with a constraint~n',[Loop]);true).
/*
%collaborative loop	that decreases a constant amount
check_loop_minsum(Head,Call,Exp_diff,Loop,Summands,[],Pending,Pending):-
		get_enriched_loop(Loop,Head,Call,Cs),
%		term_variables((Head,Call),Vars),	
		le_print_int(Exp_diff,Exp_diff_print_int,Denominator),
%		nad_entails(Vars,Cs,[Exp_diff_print_int>=0]),
		nad_maximize([Exp_diff_print_int=Denominator*D|Cs],[D],[Delta]),!,
		cstr_get_it_name(Loop,Loop_name),
		Summands=[summand(neg,[(Loop_name,Loop_var)],mult([Loop_var,Delta]))],
		(get_param(debug,[])->format('Loop ~p collaborates removing a constant ~p ~n',[Loop,Delta]);true).

%collaborative loop	that decreases a variable amount
check_loop_minsum(Head,Call,Exp_diff,Loop,Summands,[],Pending,Pending1):-	
	get_enriched_loop(Loop,Head,Call,Cs),
%	term_variables((Head,Call),Vars),	
	term_variables(Head,Vars_head),from_list_sl(Vars_head,Vars_head_set),
	term_variables(Exp_diff,Vars_exp),from_list_sl(Vars_exp,Vars_exp_set),
	difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest),
%	le_print_int(Exp_diff,Exp_diff_print_int,_),
%	nad_entails(Vars,Cs,[Exp_diff_print_int>=0]),
	max_min_linear_expression_all(Exp_diff, Vars_of_Interest, Cs,max, Maxs),
	Maxs\=[],!,
	cstr_name_aux_var(Aux_name),
	Summands=[summand(neg,[(Aux_name,Aux_var)],mult([Aux_var]))],
	maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxsums),
	save_pending_list(maxsum,Loop,Maxsums,Pending,Pending1),
	(get_param(debug,[])->format('Loop ~p collaborates decreasing an expression ~p~n',[Loop,Maxs]);true).
*/
		
/*
%reset
check_loop_maxsum(Head,_Call,Exp_diff,head,Loop,Summands,[],Pending,Pending1):-
	get_head_expression_part(Head,Exp_diff,Exp),
	copy_term((Head,Exp),(Call,Exp_end)),	
	get_enriched_loop(Loop,Head,Call,Cs),
	term_variables(Head,Vars_head),
%	select_important_variables(Vars_head,Lin_exp,Vars_of_Interest),
	%max_min_linear_expression_all(Exp_end, Vars_of_Interest, Cs,max, Maxs),
	max_min_linear_expression_all(Exp_end, Vars_head, Cs,max, Maxs),
	Maxs\=[],!,
	cstr_name_aux_var(Aux_name),
	Summands=[summand(pos,[(Aux_name,Aux_var)],mult([Aux_var]))],
	maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxsums),
	save_pending_list(maxsum,Loop,Maxsums,Pending,Pending1),
	(get_param(debug,[])->format('Loop ~p has a reset to  ~p~n',[Loop,Maxs]);true).
*/
check_loop_minsum(_Head,_Call,_Exp_diff,Loop,[],[],_Pending,_Pending1):-	
	    (get_param(debug,[])->format('Loop ~p has undefined behavior ~n',[Loop]);true),
		fail.	


%use cacheing to avoid computing things several times
%/*
compute_max_min(Head,Call,Phase,Lin_exp,Max_min,Bounded,New_tops,New_auxs,Pending,Pending):-
	max_min_found(Head,Call,Phase,(Lin_exp_normalized2,Coeff2,Constant2),Max_min,Res),
	normalize_max_min(Lin_exp,(Lin_exp_normalized,Coeff,Constant)),
	Lin_exp_normalized2==Lin_exp_normalized,!,
	divide_fr(Coeff,Coeff2,New_coeff),
	multiply_fr(New_coeff,Constant2,Constant3),
	subtract_fr(Constant,Constant3,Final_constant),

	get_constr_op(Max_min,Op),
	(Res=top(Maxs_out)->
		(0=Final_constant,New_coeff=1->
		maplist(cstr_generate_top_exp(Bounded,Op),Maxs_out,New_tops),
		New_auxs=[]
		;
		cstr_name_aux_var(Aux_name),
		maplist(cstr_generate_top_exp([Aux_name],Op),Maxs_out,New_tops),
		(greater_fr(Final_constant,0)->
		   Internal_exp=exp([(Aux_name,Aux_var)],[],add([mult([Aux_var,New_coeff]),mult([Final_constant])]),add([]))
		   ;
		   negate_fr(Final_constant,Final_constant_neg),
		   Internal_exp=exp([(Aux_name,Aux_var)],[],add([mult([Aux_var,New_coeff])]),add([mult([Final_constant_neg])]))
		),
		New_auxs=[bound(Op,Internal_exp,Bounded)]
		)
	;
	 (Res=aux(Internal_exp2)->
	 	 New_tops=[],
	 	(0=Final_constant,New_coeff=1->		
	 		New_auxs=[bound(Op,Internal_exp2,Bounded)]
		;
		cstr_name_aux_var(Aux_name),
		(greater_fr(Final_constant,0)->
		   Internal_exp=exp([(Aux_name,Aux_var)],[],add([mult([Aux_var,New_coeff]),mult([Final_constant])]),add([]))
		   ;
		   negate_fr(Final_constant,Final_constant_neg),
		   Internal_exp=exp([(Aux_name,Aux_var)],[],add([mult([Aux_var,New_coeff])]),add([mult([Final_constant_neg])]))
		),
		New_auxs=[bound(Op,Internal_exp2,[Aux_name]),bound(Op,Internal_exp,Bounded)]
	    )
	 ;
	 	New_tops=[],
	 	New_auxs=[]
	)
	).
%*/
%use transitive invariant
compute_max_min(Head,Call,Phase,Lin_exp,Max_min,Bounded,New_tops,[],Pending,Pending):-
	get_constr_op(Max_min,Op),
	max_min_top_expression_in_phase(Head,Call,Phase,bound(Op,Lin_exp,Bounded),Maxs_out),
	maplist(cstr_generate_top_exp(Bounded,Op),Maxs_out,New_tops),
	New_tops\=[],!,
	save_max_min_found(Head,Call,Phase,Lin_exp,Max_min,top(Maxs_out)).



%use  increments and resets procedure	
compute_max_min(Head,Call,Phase,Lin_exp,Max_min,Bounded,[Top_exp],[Aux_exp],Pending,Pending_out):-
	get_constr_op(Max_min,Op),
	(Max_min=max->
	check_loops_max(Phase,Head,Call,Lin_exp,Resets,Summands,Pending,Pending_out)
	;
	check_loops_min(Phase,Head,Call,Lin_exp,Resets,Summands,Pending,Pending_out)
	),
	%we have to consider the case where the value is not reseted
	cstr_name_aux_var(Aux_name),
	cstr_generate_top_exp([Aux_name],Op,Lin_exp,Top_exp),
	cexpr_build_internal_exp(Summands,[Aux_name|Resets],Op,Internal_exp),
    Aux_exp=bound(Op,Internal_exp,Bounded),
    save_max_min_found(Head,Call,Phase,Lin_exp,Max_min,aux(Internal_exp)).

    
%failed    
compute_max_min(Head,Call,Phase,Lin_exp,Max_min,_Bounded,[],[],Pending,Pending):-
	save_max_min_found(Head,Call,Phase,Lin_exp,Max_min,none).

			
	
check_loops_max([],_Head,_Call,_Lin_exp,[],[],Pending,Pending).
%nothing happens
check_loops_max([Loop|Loops],Head,Call,Lin_exp,Resets,Summands,Pending,Pending_out):-
	get_enriched_loop(Loop,Head,Call,Cs),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	le_print_int(Lin_exp_diff,Exp_diff_int,_),
	term_variables((Head,Call),Vars),
	% the lin_exp does not increase
	nad_entails(Vars,Cs,[Exp_diff_int>=0]),!,
	check_loops_max(Loops,Head,Call,Lin_exp,Resets,Summands,Pending,Pending_out).

% add a constant
check_loops_max([Loop|Loops],Head,Call,Lin_exp,Resets,[summand(pos,[(Loop_name,Loop_var)],mult([Loop_var,Delta]))|Summands],Pending,Pending_out):-
	get_enriched_loop(Loop,Head,Call,Cs),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	negate_le(Lin_exp_diff,Lin_exp_diff_neg),
	le_print_int(Lin_exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta]),
	greater_fr(Delta,0),!,
	cstr_get_it_name(Loop,Loop_name),
	check_loops_max(Loops,Head,Call,Lin_exp,Resets,Summands,Pending,Pending_out).
	
%add a variable
check_loops_max([Loop|Loops],Head,Call,Lin_exp,Resets,[summand(pos,[(Aux_name,Var_name)],mult([Var_name]))|Summands],Pending,Pending_out):-
	get_enriched_loop(Loop,Head,Call,Cs),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	negate_le(Lin_exp_diff,Lin_exp_diff_neg),
	term_variables(Head,Vars_head),
	select_important_variables(Vars_head,Lin_exp,Vars_of_Interest),
	max_min_linear_expression_all(Lin_exp_diff_neg, Vars_of_Interest, Cs,max, Maxs),
%	max_min_linear_expression_all(Lin_exp_diff_neg, Vars_head, Cs,max, Maxs),
	Maxs\=[],!,
	cstr_name_aux_var(Aux_name),
	maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxsums),
	save_pending_list(maxsum,Loop,Maxsums,Pending,Pending1),
	check_loops_max(Loops,Head,Call,Lin_exp,Resets,Summands,Pending1,Pending_out).		
		
%reset			
check_loops_max([Loop|Loops],Head,Call,Lin_exp,[Aux_name|Resets],Summands,Pending,Pending_out):-
	get_enriched_loop(Loop,Head,Call,Cs),
	copy_term((Head,Lin_exp),(Call,Lin_exp_p)),
	term_variables(Head,Vars_head),
%	select_important_variables(Vars_head,Lin_exp,Vars_of_Interest),
%	max_min_linear_expression_all(Lin_exp_p, Vars_of_Interest, Cs,max, Maxs),
	max_min_linear_expression_all(Lin_exp_p, Vars_head, Cs,max, Maxs),
	Maxs\=[],!,
	cstr_name_aux_var(Aux_name),
	maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxtops),
	save_pending_list(max,Loop,Maxtops,Pending,Pending1),
	check_loops_max(Loops,Head,Call,Lin_exp,Resets,Summands,Pending1,Pending_out).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


check_loops_min([],_Head,_Call,_Lin_exp,[],[],Pending,Pending).
%nothing happens
% the Lin_exp does not decrease
check_loops_min([Loop|Loops],Head,Call,Lin_exp,Resets,Summands,Pending,Pending_out):-
	get_enriched_loop(Loop,Head,Call,Cs),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	le_print_int(Lin_exp_diff,Exp_diff_int,_),
	term_variables((Head,Call),Vars),
	nad_entails(Vars,Cs,[Exp_diff_int=<0]),!,
	check_loops_min(Loops,Head,Call,Lin_exp,Resets,Summands,Pending,Pending_out).

% decreases by a constant
check_loops_min([Loop|Loops],Head,Call,Lin_exp,Resets,[summand(neg,[(Loop_name,Loop_var)],mult([Loop_var,Delta]))|Summands],Pending,Pending_out):-
	get_enriched_loop(Loop,Head,Call,Cs),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	le_print_int(Lin_exp_diff,Exp_diff_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_int=Exp_diff_denominator*D|Cs],[D],[Delta]),
	greater_fr(Delta,0),!,
	cstr_get_it_name(Loop,Loop_name),
	check_loops_min(Loops,Head,Call,Lin_exp,Resets,Summands,Pending,Pending_out).
	
%add a variable
check_loops_min([Loop|Loops],Head,Call,Lin_exp,Resets,[summand(neg,[(Aux_name,Var_name)],mult([Var_name]))|Summands],Pending,Pending_out):-
	get_enriched_loop(Loop,Head,Call,Cs),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	term_variables(Head,Vars_head),
	max_min_linear_expression_all(Lin_exp_diff, Vars_head, Cs,max, Maxs),
	Maxs\=[],!,
	cstr_name_aux_var(Aux_name),
	maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxsums),
	save_pending_list(maxsum,Loop,Maxsums,Pending,Pending1),
	check_loops_min(Loops,Head,Call,Lin_exp,Resets,Summands,Pending1,Pending_out).		
		
%reset			
check_loops_min([Loop|Loops],Head,Call,Lin_exp,[Aux_name|Resets],Summands,Pending,Pending_out):-
	get_enriched_loop(Loop,Head,Call,Cs),
	copy_term((Head,Lin_exp),(Call,Lin_exp_p)),
	term_variables(Head,Vars_head),

	max_min_linear_expression_all(Lin_exp_p, Vars_head, Cs,min, Mins),
	Mins\=[],!,
	cstr_name_aux_var(Aux_name),
	maplist(cstr_generate_top_exp([Aux_name],lb),Mins,Mintops),
	save_pending_list(min,Loop,Mintops,Pending,Pending1),
	check_loops_min(Loops,Head,Call,Lin_exp,Resets,Summands,Pending1,Pending_out).		
	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simple_multiplication(Head,Call,Loop,Lin_exp,Bounded,Aux_exp,Max_min,Pending,Pending_out):-	
	get_constr_op(Max_min,Op),
	get_enriched_loop(Loop,Head,Call,Cs),
	cstr_name_aux_var(Aux_name),
	cstr_get_it_name(Loop,Loop_name),
	Internal_exp=exp([(Aux_name,Aux_var),(Loop_name,It_var)],[],add([mult([It_var,Aux_var])]),add([])),
	(is_head_expression(Head,Lin_exp)->
		Max_tops=[bound(Op,Lin_exp,[Aux_name])]
	;
	 Head=..[_|Vars_head],
	 max_min_linear_expression_all(Lin_exp, Vars_head, Cs,Max_min, Maxs_exps),
	 maplist(cstr_generate_top_exp([Aux_name],Op),Maxs_exps,Max_tops)
	 ),
	save_pending_list(Max_min,Loop,Max_tops,Pending,Pending_out),
    Aux_exp=bound(Op,Internal_exp,Bounded).	
	
get_constr_op(max,ub).
get_constr_op(min,lb).	


save_sum_found(Head,Call,Loop,Lin_exp,Max_min,Bounded,Tops,Auxs):-
	from_list_sl(Bounded,Bounded_set),
	substitute_bounded_by_var(Auxs,Bounded_set,Var,Auxs1),
	substitute_bounded_by_var(Tops,Bounded_set,Var,Tops1),
	semi_normalize_le(Lin_exp,Coeff,Lin_exp_normalized),
	ground_copy((Head,Call,Lin_exp_normalized),(_,_,Lin_exp_norm_ground)),
	assert(sum_found(Loop,Lin_exp_norm_ground,Max_min,Head,Call,Coeff,Var,Tops1,Auxs1)).
	
save_max_min_found(Head,Call,Phase,Lin_exp,Max_min,Exp):-
	normalize_max_min(Lin_exp,(Lin_exp_normalized,Coeff,Constant)),
	assert(max_min_found(Head,Call,Phase,(Lin_exp_normalized,Coeff,Constant),Max_min,Exp)).

normalize_max_min(Lin_exp,([]+0,1,Constant)):-
	Lin_exp=[]+Constant,!.
	
normalize_max_min(Lin_exp,(Lin_exp_normalized,Coeff,Constant)):-
	Lin_exp=Coeffs+Constant,
	Lin_exp_wo_constant=Coeffs+0,
	semi_normalize_le(Lin_exp_wo_constant,Coeff,Lin_exp_normalized).
	
substitute_bounded_by_var([],_,_,[]).
substitute_bounded_by_var([bound(Op,Exp,Bounded1)|Constrs],Bounded_set,Var,[bound(Op,Exp,[Var|Bounded2_set])|Constrs2]):-
	from_list_sl(Bounded1,Bounded1_set),
	difference_sl(Bounded1_set,Bounded_set,Bounded2_set),
	length(Bounded1_set,N1),length(Bounded_set,N),length(Bounded2_set,N2),
	N22 is N1-N, N22=N2,!,
	substitute_bounded_by_var(Constrs,Bounded_set,Var,Constrs2).
substitute_bounded_by_var([_|Constrs],Bounded_set,Var,Constrs2):-
	substitute_bounded_by_var(Constrs,Bounded_set,Var,Constrs2).
	

cexpr_build_internal_exp([],[Aux_name],_,exp([(Aux_name,Aux_var)],[],add([mult([Aux_var])]),add([]))).
cexpr_build_internal_exp([],Resets,ub,exp(Index,[],add([mult([max(Reset_vars)])]),add([]))):-
	generate_index(Resets,[],Reset_vars,Index).
cexpr_build_internal_exp([],Resets,lb,exp(Index,[],add([mult([min(Reset_vars)])]),add([]))):-
	generate_index(Resets,[],Reset_vars,Index).
	
cexpr_build_internal_exp([summand(pos,Index,Summand)|Summands],Resets,Op,exp(Index_pos1,Index_neg,add([Summand|Pos]),Neg)):-	
	cexpr_build_internal_exp(Summands,Resets,Op,exp(Index_pos,Index_neg,add(Pos),Neg)),
	append(Index,Index_pos,Index_pos1).
cexpr_build_internal_exp([summand(neg,Index,Summand)|Summands],Resets,Op,exp(Index_pos,Index_neg1,Pos,add([Summand|Neg]))):-	
	cexpr_build_internal_exp(Summands,Resets,Op,exp(Index_pos,Index_neg,Pos,add(Neg))),
	append(Index,Index_neg,Index_neg1).	

select_important_variables(Vars_head,Lin_exp,Vars_of_Interest):-
	from_list_sl(Vars_head,Vars_head_set),
	term_variables(Lin_exp,Vars_exp),
	from_list_sl(Vars_exp,Vars_exp_set),
	difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest).
	
generate_index([],Index_accum,[],Index_accum).
generate_index([Name|Names],Index_accum,[Var|Vars],Index):-
		generate_index(Names,[(Name,Var)|Index_accum],Vars,Index).
put_inside_mult(Factor,mult([Factor])).



get_bounded_exp([],[],[]).
get_bounded_exp([(Loop,Bounded_in_loop)|Bounded],[Loop|Bounded_loops],Bounded_vars1):-
	get_bounded_exp(Bounded,Bounded_loops,Bounded_vars),
	append(Bounded_in_loop,Bounded_vars,Bounded_vars1).
	

	
cond_add_same_loop_increment(Head,Loop,Exp,Summands,[summand(pos,[(Loop_name,Loop_var)],mult([Loop_var,Cnt]))|Summands]):-
		\+is_head_expression(Head,Exp),
		Exp=_Coeffs+Cnt,
		greater_fr(Cnt,0),!,
		cstr_get_it_name(Loop,Loop_name).	
cond_add_same_loop_increment(_Head,_Loop,_Exp,Summands,Summands).

:- use_module('../utils/polyhedra_optimizations',[
			nad_entails_aux/3,nad_normalize_polyhedron/2,
			slice_relevant_constraints_and_vars/5]).	

get_enriched_loop(Loop,Head,Call,Total_cs):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),	
	forward_invariant_temp(Head,Call,Forward_inv),
	append(Forward_inv,Cs,Total_cs).
				
get_head_expression_part(Head,Exp_diff+Cnt,Exp+Cnt):-
	term_variables(Head,Vars_head),from_list_sl(Vars_head,Vars_head_set),
	include(coeff_not_in_set(Vars_head_set),Exp_diff,Exp).
	
coeff_not_in_set(Set,(Var,_Fr)):-
	contains_sl(Set,Var).

is_head_expression(Head,Exp):-
	copy_term((Head,Exp),(Head2,Exp2)),
	numbervars(Head2,0,_),
	ground(Exp2).
	
			
find_maxsum_constraint(Loop,Head,Call,Cs,Exp_diff,Flag,Bounded,Pending,Pending_out):-
		extract_pending(Loop,maxsum,Pending,(Exp2,Bounded),Pending_out),
		term_variables((Head,Call),Vars),
		le_print_int(Exp2,Exp2_print_int,_),
		nad_entails(Vars,Cs,[Exp2_print_int>=0]),
		subtract_le(Exp_diff,Exp2,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),
		(Flag=head(Exp_original)->
		   subtract_le(Exp_original,Exp2,Exp_diff_base_case),
		   le_print_int(Exp_diff_base_case,Exp_diff_base_case_print,_),
		   nad_entails(Vars,Cs,[Exp_diff_base_case_print>=0])
		  ;
		  true),
		!.
		
		
find_minsum_constraint(Loop,Head,Call,Cs,Exp_diff,Bounded,Pending,Pending_out):-
		extract_pending(Loop,minsum,Pending,(Exp2,Bounded),Pending_out),
		term_variables((Head,Call),Vars),
		subtract_le(Exp2,Exp_diff,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),!.		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

empty_pending(pending([],[],[],[])).

print_lin_exp_in_phase(Head,Call,Exp):-
	copy_term((Head,Call,Exp),(Head2,Call2,Exp2)),
	write_le(Exp2,Exp_print),
	numbervars((Head2,Call2),0,_),
	format('~p -> ~p : ~p ~n',[Head2,Call2,Exp_print]).

print_pending_info(Head,Call,Type,Lin_exp,Pending):-
	copy_term((Head,Call,Lin_exp),(Head2,Call2,Lin_exp2)),
	write_le(Lin_exp2,Exp2_print),
	numbervars((Head2,Call2),0,_),
	print_pending_structure(Head,Call,Pending),	
	writeln(computing(Type,Exp2_print)).
	
print_pending_structure(Head,Call,Pending):-
	copy_term((Head,Call,Pending),(Head2,Call2,pending(Maxs,Mins,Maxsums,Minsums))),
	numbervars((Head2,Call2),0,_),
	format('Maxs:~n',[]),
	maplist(print_pending_elem,Maxs),
	format('Mins:~n',[]),
	maplist(print_pending_elem,Mins),
	format('Maxsums:~n',[]),
	maplist(print_pending_elems_loop,Maxsums),
	format('Minsums:~n',[]),
	maplist(print_pending_elems_loop,Minsums).

print_pending_elem((Lin_exp,Bounded)):-
	write_le(Lin_exp,Lin_exp_print),
	format('~p  ~p ~n',[Lin_exp_print,Bounded]).
print_pending_elems_loop((Loop,Elems)):-
	format('Loop:~p ~n',[Loop]),
	maplist(print_pending_elem,Elems).

save_pending_list(Type,Loop,List_tops,Pending,Pending_out):-
	foldl(save_pending(Type,Loop),List_tops,Pending,Pending_out).

union_pending(pending(Maxs1,Mins1,Maxsums1,Minsums1),pending(Maxs2,Mins2,Maxsums2,Minsums2),pending(Maxs3,Mins3,Maxsums3,Minsums3)):-
	union_sl(Maxs1,Maxs2,Maxs3),
	union_sl(Mins1,Mins2,Mins3),
	join_mm(Maxsums1,Maxsums2,Maxsums3),
	join_mm(Minsums1,Minsums2,Minsums3).
	
	
save_pending(max,_,bound(ub,Lin_exp,Bounded),Pending,Pending_out):-
	Pending=pending(Maxs,Mins,Maxsums,Minsums),
	insert_sl(Maxs,(Lin_exp,Bounded),Maxs1),
	Pending_out=pending(Maxs1,Mins,Maxsums,Minsums).
save_pending(min,_,bound(lb,Lin_exp,Bounded),Pending,Pending_out):-
	Pending=pending(Maxs,Mins,Maxsums,Minsums),
	insert_sl(Mins,(Lin_exp,Bounded),Mins1),
	Pending_out=pending(Maxs,Mins1,Maxsums,Minsums).	

save_pending(maxsum,Loop,bound(ub,Lin_exp,Bounded),Pending,Pending_out):-
	Pending=pending(Maxs,Mins,Maxsums,Minsums),
	(lookup_lm(Maxsums,Loop,Maxsum_set)->
		true
		;
		empty_sl(Maxsum_set)
	),	
	insert_sl(Maxsum_set,(Lin_exp,Bounded),Maxsum_set1),
	insert_lm(Maxsums,Loop,Maxsum_set1,Maxsums1),
	Pending_out=pending(Maxs,Mins,Maxsums1,Minsums).	

save_pending(minsum,Loop,bound(lb,Lin_exp,Bounded),Pending,Pending_out):-
	Pending=pending(Maxs,Mins,Maxsums,Minsums),
	(lookup_lm(Minsums,Loop,Minsum_set)->
		true
		;
		empty_sl(Minsum_set)
	),	
	insert_sl(Minsum_set,(Lin_exp,Bounded),Minsum_set1),
	insert_lm(Minsums,Loop,Minsum_set1,Minsums1),
	Pending_out=pending(Maxs,Mins,Maxsums,Minsums1).
	
get_one_pending(pending([Element|Maxs],Mins,Maxsums,Minsums),max,Element,pending(Maxs,Mins,Maxsums,Minsums)):-!.
get_one_pending(pending([],[Element|Mins],Maxsums,Minsums),min,Element,pending([],Mins,Maxsums,Minsums)):-!.
get_one_pending(pending([],[],[(Loop,Multimap)|Maxsums],Minsums),maxsum(Loop),Element,pending([],[],Maxsums_out,Minsums)):-
	get_one_pending_1(Multimap,Element,Multimap1),
	(Multimap1=[]->
		Maxsums_out=Maxsums
	;
		Maxsums_out=[(Loop,Multimap1)|Maxsums]
	).
get_one_pending(pending([],[],[],[(Loop,Multimap)|Minsums]),minsum(Loop),Element,pending([],[],[],Minsums_out)):-
	get_one_pending_1(Multimap,Element,Multimap1),
	(Multimap1=[]->
		Minsums_out=Minsums
	;
		Minsums_out=[(Loop,Multimap1)|Minsums]
	).	
get_one_pending_1([Element|Multimap],Element,Multimap).

extract_pending(Loop,maxsum,pending(Maxs,Mins,Maxsums,Minsums),Element,pending(Maxs,Mins,Maxsums1,Minsums)):-
	lookup_lm(Maxsums,Loop,Elements),
	select(Element,Elements,Elements1),
	(Elements1=[]->
		delete_lm(Maxsums,Loop,Maxsums1)
		;
		insert_lm(Maxsums,Loop,Elements1,Maxsums1)
	).
extract_pending(Loop,minsum,pending(Maxs,Mins,Maxsums,Minsums),Element,pending(Maxs,Mins,Maxsums,Minsums1)):-
	lookup_lm(Minsums,Loop,Elements),
	select(Element,Elements,Elements1),
	(Elements1=[]->
		delete_lm(Minsums,Loop,Minsums1)
		;
		insert_lm(Minsums,Loop,Elements1,Minsums1)
	).	


save_new_phase_top(Head,Call,Phase,Top):-
	assert(new_phase_top(Head,Call,Phase,Top)).
save_new_phase_aux(Head,Call,Phase,Top):-
	assert(new_phase_aux(Head,Call,Phase,Top)).
	
collect_phase_results(Head,Call,Phase,Tops_max,Tops_min,Auxs):-
	bagof_no_fail(Top,(new_phase_top(Head,Call,Phase,Top)),Tops),
	partition(is_ub_top,Tops,Tops_max,Tops_min),
	bagof_no_fail(Aux,(new_phase_aux(Head,Call,Phase,Aux)),Auxs),
	retractall(new_phase_top(_,_,_,_)),
	retractall(new_phase_aux(_,_,_,_)).
	
is_ub_top(bound(ub,_,_)).

is_zero(0).
is_zero(0/1).

rf_limit(N):-
	get_param(n_rankings,[N]).
	
get_difference_version(Head,Call,Rf,Rf_diff):-
	copy_term((Head,Rf),(Call,Rfp)),
	subtract_le(Rf,Rfp,Rf_diff).		
	
le_print_int(Lin_exp,Exp,Den):-
		integrate_le(Lin_exp,Den,Lin_exp_nat),
		write_le(Lin_exp_nat,Exp).
	
get_ranking_functions_constraints(Max,Head,Call,Phase,Chain,Top):-
		bagof_no_fail(Rf,
	ranking_function(Head,Chain,Phase,Rf)
	   ,Rfs),
	   ut_split_at_pos(Rfs,Max,Rfs_selected,_),
	   maplist(get_difference_version(Head,Call),Rfs_selected,Rfs_diff),
	   maplist(cstr_get_it_name,Phase,Bounded),
	   append(Rfs_selected,Rfs_diff,Rfs_total),
	   maplist(cstr_generate_top_exp(Bounded,ub),Rfs_total,Top).
	   
get_ranking_functions_lower_constraints(Max,Head,Call,Phase,Chain,Top):-
		bagof_no_fail(Df,
			get_lower_bound_val(Head,Call,Chain,Phase,Df)
	   ,Dfs),
	   ut_split_at_pos(Dfs,Max,Dfs_selected,_),
	   maplist(cstr_get_it_name,Phase,Bounded),
	   maplist(cstr_generate_top_exp(Bounded,lb),Dfs_selected,Top).
	   
get_lower_bound_val(Head,Call,Chain,Phase,LB):-
	ranking_function(Head,Chain,Phase,Rf),
	copy_term((Head,Rf),(Call,Rf1)),
	subtract_le(Rf,Rf1,Rf_diff),
	integrate_le(Rf_diff,Den,Rf_diff_nat),
	write_le(Rf_diff_nat,Rf_diff_nat_print),
	phase_loop(Phase,_,Head,Call,Phi),
	Constraint= (Den* D = Rf_diff_nat_print),
	Cs_1 = [ Constraint | Phi],
	nad_maximize(Cs_1,[D],[Delta]),
	inverse_fr(Delta,Delta_inv),
	multiply_le(Rf_diff,Delta_inv,LB).		
	
get_partial_lower_bound(Head,Call,_Chain,Loop,Lb):-
	partial_ranking_function(Head,_,_Phase,Loops,Rf,_,_),
	contains_sl(Loops,Loop),	
	get_difference_version(Head,Call,Rf,Rf_diff),
	integrate_le(Rf_diff,Den,Rf_diff_nat),
	write_le(Rf_diff_nat,Rf_diff_nat_print),
	get_enriched_loop(Loop,Head,Call,Cs),
	Constraint= (Den* D = Rf_diff_nat_print),
	Cs_1 = [ Constraint | Cs],
	nad_maximize(Cs_1,[D],[Delta]),
	inverse_fr(Delta,Delta_inv),
	multiply_le(Rf_diff,Delta_inv,Lb).
	
is_difference(Head,Call,Lin_exp,max,Loop,Total_exps):-
	get_enriched_loop(Loop,Head,Call,Cs),	
	term_variables((Head,Call),Vars),
	rf_limit(Max_candidates),
	difference_constraint_farkas_ub(Head,Call,Cs,Lin_exp,Diff_list,Diff_list2),
	get_N_positive_candidates(Diff_list,Max_candidates,Vars,Cs,Diff_list_selected),
	ut_split_at_pos(Diff_list2,Max_candidates,Diff_list_selected2,_),
	append(Diff_list_selected,Diff_list_selected2,Total_exps).
	
	
is_difference(Head,Call,Lin_exp,min,Loop,Diff_list_selected):-
	get_enriched_loop(Loop,Head,Call,Cs),	
	rf_limit(Max_candidates),
	difference_constraint_farkas_lb(Head,Call,Cs,Lin_exp,Diff_list),
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_).	
	
get_N_positive_candidates([],_,_,_,[]).
get_N_positive_candidates(_,0,_,_,[]).
get_N_positive_candidates([Lin_exp|List],N,Vars,Cs,[Lin_exp|Selected]):-
	N>0,N1 is N-1,
	le_print_int(Lin_exp,Exp,_Den),
	nad_entails(Vars,Cs,[Exp>=0]),
	get_N_positive_candidates(List,N1,Vars,Cs,Selected).
get_N_positive_candidates([_Lin_exp|List],N,Vars,Cs,Selected):-
	N>0,N1 is N-1,
	get_N_positive_candidates(List,N1,Vars,Cs,Selected).		
	
max_min_top_expression_in_phase(Head,Call,Phase,bound(Op,Lin_exp,_Bounded),Maxs_out):-
	phase_transitive_closure(Phase,_,Head_total,Head,Cs_star_trans),
	phase_loop(Phase,_,Head,Call,Cs),
	ut_flat_list([Cs_star_trans,Cs],Context),
	term_variables(Head_total,Vars_of_Interest),
	(Op=ub->
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,max, Maxs_out)
	;
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,min, Maxs_out)
	),
	Head_total=Head.		