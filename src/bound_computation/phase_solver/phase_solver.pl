/** <module> phase_solver

This module computes the cost structure of a phase.
If the phase has linear recursion, the cost structure is  in terms of the variables 
at the beginning and the end of the phase.

If the phase has multiple recursion the cost structure depends only on the input variables.
The predicate for multiple recursion also receives the costs of the rest of the chain.
The possible continuations are 'tails'.

The algorithm is iterative. We have a data structure (a tuple of Pending sets) that stores constraints that need to be treated.
For each constraint we might need to obtain the sum, the maximum or minimum of the constraint in the phase.
For this purpose, we apply the different strategies.

The strategies generate new costraints for the phase and can also add elements to the Pending sets.
The procedure uses dynamic progamming to avoid recomputing constraints that have already been computed.

By default we add constraints using the ranking functions directly at the beginning of the computation.
These constraints are useful in most cases and that allows us to simplify the rest of the strategies.

 Additional data structures used in this module are:
 
 Loop_vars= loop_vars(Head:term,Calls:list(term))
 to describe the variables of a loop or a tail in a phase
  
 Pending_constrs contains the information of the constraints that are pending to be computed
 It has the form
 pending(Head,Maxs_mins,Level_sums,Sums)
 where
  * Head is the head of the cost equations of the phase (the constraints in Maxs_mins are expressed in terms of these variables)
  * Maxs_mins=list_set((Depth,Fconstr))
  * Levels=list_set((Depth,Fconstr))
   At this moment this is unused as we do not have a level strategy anymore.
  * Sums=multimap((loop_id,Loop_vars), (Depth,Fconstr))
 Sums are for a specific loop whereas Max_mins and Levels are general for the whole phase. 
 
 In the case of multiple recursion loop_id can also be a tail (a chain that can continue the evaluation)
 
 Depth represents the depth of the recursion and is used to avoid infinite computations.

@author Antonio Flores Montoya

@copyright Copyright (C) 2014,2015,2016 Antonio Flores Montoya

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

:- module(phase_solver,[
	compute_phase_bounds/3,
	%compute_multiple_rec_phase_cost/7,
	state_get_property/3,
	state_get_one_pending/3,
	state_save_new_fconstrs/4,
	state_save_new_iconstrs/3,
	state_save_pending_list/7,
	state_get_used_set/2,
	state_get_used_constr/2,
	state_get_candidate_result/3,
	state_save_candidate_result/3,
	type_of_loop/2
	]).

:- use_module(phase_common).
:- use_module(phase_inductive_sum_strategy,[inductive_sum_strategy/8]).			
:- use_module(phase_basic_product_strategy,[basic_product_strategy/8]).	
:- use_module(phase_triangular_strategy,[triangular_strategy/7]).	
:- use_module(phase_max_min_strategy,[max_min_strategy/8]).	

:- use_module('../constraints_maximization',[max_min_linear_expression_all/5]).					      
:- use_module('../../refinement/chains',[
	phase_get_property/3,
	phase_get_rfs/2,
	phase_add_property/4,
	phase_get_pattern/2,
	is_multiple_phase/2
	]).	

:- use_module('../../refinement/loops',[
	loops_get_head/2,
	loops_get_list_fresh_with_id/3,
	loop_get_cost/2,
	loops_get_loop/3,
	loop_head/2,
	loop_calls/2,
	loop_ioVars/2
	]).				

:- use_module('../../IO/params',[get_param/2]).		
:- use_module('../../IO/output',[
	print_or_log/2,
	print_header/3,
	print_phase_solving_state/1,
	print_selected_pending_constraint/3,
	print_phase_computation_changes/1
	]).		
  		
:- use_module('../../utils/cofloco_utils',[
	tuple/3,
	zip_with_op/3,
	ground_copy/2,
	bagof_no_fail/3
	]).	
	
:- use_module('../../utils/cost_structures',[
	cstr_extend_variables_names/3,
	cstr_simplify/2,
	cstr_sort_iconstrs/2,
	cstr_add_fconstrs/3,
	cstr_add_iconstrs/3,
	
	new_itvar/1,
	get_loop_itvar/2,
			
	is_ub_bconstr/1,
	is_constant_bconstr/1,
			
	astrexp_new/2,
	pstrexp_pair_empty/1,
	pstrexp_pair_add/3,
	cstr_propagate_sums/4,
	fconstr_new/4,
	iconstr_new/4,
	cstr_empty/1,
	cstr_join/3
	]).			

:- use_module('../../utils/polyhedra_optimizations',[
	nad_is_bottom/1,
	nad_normalize_polyhedron/2
	]).			

:- use_module(stdlib(numeric_abstract_domains),[
	nad_maximize/3,
	nad_project/3,
	nad_list_lub/2,
	nad_glb/3
	]).
:- use_module(stdlib(linear_expression),[
	integrate_le/3,
	write_le/2,
	multiply_le/3,
	semi_normalize_le/3,
	subtract_le/3,
	negate_le/2,
	parse_le_fast/2
	]).							
:- use_module(stdlib(fraction),[
	inverse_fr/2,
	greater_fr/2,
	geq_fr/2,
	divide_fr/3,
	negate_fr/2,
	multiply_fr/3,
	subtract_fr/3
	]).


:- use_module(stdlib(utils),[
	ut_flat_list/2,
	ut_split_at_pos/4
	]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map)).
:- use_module(stdlib(multimap)).

:- use_module(library(apply_macros)).
:- use_module(library(lists)).


compute_phase_bounds(chains(Phases,Chains),Loops,chains(Phases2,Chains)):-
	maplist(compute_phase_bound(Loops),Phases,Phases2).

compute_phase_bound(Loops,Phase,Phase2):-
	phase_get_pattern(Phase,Phase_pattern),
	%multiple phase
	(is_multiple_phase(Phase_pattern,Loops)->
		Phase2=Phase
		;
		(get_param(debug,[])->
	 		print_header('Computing cost of phase ~p ~n',[Phase_pattern],4)
	 		;
	 		true
		),
		%non-iterative phase
		(number(Phase_pattern)->
			loops_get_loop(Loops,Phase_pattern,Loop),
			loop_head(Loop,Head),
			loop_calls(Loop,Calls),
			loop_get_cost(Loop,Cost)
		;
		%linear phase
			loops_get_head(Loops,Head),
			copy_term(Head,Call),
			Calls=[Call],
			loops_get_list_fresh_with_id(Loops,Phase_pattern,Phase_loops),
	    	compute_phase_cost(Head,Call,Phase,Phase_loops,Cost)
	    ),
	    phase_add_property(Phase,cost,cost(Head,Calls,Cost),Phase2)
	 ).



compute_phase_cost(Head,Call,Phase,Phase_loops,Cost_final):-
	state_empty(Empty_state),
	state_set_property(Empty_state,phase_type,single,State1),
	state_set_property(State1,phase,Phase,State2),
    %get the cost of each iterative component of the phase	
	maplist(loop_get_cost_and_vars,Phase_loops,Costs,Loop_vars),
	
	compute_phase_cost_generic(State2,loop_vars(Head,[Call]),Phase_loops,Loop_vars,Costs,Cost_final).
	
loop_get_cost_and_vars((_Id,Loop),Cost,loop_vars(Head,Calls)):-
	loop_get_cost(Loop,Cost),
	loop_head(Loop,Head),
	loop_calls(Loop,Calls).
/*
compute_multiple_rec_phase_cost(Head,IOvars,Phase,Chain_prefix,Chain_rest,Costs_tails_n,Cost_final):-
	% the multiple recursion phase case and the linear case
	(
	Chain_rest=[multiple(Phase,Tails_n)],
	Phase_4_inv=multiple(Phase,Tails_n),
	Linear_multiple='multiple'
	;
	Chain_rest=[Phase|Tail],
	Tails_n=[Tail],
	Phase_4_inv=Phase,
	Linear_multiple='linear'
	),
	init_solving_phase(Phase),
	%if the phase is non-terminating, we have to remove the dummy tail
	(Tails_n=[[]|Tails]->
	   	Costs_tails_n=[_|Costs_tails],
	   	%record this fact for usage in the strategies
	   	assert(phase_type(non_terminating))
	   	;
	   	Costs_tails_n=Costs_tails,
	   	Tails_n=Tails
	),
	assert(phase_type(multiple)),
	nad_glb(Forward_invariant,Backward_invariant,Total_inv),
	save_enriched_loops(Head,Total_inv,Phase,Phase_feasible),
	
	%get the cost of each iterative component of the phase
	profiling_start_timer(equation_cost),
	maplist(get_equation_loop_cost(Head,IOvars,(Forward_hash,Forward_invariant,Backward_invariant)),Phase_vars_loops,Phase_feasible,Costs_loops),
	
	profiling_stop_timer_acum(equation_cost,_),
	
	%for the tails
	get_extra_tail_inv(Head,Extra_tail_inv),
	save_enriched_tails(Head,Extra_tail_inv,Tails,Tails_feasible,Costs_tails,Cost_tails_feasible),
	maplist(get_tail_phase_vars(Head),Tails_feasible,Phase_vars_tails),
	
	%put together all the ids, variables and costs
	append(Phase_feasible,Tails_feasible,Loops_tails_feasible),
	append(Phase_vars_loops,Phase_vars_tails,Phase_vars),
	append(Costs_loops,Cost_tails_feasible,Costs),
	compute_phase_cost_generic(Head,IOvars,loop_vars(Head,[]),Loops_tails_feasible,Phase_vars,Costs,Cost_final),!,
	assertz(phase_cost(Chain_rest,Head,[],Cost_final)).
*/
compute_phase_cost_generic(State,Final_vars,Phase_loops,Loop_vars,Costs,Cost_final):-
	maplist(tuple,Loop_ids,_,Phase_loops),
	maplist(cstr_propagate_sums,Loop_ids,Costs,Costs_propagated2,Max_min_pairs_Sums_pairs),
	%new cost structure
	cstr_empty(Empty_cstr),
	foldl(cstr_join,Costs_propagated2,Empty_cstr,New_cost_initial),	
	state_set_property(State,new_cost,costWvars(Final_vars,New_cost_initial),State2),
	%add constraints from the ranking functions
	cond_add_n_elem_constraints(State2,State3),

	generate_initial_pending(Phase_loops,Loop_vars,Max_min_pairs_Sums_pairs,Pending),
	state_set_pending(State3,Pending,State4),
	%main predicate
	
	compute_all_pending(Phase_loops,State4,State5),
	state_get_property(State5,new_cost,costWvars(Final_vars,New_cost)),
	
	(get_param(debug,[])->
	 		print_header('Simplifying cost structure  ~n',[],4)
	 		;
	 		true),		
	cstr_sort_iconstrs(New_cost,Ncost_sorted),		
	cstr_simplify(Ncost_sorted,Cost_final).


generate_initial_pending(Phase_loops,Phase_vars,Max_min_pairs_Sums_pairs,Pending2):-
	%unpack result of propagation
	maplist(tuple,Max_mins,Sums,Max_min_pairs_Sums_pairs),
	%we add pending sums for the number of iterations of each loop as they will be needed in most occasions anyway
	% this way, we can always assume they are computed
	maplist(tuple,Loop_ids,_,Phase_loops),
	maplist(get_it_sum_constraint(ub),Loop_ids,It_cons_max), 
	maplist(append,It_cons_max,Sums,Sums1),
	(get_param(compute_lbs,[])->
    	maplist(get_it_sum_constraint(lb),Loop_ids,It_cons_min),
    	maplist(append,It_cons_min,Sums1,Sums2)
    	;
    	 Sums2=Sums1
     ),
	length(Phase_loops,N),
	%this is completely heuristic
	Max_pending is 2*N+2,
	pending_empty(Max_pending,Empty_pending),
	%we start from depth 0
	
	foldl(save_pending_list(max_min,0),Phase_vars,Loop_ids,Max_mins,Empty_pending,Pending1),
	foldl(save_pending_list(sum,0),Phase_vars,Loop_ids,Sums2,Pending1,Pending2).

	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_tail_phase_vars(Head,_,loop_vars(Head,[])).

get_it_sum_constraint(ub,Loop,[bound(ub,[]+1,[Loop_name])]):-!,
	get_loop_itvar(Loop,Loop_name).
get_it_sum_constraint(lb,Loop,[bound(lb,[]+1,[Loop_name])]):-
	get_loop_itvar(Loop,Loop_name).
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! compute_all_pending(Phase:phase,Pending:pending_constrs)
% the main loop of the computation:
% compute one pending element at a time unil there are no more pending elements

	
compute_all_pending(Phase_loops,State,State3):-
	print_phase_solving_state(State),
	(compute_pending(Phase_loops,State,State2)->
		compute_all_pending(Phase_loops,State2,State3)
		;
		State3=State
	).


%! compute_pending(Head:term,Call:term,Phase:phase,Pending:pending_constrs,Pending_out:pending_constrs)
% extract one pending constraint from Pending and compute it
% each pending element has a Depth associated to avoid infinite computations, each new pending element created will have
% an increased depth and no pending elements will be added beyond the maximum depth
%
% The result of computing a pending element is a set of final constraints (New_fconstrs) and intermediate constraints (New_iconstrs)
% that are stored in the database
compute_pending(Phase_loops,State,State3):-
	state_get_one_pending(State,pending(Type,Loop_id,Depth,Loop_vars,Constr),State2),
	print_selected_pending_constraint(Loop_vars,Type,Constr),
	compute_pending_element(Type,Loop_id,Depth,Loop_vars,Constr,Phase_loops,State2,State3).

%case distinction according to what we have to compute

compute_pending_element(sum,Loop_id,Depth,Loop_vars,Constr,Phase_loops,State,State2):-
	compute_sum(Loop_id,Depth,Loop_vars,Constr,Phase_loops,State,State2).

compute_pending_element(max_min,Loop_id,Depth,Loop_vars,Constr,Phase_loops,State,State2):-
	compute_max_min(Loop_id,Depth,Loop_vars,Constr,Phase_loops,State,State2).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%trivial case where we have 0
compute_sum(_Loop_id,_Depth,Loop_vars,Constr,_Phase_loops,State,State2):-
	Constr=bound(_,[]+0,_),!,
	state_save_new_fconstrs(State,Loop_vars,[Constr],State2).
	


% Stored solution
compute_sum(Loop_id,_Depth,Loop_vars,Constr,_Phase_loops,State,State3):-
	state_get_found(State,pattern(sum,Constr,Loop_vars,Loop_id),result(Fconstrs,Iconstrs)),
	state_save_new_fconstrs(State,Loop_vars,Fconstrs,State2),
	state_save_new_iconstrs(State2,Iconstrs,State3),
	(get_param(debug,[])->print_or_log('   - Found a solution using cacheing ~n',[]);true).

			
%triangular strategy
% valid for minsums of expressions that are not constant	
compute_sum(Loop_id,_Depth,Loop_vars,Constr,Phase_loops,State,State3):-
	state_get_property(State,phase_type,single),
	\+is_ub_bconstr(Constr),
	triangular_strategy(Constr,Loop_vars,Loop_id,Phase_loops,State,State2,Changes),
	print_phase_computation_changes(Changes),
	state_save_found(State2,found(sum,Constr,Loop_vars,Loop_id,Changes),State3).
	
%Inductive strategy
compute_sum(Loop_id,Depth,Loop_vars,Constr,Phase_loops,State,State4):-
	inductive_sum_strategy(Constr,Depth,Loop_vars,Loop_id,Phase_loops,State,State2,Changes),
	Changes\=[],
	print_phase_computation_changes(Changes),
	% this is an heuristic
	% if we are computing a minsum or we have created some intermediate constraints, we apply the basic product strategy as well
	(
	(Constr\=bound(_,[]+_,_),%not constant
	((member(new_iconstrs(New_iconstrs),Changes),New_iconstrs\=[]); \+is_ub_bconstr(Constr))
		)->%computing lower bounds or there are parts that can still fail
		basic_product_strategy(Constr,Depth,Loop_vars,Loop_id,Phase_loops,State2,State3,Changes2),
		print_phase_computation_changes(Changes2)
	;
		State3=State2
	),
	state_save_found(State3,found(sum,Constr,Loop_vars,Loop_id,Changes),State4).


%Basic Product strategy
compute_sum(Loop_id,Depth,Loop_vars,Constr,Phase_loops,State,State3):-
	\+is_constant_bconstr(Constr),!,
	basic_product_strategy(Constr,Depth,Loop_vars,Loop_id,Phase_loops,State,State2,Changes),
	print_phase_computation_changes(Changes),
	state_save_found(State2,found(sum,Constr,Loop_vars,Loop_id,Changes),State3).

	
compute_sum(_Loop_id,_Depth,_Loop_vars,_Constr,_Phase_loops,State,State):-
	(get_param(debug,[])->print_or_log('   - No strategy succeeded ~n',[]);true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% a constant does not need to be maximized/minimized
compute_max_min(_Loop_id,_Depth,Loop_vars,Constr,_Phase_loops,State,State2):-
	is_constant_bconstr(Constr),!,
	state_save_new_fconstrs(State,Loop_vars,[Constr],State2).
	



compute_max_min(Loop_id,_Depth,Loop_vars,Constr,_Phase_loops,State,State3):-
	state_get_found(State,pattern(maxmin,Constr,Loop_vars,Loop_id),result(Fconstrs,Iconstrs)),
	state_save_new_fconstrs(State,Loop_vars,Fconstrs,State2),
	state_save_new_iconstrs(State2,Iconstrs,State3),	
	(get_param(debug,[])->print_or_log('   - Found a solution using cacheing ~n',[]);true).	




compute_max_min(Loop_id,Depth,Loop_vars,Constr,Phase_loops,State,State3):-	
	max_min_strategy(Constr,Depth,Loop_vars,Loop_id,Phase_loops,State,State2,Changes),
	print_phase_computation_changes(Changes),
	state_save_found(State2,found(maxmin,Constr,Loop_vars,Loop_id),State3).
	


 
%failed    
compute_max_min(Loop_id,_Depth,Loop_vars,Constr,_Phase_loops,State,State2):-
	state_save_found(State,found(maxmin,Constr,Loop_vars,Loop_id),State2),
	(get_param(debug,[])->print_or_log('   - No strategy succeeded ~n',[]);true).


	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    	   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Auxiliary strategies

%! add_general_ranking_functions(Head:term,Call:term,Phase:phase) is det
% add final constraints using the already computed ranking functions

cond_add_n_elem_constraints(State,State2):-
	state_get_property(State,phase_type,single),!,
	state_get_property(State,phase,Phase),
	state_get_property(State,new_cost,costWvars(loop_vars(Head,[Call]),New_cost)),
	
	get_param(n_candidates,[Max]),
	get_ranking_functions_constraints(Max,Head,Call,Phase,Ub_fconstrs),
	cstr_add_fconstrs(New_cost,Ub_fconstrs,New_cost2),
	(get_param(compute_lbs,[])->
	   get_ranking_functions_lower_constraints(Max,Head,Call,Phase,Lb_fconstrs),
	   cstr_add_fconstrs(New_cost2,Lb_fconstrs,New_cost3)
	   ;
	   New_cost3=New_cost2
	 ),
	 state_set_property(State,new_cost,costWvars(loop_vars(Head,[Call]),New_cost3),State2).
	 
cond_add_n_elem_constraints(State,State).
	
%! get_ranking_functions_constraints(Max:int,Head:term,Call:term,Phase:phase,Chain:chain,Fconstrs:list(fconstr))
% generate at most Max upper bound final constraints from the ranking functions
% -the ranking function itself
% -the difference between the ranking function at the beginning and at the end of the phase
get_ranking_functions_constraints(Max,Head,Call,Phase,Fconstrs):-
	phase_get_rfs(Phase,ranking_functions(Head,Rfs)),
	maplist(parse_le_fast,Rfs,Rfs_le),
	ut_split_at_pos(Rfs_le,Max,Rfs_selected,_),
	maplist(get_difference_version(Head,Call),Rfs_selected,Rfs_diff),
	phase_get_pattern(Phase,Phase_pattern),
	maplist(get_loop_itvar,Phase_pattern,Bounded),
	append(Rfs_selected,Rfs_diff,Rfs_total),
	maplist(fconstr_new(Bounded,ub),Rfs_total,Fconstrs).
	
%! get_ranking_functions_lower_constraints(Max:int,Head:term,Call:term,Phase:phase,Chain:chain,Fconstrs:list(fconstr))
% generate at most Max lower bound final constraints from the ranking functions
% -the difference between the initial and the final value of the rf divided by the maximum decrease
% per iteration is a good lb candidate 
get_ranking_functions_lower_constraints(Max,Head,Call,Phase,Fconstrs):-
	phase_get_rfs(Phase,ranking_functions(Head,Rfs)),
	maplist(parse_le_fast,Rfs,Rfs_le),
	phase_get_property(Phase,phase_loop,phase_loop(Head,Call,Cs)),
	conditional_maplist(get_lower_bound_val(Head,Call,Cs),Rfs_le,Dfs),
	phase_get_pattern(Phase,Phase_pattern),
	ut_split_at_pos(Dfs,Max,Dfs_selected,_),
	maplist(get_loop_itvar,Phase_pattern,Bounded),
	maplist(fconstr_new(Bounded,lb),Dfs_selected,Fconstrs).

conditional_maplist(_Pred,[],[]):-!.
conditional_maplist(Pred,[X|Xs],[Y|Ys]):-
	call(Pred,X,Y),!,
	conditional_maplist(Pred,Xs,Ys).
	
conditional_maplist(Pred,[_X|Xs],Ys):-
	conditional_maplist(Pred,Xs,Ys).
	
get_lower_bound_val(Head,Call,Cs,Rf,LB):-
	copy_term((Head,Rf),(Call,Rf1)),
	subtract_le(Rf,Rf1,Rf_diff),
	integrate_le(Rf_diff,Den,Rf_diff_nat),
	write_le(Rf_diff_nat,Rf_diff_nat_print),
	Constraint= (Den* D = Rf_diff_nat_print),
	Cs_1 = [ Constraint | Cs],
	% maximum decrease
	nad_maximize(Cs_1,[D],[Delta]),
	inverse_fr(Delta,Delta_inv),
	multiply_le(Rf_diff,Delta_inv,LB).		
	

	


	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicates to handle the pending_constrs data structure

%state has pending, used, new_cost and cached solved candidates
% and phase_type and phase
state_empty(state(Initial3)):-
	empty_lm(Empty),
	used_empty(Empty_used),
	founds_empty(Founds_empty),
	candidate_results_empty(Empty_can_res),
	insert_lm(Empty,used,Empty_used,Initial),
	insert_lm(Initial,candidate_results,Empty_can_res,Initial2),
	insert_lm(Initial2,founds,Founds_empty,Initial3).

state_set_property(state(Map),Key,Val,state(Map2)):-
	insert_lm(Map,Key,Val,Map2).
state_get_property(state(Map),Key,Val):-
	lookup_lm(Map,Key,Val).	
	
state_set_pending(State,Pending,State2):-
	state_set_property(State,pending,Pending,State2).
	
state_get_one_pending(State,Pending,State3):-
	state_get_property(State,pending,Pending_set),
	pending_extract_one(Pending_set,Pending,Pending_set2),
	state_set_property(State,pending,Pending_set2,State2),
	
	Pending=pending(Type,Loop,_,Head_call,Constr),
	ground_copy(used(Type,Loop,Head_call,Constr),Used_ground),
	state_get_property(State2,used,Used_set),
	used_add(Used_set,Used_ground,Used_set2),
	state_set_property(State2,used,Used_set2,State3).


		
state_save_new_fconstrs(State,Loop_vars,Constrs,State2):-
	state_get_property(State,new_cost,costWvars(Cost_vars,Cost)),	
	(Cost_vars=Loop_vars
	 ; 
	Cost_vars=loop_vars(Head,_),
	Loop_vars=loop_vars(Head,_)
	),
	cstr_add_fconstrs(Cost,Constrs,Cost2),
	state_set_property(State,new_cost,costWvars(Cost_vars,Cost2),State2).	
	
state_save_new_iconstrs(State,Constrs,State2):-
	state_get_property(State,new_cost,costWvars(Cost_vars,Cost)),	
	cstr_add_iconstrs(Cost,Constrs,Cost2),
	state_set_property(State,new_cost,costWvars(Cost_vars,Cost2),State2).	

state_get_used_set(State,Used):-
	state_get_property(State,used,Used).
	
state_get_used_constr(State,Used_elem):-
	state_get_used_set(State,Used_set),
	used_get(Used_set,Used_elem).

state_save_pending_list(State,Type,Depth,Loop_vars,Loop_id,Constrs,State2):-
	state_get_property(State,pending,Pending),
	save_pending_list(Type,Depth,Loop_vars,Loop_id,Constrs,Pending,Pending2),
	state_set_property(State,pending,Pending2,State2).
	
	
state_get_candidate_result(State,Candidate,Candidate_result):-
	state_get_property(State,candidate_results,Candidate_results),
	candidate_results_get(Candidate_results,Candidate,Candidate_result).
	
state_save_candidate_result(State,Candidate_result,State2):-
	state_get_property(State,candidate_results,Candidate_results),
	candidate_results_add(Candidate_results,Candidate_result,Candidate_results2),
	state_set_property(State,candidate_results,Candidate_results2,State2).


state_get_found(State,Found,Found_result):-
	state_get_property(State,founds,Founds),
	founds_get(Founds,Found,Found_result).
	
state_save_found(State,Found,State2):-
	state_get_property(State,founds,Founds),
	founds_add(Founds,Found,Founds2),
	state_set_property(State,founds,Founds2,State2).
	

founds_empty(founds([])).

founds_add(founds(Map),found(sum,bound(Op,Lin_exp,Bounded),Loop_vars,Loop_id,Changes),founds(Map2)):-	
	foldl(change_collect_fconstrs(Loop_vars),Changes,[],Fconstrs),
	foldl(change_collect_iconstrs,Changes,[],Iconstrs),
	from_list_sl(Bounded,Bounded_set),
	substitute_bounded_by_var(Iconstrs,Bounded_set,Var,Iconstrs1),
	substitute_bounded_by_var(Fconstrs,Bounded_set,Var,Fconstrs1),
	semi_normalize_le(Lin_exp,Coeff,Lin_exp_normalized),
	ground_copy((Loop_vars,Lin_exp_normalized),(_,Lin_exp_norm_ground)),	
	insert_lm(Map,(sum,Loop_id,Lin_exp_norm_ground,Op),(Loop_vars,Coeff,Var,Fconstrs1,Iconstrs1),Map2).
	

founds_add(founds(Map),found(maxmin,bound(Op,Lin_exp,[Itvar]),Loop_vars,Loop_id),founds(Map2)):-	
	normalize_max_min(Lin_exp,(Lin_exp_normalized,Coeff,Constant)),
	ground_copy((Loop_vars,Lin_exp_normalized),(_,Lin_exp_normalized_ground)),	
	insert_lm(Map,(maxmin,Loop_id,Lin_exp_normalized_ground,Op),(Coeff,Constant,Itvar),Map2).


founds_get(founds(Map),pattern(sum,bound(Op,Lin_exp,Bounded),Loop_vars,Loop_id),result(Fconstrs1,[New_iconstr|Iconstrs1])):-
	semi_normalize_le(Lin_exp,Coeff2,Lin_exp_normalized2),
	ground_copy((Loop_vars,Lin_exp_normalized2),(_,Lin_exp_norm_ground)),
	lookup_lm(Map,(sum,Loop_id,Lin_exp_norm_ground,Op),Record),
	copy_term(Record,(Loop_vars,Coeff,Aux_itvar,Fconstrs1,Iconstrs1)),
	divide_fr(Coeff2,Coeff,Coeff_final),
	new_itvar(Aux_itvar),
	astrexp_new(add([mult([Aux_itvar,Coeff_final])])-add([]),Astrexp),
	iconstr_new(Astrexp,Op,Bounded,New_iconstr).

found_get(founds(Map),pattern(maxmin,bound(Op,Lin_exp,Bounded),Loop_vars,Loop_id),result([],[Iconstr])):-
	normalize_max_min(Lin_exp,(Lin_exp_normalized,Coeff,Constant)),
	ground_copy((Loop_vars,Lin_exp_normalized),(_,Lin_exp_normalized_ground)),	
	lookup_lm(Map,(maxmin,Loop_id,Lin_exp_normalized_ground,Op),(Coeff2,Constant2,Itvar)),
	
	divide_fr(Coeff,Coeff2,New_coeff),
	multiply_fr(New_coeff,Constant2,Constant3),
	subtract_fr(Constant,Constant3,Final_constant),
	(greater_fr(Final_constant,0)->
		   astrexp_new(add([mult([Itvar,New_coeff]),mult([Final_constant])])-add([]),Astrexp)
		   ;
		   astrexp_new(add([mult([Itvar,New_coeff])])-add([mult([-1,Final_constant])]),Astrexp)
	),
	iconstr_new(Astrexp,Op,Bounded,Iconstr).


normalize_max_min(Lin_exp,([]+0,1,Constant)):-
	Lin_exp=[]+Constant,!.
	
normalize_max_min(Lin_exp,(Lin_exp_normalized,Coeff,Constant)):-
	Lin_exp=Coeffs+Constant,
	Lin_exp_wo_constant=Coeffs+0,
	semi_normalize_le(Lin_exp_wo_constant,Coeff,Lin_exp_normalized).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

candidate_results_empty(candidate_results(Map)):-
	empty_lm(Map).
	
candidate_results_get(candidate_results(Map),candidate(Loop_vars,Linexp,Op),Candidate_result):-
	Loop_vars=loop_vars(Head,_Calls),
	ground_copy((Head,Linexp),(_,Linexp_gr)),
	lookup_lm(Map,(Linexp_gr,Op),Candidate_result).

candidate_results_add(candidate_results(Map),candidate_result(Linexp,Op,Loop_vars,Classification),candidate_results(Map2)):-
	Loop_vars=loop_vars(Head,_Calls),
	ground_copy((Head,Linexp),(_,Linexp_gr)),
	insert_lm(Map,(Linexp_gr,Op),candidate_result(Linexp,Op,Loop_vars,Classification),Map2).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
used_empty(used_set([])).
used_add(used_set(Set),Used,used_set(Set2)):-
	insert_sl(Set,Used,Set2).

used_get(used_set(Set),Used_elem):-
	member(Elem,Set),
	varnumbers(Elem,Used_elem).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%		
pending_empty(Max_depth,pending_set(Max_depth,[])).

%! save_pending_list(Type:flag,Loop:loop_id,Fconstrs:list(fconstr),Pending:pending_constrs,Pending_out:pending_constrs)
% add the final constraints Fconstrs to the pending constrs Pending
% They are added with Depth+1 where Depth is the current Depth
% If Depth is above the limit, the constraints are not added and will be ignored
% Type in {max_min,level,sum}
save_pending_list(Type,Depth,Loop_vars,Loop,Fconstrs,Pending,Pending_out):-
	foldl(save_pending(Type,Loop,Depth,Loop_vars),Fconstrs,Pending,Pending_out).


%!union_pending(Pending1:pending_constrs,Pending2:pending_constrs,Pending3:pending_constrs)
% join Pending1 and Pending2 into Pending3
pending_union(pending_set(Max_depth,Set1),pending_set(Max_depth,Set2),pending_set(Max_depth,Set3)):-
	union_sl(Set1,Set2,Set3).
	

%! save_pending(Type:flag,Loop:loop_id,Depth:int,Fconstr:fconstr,Pending:pending_constrs,Pending_out:pending_constrs)
% add Fconstr to Pending with flag Type, Loop and Depth
save_pending(Type,Loop,Depth,Head_call,Constr,pending_set(Max_depth,Set),pending_set(Max_depth,Set2)):-
	(Depth=< Max_depth->
		insert_sl(Set,pending(Type,Loop,Depth,Head_call,Constr),Set2)
		;
		Set2=Set
	).
	
%! get_one_pending(Pending:pending_constrs,Type:term,Elem:(int,nlinexp,list(itvar)),Pending_out:pending_constrs) is semidet
% get one pending constraint from Pending
% it fails if Pending is empty
pending_get_one(pending_set(Max_depth,Set),Pending,pending_set(Max_depth,Set1)):-
	Set=[Pending|Set1].

% Similar to the previous predicate but specifying the Loop and whether it is maxsum or minsum that
% we want to obtain
pending_extract_one(pending_set(Max_depth,Set),Pending,pending_set(Max_depth,Set1)):-
	select(Pending,Set,Set1).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type_of_loop([_|_],'Chain-Tail'):-!.
type_of_loop(N,'Loop'):-number(N).		

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Cacheing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%cacheing computation of sums, maxs and mins




%! save_sum_found(Head:term,Call:term,Loop:loop_id,Lin_exp:alinexp,Max_min:flag,Bounded:list(itvar),Fconstrs:list(fconstr),Iconstrs:list(iconstr))
% Store the costraints resulting from the computation of "Maxmin"sum(Lin_exp)
% We take only the constraints that contain Bounded and substitute the set Bounded by a variable Var so it
% can be later unified with an itvar
%
% we normalize the linear expression so any multiple of the original constraint 
% can reuse the stored result



change_collect_fconstrs(Loop_vars,new_fconstrs(Loop_vars,Fconstrs),Accum,Accum2):-!,
	append(Fconstrs,Accum,Accum2).
change_collect_fconstrs(_Loop_vars,_,Accum,Accum).

change_collect_iconstrs(new_iconstrs(Iconstrs),Accum,Accum2):-!,
	append(Iconstrs,Accum,Accum2).
change_collect_iconstrs(_,Accum,Accum).

	
substitute_bounded_by_var([],_,_,[]).
substitute_bounded_by_var([bound(Op,Exp,Bounded1)|Constrs],Bounded_set,Var,[bound(Op,Exp,[Var|Bounded2_set])|Constrs2]):-
	from_list_sl(Bounded1,Bounded1_set),
	difference_sl(Bounded1_set,Bounded_set,Bounded2_set),
	length(Bounded1_set,N1),length(Bounded_set,N),length(Bounded2_set,N2),
	N22 is N1-N, N22=N2,!,
	substitute_bounded_by_var(Constrs,Bounded_set,Var,Constrs2).
substitute_bounded_by_var([_|Constrs],Bounded_set,Var,Constrs2):-
	substitute_bounded_by_var(Constrs,Bounded_set,Var,Constrs2).	


	
%FIXME simplify this
%! max_min_found(Head:term,Phase:phase,(Lin_exp_normalized2,Coeff2,Constant2),Max_min:flag,Res:?)
% a max or min has been found for the linear expression Lin_exp_normalized2*Coeff2+Constant2 and is Res
% we can use this information to compute maxs or mins for similar expressions
:-dynamic max_min_found/5.

%! save_max_min_found(Head:term,Call:term,Phase:phase,Lin_exp:alinexp,Max_min:flag,Exp:final_inter_none)
% final_inter_none:= final(list(alinexp)) | inter(astrexp) | none
% Store the value Exp from the maximization/minimization of a linear expression Lin_exp
% we normalize the linear expression to be able to reuse the result in more cases:
% any multiple plus any constant


