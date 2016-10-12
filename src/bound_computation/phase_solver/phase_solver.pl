/** <module> phase_solver

This module computes the cost structure of a phase.
If the phase has linear recursion, the cost structure is  in terms of the variables 
at the beginning and the end of the phase.

If the phase has multiple recursion the cost structure depends only on the input variables.
The predicate for multiple recursion also receives the cost of the rest of the chain so it can also be transformed.
For now, we can only compute upper bounds of multiple recursion.

The algorithm is iterative. We have a data structure (a tuple of Pending sets) that stores constraints that need to be treated.
For each constraint we might need to obtain the sum, the sum in a level or the maximum or minimum of the constraint in the phase.
For this purpose, we apply the different strategies.

The strategies generate new costraints for the phase and can also add elements to the Pending sets.
The procedure uses dynamic progamming to avoid recomputing constraints that have already been computed.

By default we add constraints using the ranking functions directly at the beginning of the computation.
These constraints are useful in most cases and that allows us to simplify the rest of the strategies.

 Additional data structures used in this module are:
  
 Pending_constrs contains the information of the constraints that are pending to be computed
 It has the form
 pending(Head,Maxs_mins,Level_sums,Sums)
 where
  * Head is the head of the cost equations of the phase (the constraints in Maxs_mins are expressed in terms of these variables)
  * Maxs_mins=list_set((Depth,Fconstr))
  * Levels=list_set((Depth,Fconstr))
  * Sums=multimap((loop_id,Loop_vars), (Depth,Fconstr))
 Sums are for a specific loop whereas Max_mins and Levels are general for the whole phase. 
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
				compute_multiple_rec_phase_cost/6,
				compute_phase_cost/6,
				init_phase_solver/0,
				
				used_pending_constraint/3,
				save_used_pending_constraint/3,
				enriched_loop/4,
				current_chain_prefix/1,
		        empty_pending/1,
		        save_pending_list/6,
		        extract_pending/6,
		        union_pending/3]).

:- use_module(phase_common).
:- use_module(phase_inductive_sum_strategy,[
	init_inductive_sum_strategy/0,
	inductive_sum_strategy/8,
	inductive_level_sum_strategy/7
	]).			
:- use_module(phase_basic_product_strategy,[
	basic_product_strategy/6,
	level_product_strategy/6,
	leaf_product_strategy/5
	]).	
:- use_module(phase_triangular_strategy,[triangular_strategy/8]).	
:- use_module(phase_max_min_strategy,[max_min_strategy/7]).	

	

:- use_module('../cost_equation_solver',[get_loop_cost/5]).
:- use_module('../constraints_maximization',[max_min_linear_expression_all/5]).					      
:- use_module('../../db',[
			   phase_loop/5,
			   get_input_output_vars/3,
		       loop_ph/6]).

:- use_module('../../IO/params',[get_param/2]).		
:- use_module('../../IO/output',[
	print_or_log/2,
	print_header/3,
	print_pending_set/2,
	print_loops_costs/3,
	print_selected_pending_constraint/3,
	print_new_phase_constraints/3]).		
:- use_module('../../ranking_functions',[ranking_function/4]).	  		
:-use_module('../../refinement/invariants',[
				  partial_backward_invariant/5,
			      phase_transitive_star_closure/5,
			      forward_invariant/4,		      
			      context_insensitive_backward_invariant/3,
		      	  context_insensitive_forward_invariant/3]).			

	
:- use_module('../../utils/cofloco_utils',[
			tuple/3,
			zip_with_op/3,
			ground_copy/2,
			bagof_no_fail/3]).	
:- use_module('../../utils/cost_structures',[
			cstr_extend_variables_names/3,
			cstr_join_equal_fconstr/2,
			cstr_remove_cycles/2,
			new_itvar/1,
			get_loop_itvar/2,
			get_loop_depth_itvar/2,
			is_ub_bconstr/1,
			astrexp_new/2,
			pstrexp_pair_empty/1,
			pstrexp_pair_add/3,
			cstr_propagate_sums/4,
			fconstr_new/4,
			iconstr_new/4,
			cstr_empty/1,
			cstr_join/3]).			

:- use_module('../../utils/polyhedra_optimizations',[
		nad_is_bottom/1,
		nad_normalize_polyhedron/2 ]).			

:- use_module(stdlib(numeric_abstract_domains),[
			nad_maximize/3,
			nad_list_lub/2,
			nad_glb/3]).
:- use_module(stdlib(linear_expression),[
			integrate_le/3,
			write_le/2,
			multiply_le/3,
			semi_normalize_le/3,
			subtract_le/3,
			negate_le/2]).							
:- use_module(stdlib(fraction),[inverse_fr/2,greater_fr/2,geq_fr/2,divide_fr/3,negate_fr/2,multiply_fr/3,subtract_fr/3]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_increase/3]).
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map)).
:- use_module(stdlib(multimap)).
:-use_module(library(apply_macros)).
:-use_module(library(lists)).

%! phase_cost(Phase:phase,Head:term,Calls:list(term_,Cost:cstr)
% store the cost structure of a phase given a local invariant
% for cacheing purposes
:- dynamic  phase_cost/4.

%! init_phase_solver is det
% clear all the intermediate results
init_phase_solver:-
	retractall(phase_cost(_,_,_,_)).

	
%! compute_phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cstr) is det
% Obtain the cost of a phase given a forward invariant.
% The cacheing case
compute_phase_cost(Head,Calls,Phase,_Chain_prefix,_Chain_rest,Cost):-
	get_param(context_sensitive,[Sensitivity]),Sensitivity=<1,
	phase_cost(Phase,Head,Calls,Cost),!,
	(get_param(debug,[])->
	 	print_header('Found solution for phase  ~p in the cache ~n',[Phase],4)
	 	;true),
	counter_increase(compressed_phases1,1,_).
	

compute_phase_cost(Head,[Call],Phase,Chain_prefix,Chain_rest,Cost_final):-
	get_param(context_sensitive,[Sensitivity]),
	(Sensitivity =< 1 ->
		context_insensitive_backward_invariant(Head,Phase,Backward_invariant),
		context_insensitive_forward_invariant(Head,Phase,Forward_invariant),
	    Forward_hash=0,
	    (get_param(debug,[])->
	 		print_header('Computing cost of phase ~p ~n',[Phase],4)
	 		;true),
	 	init_solving_phase([Phase,no_chain],Phase)	
	;
		forward_invariant(Head,(Chain_prefix,_),Forward_hash,Forward_invariant),
		partial_backward_invariant(Chain_rest,Head,(Forward_hash,Forward_invariant),_,Backward_invariant),
		(get_param(debug,[])->
	 		print_header('Computing cost of phase ~p with suffix ~p and prefix ~p ~n',[Phase,Chain_rest,Chain_prefix],4)
	 		;true),
	 	init_solving_phase(Chain_prefix,Phase)
	),
	nad_glb(Forward_invariant,Backward_invariant,Total_inv),
	save_enriched_loops(Head,Total_inv,Phase,Phase_feasible),
	
    %get the cost of each iterative component of the phase	
	profiling_start_timer(equation_cost),
	maplist(get_equation_loop_cost((Forward_hash,Forward_invariant)),Phase_vars,Phase_feasible,Costs),
	print_loops_costs(Phase_feasible,Phase_vars,Costs),
	profiling_stop_timer_acum(equation_cost,_),
	cstr_empty(Empty_cost),
	add_n_elem_constraints(Head,Call,Phase,Phase_feasible),
	compute_phase_cost_generic(Head,loop_vars(Head,[Call]),Phase_feasible,Phase_vars,Costs,Empty_cost,([],[]),Cost_final),
	assertz(phase_cost(Phase,Head,[Call],Cost_final)).
	
compute_multiple_rec_phase_cost(Head,Phase,_Chain_prefix,Chain_rest,_Cost_prev,Cost):-
	get_param(context_sensitive,[Sensitivity]),Sensitivity=<1,
	phase_cost(Chain_rest,Head,[],Cost),!,
	(get_param(debug,[])->
	 	print_header('Found solution for phase  ~p in the cache ~n',[Phase],4)
	 	;true),
	counter_increase(compressed_phases1,1,_).
		
compute_multiple_rec_phase_cost(Head,Phase,Chain_prefix,Chain_rest,Cost_prev,Cost_final):-
	Chain_rest=[multiple(Phase,Tails)],
	get_param(context_sensitive,[Sensitivity]),
	(Sensitivity =< 1 ->
		context_insensitive_backward_invariant(Head,multiple(Phase,Tails),Backward_invariant),
		context_insensitive_forward_invariant(Head,Phase,Forward_invariant),
		Forward_hash=0,
		(get_param(debug,[])->
			print_header('Computing cost of phase ~p with multiple recursion~n',[Phase],4)
	    	;true),
	    init_solving_phase([Phase,no_chain],Phase)		
	  ;  
	    forward_invariant(Head,(Chain_prefix,_),Forward_hash,Forward_invariant),
	    partial_backward_invariant(Chain_rest,Head,(Forward_hash,Forward_invariant),_,Backward_invariant),
	    (get_param(debug,[])->
			print_header('Computing cost of phase ~p with multiple recursion with suffix ~p and prefix ~p ~n',[Phase,Tails,Chain_prefix],4)
	    	;true),
	    init_solving_phase(Chain_prefix,Phase)
	),
	nad_glb(Forward_invariant,Backward_invariant,Total_inv),
	save_enriched_loops(Head,Total_inv,Phase,Phase_feasible),
	%get the cost of each iterative component of the phase
	profiling_start_timer(equation_cost),
	maplist(get_equation_loop_cost((Forward_hash,Forward_invariant)),Phase_vars,Phase_feasible,Costs),
	print_loops_costs(Phase_feasible,Phase_vars,Costs),
	profiling_stop_timer_acum(equation_cost,_),
	cstr_propagate_sums(0,Cost_prev,Cost_prev_propagated,(Max_min,Level)),
	get_loop_itvar(0,Itvar_last_level),
	Max_min_sum_pair=(Max_min,[bound(ub,[]+1,[Itvar_last_level])|Level]),
	add_depth_constraints(Head,Phase,Phase_feasible),
	compute_phase_cost_generic(Head,loop_vars(Head,[]),Phase_feasible,Phase_vars,Costs,Cost_prev_propagated,Max_min_sum_pair,Cost_final),
	assertz(phase_cost(Chain_rest,Head,[],Cost_final)).
	
compute_phase_cost_generic(Head,Result_vars,Phase,Phase_vars,Costs,Base_cost,Base_max_min_levels,Cost_final):-
	maplist(cstr_propagate_sums,Phase,Costs,Costs_propagated2,Max_min_pairs_Sums_pairs),
	foldl(cstr_join,Costs_propagated2,Base_cost,cost([],[],Iconstrs,Bases,Base)),
	%unpack result of propagation
	maplist(tuple,Max_mins,Sums,Max_min_pairs_Sums_pairs),
	%we add pending sums for the number of iterations of each loop as they will be needed in most occasions anyway
	% this way, we can always assume they are computed
	maplist(get_it_sum_constraint(ub),Phase,It_cons_max), 
	maplist(append,It_cons_max,Sums,Sums1),
	(get_param(compute_lbs,[])->
    	maplist(get_it_sum_constraint(lb),Phase,It_cons_min),
    	maplist(append,It_cons_min,Sums1,Sums2)
    	;
    	 Sums2=Sums1
     ),
	%add_ranking_functions_constraints(Head,Phase),
	%main predicate
	compute_sums_and_max_min_in_phase(Head,Phase,Phase_vars,Max_mins,Sums2,Base_max_min_levels),
	%collect stored results
	collect_phase_results(Result_vars,Final_ub_fconstrs,Final_lb_fconstrs,New_iconstrs),
	reverse(New_iconstrs,New_iconstrs2),
	append(New_iconstrs2,Iconstrs,Iconstrs_final),
	cstr_join_equal_fconstr(cost(Final_ub_fconstrs,Final_lb_fconstrs,Iconstrs_final,Bases,Base),Cost_final).


%! compute_sums_and_max_min_in_phase(Head:term,Call:term,Phase:phase,Maxs:list(fconstrs),Mins:list(fconstrs),Max_sums:list(fconstrs),Min_sums:list(fconstrs))
% store all the pending computations in Pending structure and compute them incrementally
% the results are stored in the database and collected later
compute_sums_and_max_min_in_phase(Head,Phase,Phase_vars,Max_mins,Sums,(Base_max_min,Base_levels)):-
	empty_pending(Empty_pending),
	length(Phase,N),
	%this is completely heuristic
	Max_pending is 2*N+2,
	assertz(max_pending_depth(Max_pending)),
	%we start from depth 0
	assertz(current_pending_depth(0)),
	maplist(transform_max_min2_head(Head),Phase_vars,Phase,Max_mins,Max_mins_head),
	save_pending_list(max_min,Head,0,Base_max_min,Empty_pending,Pending1),
	save_pending_list(level,Head,0,Base_levels,Pending1,Pending2),
	foldl(save_pending_list(max_min,Head),Phase,Max_mins_head,Pending2,Pending3),
	foldl(save_pending_list(sum),Phase_vars,Phase,Sums,Pending3,Pending4),
	retract(current_pending_depth(0)),
	print_pending_set(Head,Pending4),
	compute_all_pending(Phase,Pending4),
	retract(max_pending_depth(Max_pending)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

init_solving_phase(Chain_prefix,Phase):-
	init_inductive_sum_strategy,
	retractall(enriched_loop(_,_,_,_)),
	retractall(current_chain_prefix(_)),
	retractall(current_phase(_)),
	retractall(used_term(_,_,_,_,_,_)),
	retractall(max_min_found(_,_,_,_,_)),
	retractall(sum_found(_,_,_,_,_,_,_,_)),
	retractall(used_pending_constraint(_,_,_)),
	assertz(current_chain_prefix(Chain_prefix)),
	assertz(current_phase(Phase)).

	
get_equation_loop_cost((Forward_hash,Forward_inv),loop_vars(Head,Calls),Eq_id,Cost2):-
	get_loop_cost(Head,Calls,(Forward_hash,Forward_inv),Eq_id,Cost),
	cstr_extend_variables_names(Cost,it(Eq_id),Cost2).
	

get_it_sum_constraint(ub,Loop,[bound(ub,[]+1,[Loop_name])]):-
	get_loop_itvar(Loop,Loop_name).
get_it_sum_constraint(lb,Loop,[bound(lb,[]+1,[Loop_name])]):-
	get_loop_itvar(Loop,Loop_name).
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% auxiliary dynamic predicates

%recording the resulting cost of the phase and recovering

%! new_phase_fconstr(Head_Call:term,Fconstr)
% temporary storage of final constraints for the phase Phase
:-dynamic new_phase_fconstr/2.

%! new_phase_iconstr(Head_Call:term,Iconstr)
% temporary storage of intermediate constraint
:-dynamic new_phase_iconstr/2.


save_new_phase_fconstr(Loop_vars,FConstr):-
	assertz(new_phase_fconstr(Loop_vars,FConstr)).
save_new_phase_iconstr(Loop_vars,IConstr):-
	assertz(new_phase_iconstr(Loop_vars,IConstr)).
	
collect_phase_results(Loop_vars,Ub_fconstrs,Lb_fconstrs,Iconstrs_total):-
	Loop_vars=loop_vars(Head,Calls),
	(Calls=[]->
		bagof_no_fail(Top,Calls2^(new_phase_fconstr(loop_vars(Head,Calls2),Top)),Fconstrs),
		bagof_no_fail(Aux,Calls2^(new_phase_iconstr(loop_vars(Head,Calls2),Aux)),Iconstrs)
		;
		bagof_no_fail(Top,(new_phase_fconstr(Loop_vars,Top)),Fconstrs),
		bagof_no_fail(Aux,(new_phase_iconstr(Loop_vars,Aux)),Iconstrs)
	),
	bagof_no_fail(Top,(new_phase_fconstr(Head,Top)),Fconstrs2),
	append(Fconstrs,Fconstrs2,Fconstrs_total),
	partition(is_ub_bconstr,Fconstrs_total,Ub_fconstrs,Lb_fconstrs),
	
	bagof_no_fail(Aux,(new_phase_iconstr(Head,Aux)),Iconstrs2),
	append(Iconstrs,Iconstrs2,Iconstrs_total),
	retractall(new_phase_fconstr(_,_)),
	retractall(new_phase_iconstr(_,_)).
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%temporary information that we want available during the computation of the phase cost

%! enriched_loop(Loop,Head,Calls,Cs_normalized)
% the loop enriched with the forward invariant
:-dynamic enriched_loop/4.

save_enriched_loops(Head,Total_inv,Phase,Phase_feasible):-
	maplist(save_enriched_loop(Head,Total_inv),Phase,Phase_feasible_aux),
	partition(is_wrapped_no,Phase_feasible_aux,Excluded,Phase_feasible),
	((get_param(debug,[]), Excluded\=[])->
			maplist(zip_with_op(no),Excluded_print,Excluded),
		   	print_or_log(' * The following loops are unfeasible in this instance of the phase ~p : ~p ~n',[Phase,Excluded_print])	   	
		   	;true).

is_wrapped_no(no(_)).
	
save_enriched_loop(Head,Inv,Loop,Loop_feasible):-
	loop_ph(Head,(Loop,_),Calls,Cs,_,_),
	foldl(get_call_inv,Calls,(Head,Inv,Inv),(Head,_,Total_inv)),
	append(Total_inv,Cs,Total_cs),
	nad_normalize_polyhedron(Total_cs,Cs_normalized),
	(nad_is_bottom(Cs_normalized)->
		Loop_feasible=no(Loop)
	;
		assertz(enriched_loop(Loop,Head,Calls,Cs_normalized)),
		Loop_feasible=Loop
	).

get_call_inv(Call,(Head,Inv_0,Inv),(Head,Inv_0,Total_inv)):-
	copy_term((Head,Inv_0),(Call,Inv2)),
	nad_glb(Inv,Inv2,Total_inv).
%! max_pending_depth(N:int)
% maximum number or 'recursive' definitions of cost 
% it depends on the number of loops in the phase and could be adjusted
:-dynamic max_pending_depth/1.

%! current_pending_depth(N:int)
% how many recursive calls we have so far for a given expression
:-dynamic current_pending_depth/1.

%! current_chain_prefix(Chain_prefix:chain_prefix)
% the chain to which the phase being computed belongs
% used to 
:- dynamic  current_chain_prefix/1.

%! current_phase(Phase:list(loop_id))
% the phase whose cost we are currently computing
:- dynamic  current_phase/1.

%! used_pending_constraint(Loop:loop_id,Loop_vars:loop_vars,Constr:fconstr)
:-dynamic used_pending_constraint/3.
save_used_pending_constraint(Loop,Loop_vars,Constr):-
	used_pending_constraint(Loop,Loop_vars,Constr2),
	Constr2==Constr,!.
save_used_pending_constraint(Loop,Loop_vars,Constr):-
	assertz(used_pending_constraint(Loop,Loop_vars,Constr)).
	

transform_max_min2_head(Head,loop_vars(Head,Calls),Loop,Maxs_mins,Maxs_mins_head):-
	get_input_output_vars(Head,Vars_head,_),
	enriched_loop(Loop,Head,Calls,Cs),
	foldl(transform_max_min2_head_1(Vars_head,Cs),Maxs_mins,[],Maxs_mins_head).
	
transform_max_min2_head_1(Vars_head,Cs,bound(Op,Lin_exp,Bounded),Fconstrs,[bound(Op,Lin_exp_head,Bounded)|Fconstrs]):-
	get_constr_op(Max_min,Op),
	max_min_linear_expression_all(Lin_exp, Vars_head, Cs,Max_min, Maxs_mins_head),
	member(Lin_exp_head,Maxs_mins_head),!.
transform_max_min2_head_1(_Vars_head,_Cs,_,Fconstrs,Fconstrs).



	
%! compute_all_pending(Phase:phase,Pending:pending_constrs)
% the main loop of the computation:
% compute one pending element at a time unil there are no more pending elements
compute_all_pending(Phase,Pending):-
	compute_pending(Phase,Pending,Pending_out),
	print_pending_set(_Head,Pending_out),
	compute_all_pending(Phase,Pending_out).

compute_all_pending(_,_).

%! compute_pending(Head:term,Call:term,Phase:phase,Pending:pending_constrs,Pending_out:pending_constrs)
% extract one pending constraint from Pending and compute it
% each pending element has a Depth associated to avoid infinite computations, each new pending element created will have
% an increased depth and no pending elements will be added beyond the maximum depth
%
% The result of computing a pending element is a set of final constraints (New_fconstrs) and intermediate constraints (New_iconstrs)
% that are stored in the database
compute_pending(Phase,Pending,Pending_out):-
	get_one_pending(Pending,Type,Loop_vars,(Depth,Constr),Pending1),
	%(get_param(debug,[])->print_pending_info(Head,Call,Type,Lin_exp,Pending1);true),
	assertz(current_pending_depth(Depth)),
	print_selected_pending_constraint(Loop_vars,Type,Constr),
	compute_pending_element(Type,Loop_vars,Phase,Constr,New_fconstrs,New_iconstrs,Pending1,Pending_out),	
	retract(current_pending_depth(Depth)),
	print_new_phase_constraints(Loop_vars,New_fconstrs,New_iconstrs),
	maplist(save_new_phase_fconstr(Loop_vars),New_fconstrs),
	maplist(save_new_phase_iconstr(Loop_vars),New_iconstrs).

%case distinction according to what we have to compute

compute_pending_element(sum(Loop),Loop_vars,Phase,Constr,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	save_used_pending_constraint(Loop,Loop_vars,Constr),
	compute_sum(Constr,Loop_vars,Loop,Phase,New_fconstrs,New_iconstrs,Pending,Pending_out).

compute_pending_element(max_min,Head,Phase,Constr,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	compute_max_min(Constr,Head,Phase,New_fconstrs,New_iconstrs,Pending,Pending_out).	

compute_pending_element(level,Head,Phase,Constr,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	compute_level_sum(Constr,Head,Phase,New_fconstrs,New_iconstrs,Pending,Pending_out).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%trivial case where we have 0
compute_sum(Constr,_Loop_vars,_Loop,_Phase,[Constr],[],Pending,Pending):-
	Constr=bound(_,[]+0,_),!.

% Stored solution
compute_sum(Constr,Loop_vars,Loop,Phase,Fconstrs,Iconstrs,Pending,Pending):-
	sum_cacheing_strategy(Constr,Loop_vars,Loop,Phase,Fconstrs,Iconstrs),
	(get_param(debug,[])->print_or_log('   - Found a solution using cacheing ~n',[]);true).

			
%triangular strategy
% valid for minsums of expressions that are not constant	
compute_sum(Constr,Loop_vars,Loop,Phase,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	Constr=bound(lb,_,_),
	triangular_strategy(Constr,Loop_vars,Loop,Phase,New_fconstrs,New_iconstrs,Pending,Pending_out),
	save_sum_found(Constr,Loop_vars,Loop,New_fconstrs,New_iconstrs).	
	

%Inductive strategy
compute_sum(Constr,Loop_vars,Loop,Phase,New_fconstrs,New_iconstrs2,Pending,Pending_out):-
	inductive_sum_strategy(Constr,Loop_vars,Loop,Phase,New_fconstrs,New_iconstrs,Pending,Pending_aux),
	% this is an heuristic
	% if we are computing a minsum or we have created some intermediate constraints, we apply the basic product strategy as well
	(
	(Constr\=bound(_,[]+_,_),%not constant
	(New_iconstrs\=[]; Constr=bound(lb,_,_)))->%computing lower bounds or there are parts that can still fail
	basic_product_strategy(Constr,Loop_vars,Loop,Iconstr_extra,Pending_aux,Pending_out),
	New_iconstrs2=[Iconstr_extra|New_iconstrs]
	;
	Pending_aux=Pending_out,
	New_iconstrs2=New_iconstrs
	),
	save_sum_found(Constr,Loop_vars,Loop,New_fconstrs,New_iconstrs2).

%Level sum strategy
compute_sum(Constr,Loop_vars,Loop,_Phase,[],[Iconstr1,Iconstr2],Pending,Pending_out):-
	%multiple calls
	Loop_vars=loop_vars(_Head,[_,_|_]),
	level_product_strategy(Constr,Loop_vars,Loop,Iconstr1,Pending,Pending_aux),
	basic_product_strategy(Constr,Loop_vars,Loop,Iconstr2,Pending_aux,Pending_out),
	save_sum_found(Constr,Loop_vars,Loop,[],[Iconstr1]),
	save_sum_found(Constr,Loop_vars,Loop,[],[Iconstr2]).

%Basic Product strategy
compute_sum(Constr,Loop_vars,Loop,_Phase,[],[Iconstr],Pending,Pending_out):-
	Constr\=bound(_,[]+1,_),!,
	basic_product_strategy(Constr,Loop_vars,Loop,Iconstr,Pending,Pending_out),
	save_sum_found(Constr,Loop_vars,Loop,[],[Iconstr]).
	
compute_sum(_Constr,_Loop_vars,_Loop,_Phase,[],[],Pending,Pending):-
	(get_param(debug,[])->print_or_log('   - No strategy succeeded ~n',[]);true).

only_tail_constr(loop_vars(Head,_),Fconstr):-
	copy_term((Head,Fconstr),(Head2,Fconstr2)),
	numbervars(Head2,0,_),
	maplist(term_variables,Fconstr2,Vars),
	\+member([],Vars).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


compute_level_sum(Constr,Head,Phase,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	inductive_level_sum_strategy(Constr,Head,Phase,New_fconstrs,New_iconstrs,Pending,Pending_out).

compute_level_sum(Constr,Head,_Phase,[],[Iconstr],Pending,Pending_out):-
	leaf_product_strategy(Constr,Head,Iconstr,Pending,Pending_out).
compute_level_sum(_,_,_,[],[],Pending,Pending):-
	(get_param(debug,[])->print_or_log('   - No strategy succeeded ~n',[]);true).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% a constant does not need to be maximized/minimized
compute_max_min(Constr,_,_Phase,[Constr],[],Pending,Pending):-
	Constr=bound(_,[]+_C,_),!.

compute_max_min(Constr,Head,Phase,New_fconstrs,New_iconstrs,Pending,Pending):-
	max_min_cacheing_strategy(Constr,Head,Phase,New_fconstrs,New_iconstrs),
	(get_param(debug,[])->print_or_log('   - Found a solution using cacheing ~n',[]);true).	


%use transitive invariant
compute_max_min(Constr,Head,Phase,New_fconstrs,[],Pending,Pending):-
	transitive_invariant_strategy(Constr,Head,New_fconstrs),
	(get_param(debug,[])->print_or_log('   - Found a solution using transitive invariants ~n',[]);true),	
	save_max_min_found(Constr,Head,Phase).

%use  increments and resets procedure	
compute_max_min(Constr,Head,Phase,Fconstrs,Iconstrs,Pending,Pending_out):-
	max_min_strategy(Constr,Head,Phase,Fconstrs,Iconstrs,Pending,Pending_out),
    save_max_min_found(Constr,Head,Phase).
 
%failed    
compute_max_min(Constr,Head,Phase,[],[],Pending,Pending):-
	save_max_min_found(Constr,Head,Phase),
	(get_param(debug,[])->print_or_log('   - No strategy succeeded ~n',[]);true).


	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    	   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Auxiliary strategies


add_depth_constraints(Head,Phase,Phase_feasible):-
	get_param(n_candidates,[Max]),
	current_chain_prefix(Chain_prefix),
	bagof_no_fail(Rf,
		ranking_function(Head,Chain_prefix,Phase,Rf)
	  ,Rfs),
	ut_split_at_pos(Rfs,Max,Rfs_selected,_),
	maplist(get_loop_depth_itvar,Phase_feasible,Bounded),
	maplist(fconstr_new(Bounded,ub),Rfs_selected,Fconstrs),
	maplist(save_new_phase_fconstr(Head),Fconstrs).

%! add_general_ranking_functions(Head:term,Call:term,Phase:phase) is det
% add final constraints using the already computed ranking functions
add_n_elem_constraints(Head,Call,Phase,Phase_feasible):-
	get_param(n_candidates,[Max]),
	current_chain_prefix(Chain_prefix),
	get_ranking_functions_constraints(Max,Head,Call,Phase,Phase_feasible,Chain_prefix,Ub_fconstrs),
	maplist(save_new_phase_fconstr(loop_vars(Head,[Call])),Ub_fconstrs),
	(get_param(compute_lbs,[])->
	   get_ranking_functions_lower_constraints(Max,Head,Call,Phase,Phase_feasible,Chain_prefix,Lb_fconstrs),
	   maplist(save_new_phase_fconstr(loop_vars(Head,[Call])),Lb_fconstrs)
	   ;
	   true
	 ).
%! get_ranking_functions_constraints(Max:int,Head:term,Call:term,Phase:phase,Chain:chain,Fconstrs:list(fconstr))
% generate at most Max upper bound final constraints from the ranking functions
% -the ranking function itself
% -the difference between the ranking function at the beginning and at the end of the phase
get_ranking_functions_constraints(Max,Head,Call,Phase,Phase_feasible,Chain,Fconstrs):-
	bagof_no_fail(Rf,
		ranking_function(Head,Chain,Phase,Rf)
	  ,Rfs),
	ut_split_at_pos(Rfs,Max,Rfs_selected,_),
	maplist(get_difference_version(Head,Call),Rfs_selected,Rfs_diff),
	maplist(get_loop_itvar,Phase_feasible,Bounded),
	append(Rfs_selected,Rfs_diff,Rfs_total),
	maplist(fconstr_new(Bounded,ub),Rfs_total,Fconstrs).
	
%! get_ranking_functions_lower_constraints(Max:int,Head:term,Call:term,Phase:phase,Chain:chain,Fconstrs:list(fconstr))
% generate at most Max lower bound final constraints from the ranking functions
% -the difference between the initial and the final value of the rf divided by the maximum decrease
% per iteration is a good lb candidate 
get_ranking_functions_lower_constraints(Max,Head,Call,Phase,Phase_feasible,Chain,Fconstrs):-
	bagof_no_fail(Df,
		get_lower_bound_val(Head,Call,Chain,Phase,Df)
	,Dfs),
	ut_split_at_pos(Dfs,Max,Dfs_selected,_),
	maplist(get_loop_itvar,Phase_feasible,Bounded),
	maplist(fconstr_new(Bounded,lb),Dfs_selected,Fconstrs).
	   
get_lower_bound_val(Head,Call,Chain,Phase,LB):-
	ranking_function(Head,Chain,Phase,Rf),
	copy_term((Head,Rf),(Call,Rf1)),
	subtract_le(Rf,Rf1,Rf_diff),
	integrate_le(Rf_diff,Den,Rf_diff_nat),
	write_le(Rf_diff_nat,Rf_diff_nat_print),
	phase_loop(Phase,_,Head,Call,Phi),
	Constraint= (Den* D = Rf_diff_nat_print),
	Cs_1 = [ Constraint | Phi],
	% maximum decrease
	nad_maximize(Cs_1,[D],[Delta]),
	inverse_fr(Delta,Delta_inv),
	multiply_le(Rf_diff,Delta_inv,LB).		
	

	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Transitive invariants
transitive_invariant_strategy(bound(Op,Lin_exp,Bounded),Head,New_fconstrs):-
	get_constr_op(Max_min,Op),
	current_phase(Phase),
	phase_transitive_star_closure(Phase,_,Head_total,Head,Cs_star_trans),
	phase_loop(Phase,_,Head,_Call,Cs),
	ut_flat_list([Cs_star_trans,Cs],Context),
	get_input_output_vars(Head_total,Vars_of_Interest,_),
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,Max_min, Maxs_out),
	Head_total=Head,
	maplist(fconstr_new(Bounded,Op),Maxs_out,New_fconstrs),
	New_fconstrs\=[],!.
	
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Cacheing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%cacheing computation of sums, maxs and mins

%FIXME simplify this
%! sum_found(Loop:loop_id,Lin_exp_norm_ground:alinexp_ground,Max_min:flag,Loop_vars:loop_vars,Coeff,Aux_itvar:Var,Fconstrs:list(fconstr),IConstrs:list(iconstr))
%  a sum has been found for the linear expression Lin_exp_norm_ground*Coeff and it corresponds to the constraints Fconstrs and IConstrs
% one can use this sum by simply unifying Aux_itvar with the itvar that we want to bound
:-dynamic sum_found/8.


%! save_sum_found(Head:term,Call:term,Loop:loop_id,Lin_exp:alinexp,Max_min:flag,Bounded:list(itvar),Fconstrs:list(fconstr),Iconstrs:list(iconstr))
% Store the costraints resulting from the computation of "Maxmin"sum(Lin_exp)
% We take only the constraints that contain Bounded and substitute the set Bounded by a variable Var so it
% can be later unified with an itvar
%
% we normalize the linear expression so any multiple of the original constraint 
% can reuse the stored result
save_sum_found(bound(Op,Lin_exp,Bounded),Loop_vars,Loop,Fconstrs,Iconstrs):-	
	from_list_sl(Bounded,Bounded_set),
	substitute_bounded_by_var(Iconstrs,Bounded_set,Var,Iconstrs1),
	substitute_bounded_by_var(Fconstrs,Bounded_set,Var,Fconstrs1),
	semi_normalize_le(Lin_exp,Coeff,Lin_exp_normalized),
	ground_copy((Loop_vars,Lin_exp_normalized),(_,Lin_exp_norm_ground)),
	assertz(sum_found(Loop,Lin_exp_norm_ground,Op,Loop_vars,Coeff,Var,Fconstrs1,Iconstrs1)).
	
substitute_bounded_by_var([],_,_,[]).
substitute_bounded_by_var([bound(Op,Exp,Bounded1)|Constrs],Bounded_set,Var,[bound(Op,Exp,[Var|Bounded2_set])|Constrs2]):-
	from_list_sl(Bounded1,Bounded1_set),
	difference_sl(Bounded1_set,Bounded_set,Bounded2_set),
	length(Bounded1_set,N1),length(Bounded_set,N),length(Bounded2_set,N2),
	N22 is N1-N, N22=N2,!,
	substitute_bounded_by_var(Constrs,Bounded_set,Var,Constrs2).
substitute_bounded_by_var([_|Constrs],Bounded_set,Var,Constrs2):-
	substitute_bounded_by_var(Constrs,Bounded_set,Var,Constrs2).	

sum_cacheing_strategy(bound(Op,Lin_exp,Bounded),Loop_vars,Loop,_Phase,Fconstrs1,[New_iconstr|Iconstrs1]):-
	semi_normalize_le(Lin_exp,Coeff2,Lin_exp_normalized2),
	ground_copy((Loop_vars,Lin_exp_normalized2),(_,Lin_exp_norm_ground)),
	sum_found(Loop,Lin_exp_norm_ground,Op,Loop_vars,Coeff,Aux_itvar,Fconstrs1,Iconstrs1),!,
	divide_fr(Coeff2,Coeff,Coeff_final),
	new_itvar(Aux_itvar),
	astrexp_new(add([mult([Aux_itvar,Coeff_final])])-add([]),Astrexp),
	iconstr_new(Astrexp,Op,Bounded,New_iconstr).
	
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

save_max_min_found(bound(Op,Lin_exp,[Itvar]),Head,Phase):-
	normalize_max_min(Lin_exp,(Lin_exp_normalized,Coeff,Constant)),
	assertz(max_min_found(Head,Phase,(Lin_exp_normalized,Coeff,Constant),Op,Itvar)).

normalize_max_min(Lin_exp,([]+0,1,Constant)):-
	Lin_exp=[]+Constant,!.
	
normalize_max_min(Lin_exp,(Lin_exp_normalized,Coeff,Constant)):-
	Lin_exp=Coeffs+Constant,
	Lin_exp_wo_constant=Coeffs+0,
	semi_normalize_le(Lin_exp_wo_constant,Coeff,Lin_exp_normalized).

max_min_cacheing_strategy(bound(Op,Lin_exp,Bounded),Head,Phase,[],[Iconstr]):-	
	max_min_found(Head,Phase,(Lin_exp_normalized2,Coeff2,Constant2),Op,Itvar),
	normalize_max_min(Lin_exp,(Lin_exp_normalized,Coeff,Constant)),
	% there is a linear expression that has been computed and is a multiple of the one we are computing
	Lin_exp_normalized2==Lin_exp_normalized,!,
	
	divide_fr(Coeff,Coeff2,New_coeff),
	multiply_fr(New_coeff,Constant2,Constant3),
	subtract_fr(Constant,Constant3,Final_constant),
	(greater_fr(Final_constant,0)->
		   astrexp_new(add([mult([Itvar,New_coeff]),mult([Final_constant])])-add([]),Astrexp)
		   ;
		   astrexp_new(add([mult([Itvar,New_coeff])])-add([mult([-1,Final_constant])]),Astrexp)
	),
	iconstr_new(Astrexp,Op,Bounded,Iconstr).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicates to handle the pending_constrs data structure

empty_pending(pending(_,[],[],[])).

%! save_pending_list(Type:flag,Loop:loop_id,Fconstrs:list(fconstr),Pending:pending_constrs,Pending_out:pending_constrs)
% add the final constraints Fconstrs to the pending constrs Pending
% They are added with Depth+1 where Depth is the current Depth
% If Depth is above the limit, the constraints are not added and will be ignored
% Type in {max_min,level,sum}
save_pending_list(Type,Loop_vars,Loop,Fconstrs,Pending,Pending_out):-
	current_pending_depth(Depth),
	max_pending_depth(Max_depth),Depth<Max_depth,!,
	Depth_new is Depth+1,
	foldl(save_pending(Type,Loop,Depth_new,Loop_vars),Fconstrs,Pending,Pending_out).
save_pending_list(_Type,_,_Loop,_Fconstrs,Pending,Pending).

%!union_pending(Pending1:pending_constrs,Pending2:pending_constrs,Pending3:pending_constrs)
% join Pending1 and Pending2 into Pending3
union_pending(pending(Head,Max_min1,Level1,Sums1),pending(Head,Max_min2,Level2,Sums2),pending(Head,Max_min3,Level3,Sums3)):-
	union_sl(Max_min1,Max_min2,Max_min3),
	union_sl(Level1,Level2,Level3),
	join_pending_sums(Sums1,Sums2,Sums3).
	

join_pending_sums(Sum,[],Sum):-!.
join_pending_sums([],Sum,Sum):-!.
join_pending_sums([(Loop,(Head_call,Set1))|Sums1],[(Loop,(Head_call,Set2))|Sums2],[(Loop,(Head_call,Set_union))|Sums_union]):-!,
	union_sl(Set1,Set2,Set_union),
	join_pending_sums(Sums1,Sums2,Sums_union).
	
join_pending_sums([(Loop1,Elem1)|Sums1],[(Loop2,Elem2)|Sums2],[(Loop1,Elem1)|Sums_union]):-
	Loop1<Loop2,!,
	join_pending_sums(Sums1,[(Loop2,Elem2)|Sums2],Sums_union).
join_pending_sums([(Loop1,Elem1)|Sums1],[(Loop2,Elem2)|Sums2],[(Loop2,Elem2)|Sums_union]):-
	Loop1>Loop2,
	join_pending_sums([(Loop1,Elem1)|Sums1],Sums2,Sums_union).	

%! save_pending(Type:flag,Loop:loop_id,Depth:int,Fconstr:fconstr,Pending:pending_constrs,Pending_out:pending_constrs)
% add Fconstr to Pending with flag Type, Loop and Depth
save_pending(max_min,_,Depth,Head_call,Constr,Pending,Pending_out):-
	Pending=pending(Head_call,Maxs_mins,Levels,Sums),
	insert_sl(Maxs_mins,(Depth,Constr),Maxs_mins1),
	Pending_out=pending(Head_call,Maxs_mins1,Levels,Sums).
save_pending(level,_,Depth,Head_call,Constr,Pending,Pending_out):-
	Pending=pending(Head_call,Maxs_mins,Levels,Sums),
	insert_sl(Levels,(Depth,Constr),Levels1),
	Pending_out=pending(Head_call,Maxs_mins,Levels1,Sums).
	
save_pending(sum,Loop,Depth,Head_call,Constr,Pending,Pending_out):-
	Pending=pending(Head,Maxs_mins,Levels,Sums),
	(lookup_lm(Sums,Loop,(Head_call,Sum_set))->
		true
		;
		empty_sl(Sum_set)
	),	
	insert_sl(Sum_set,(Depth,Constr),Sum_set1),
	insert_lm(Sums,Loop,(Head_call,Sum_set1),Sums1),
	Pending_out=pending(Head,Maxs_mins,Levels,Sums1).	


%! get_one_pending(Pending:pending_constrs,Type:term,Elem:(int,nlinexp,list(itvar)),Pending_out:pending_constrs) is semidet
% get one pending constraint from Pending
% it fails if Pending is empty
get_one_pending(pending(Head,[Element|Maxs_mins],Levels,Sums),max_min,Head,Element,pending(Head,Maxs_mins,Levels,Sums)):-!.
get_one_pending(pending(Head,[],[Element|Levels],Sums),level,Head,Element,pending(Head,[],Levels,Sums)):-!.
get_one_pending(pending(Head,[],[],[(Loop,(Head_call,Multimap))|Sums]),sum(Loop),Head_call,Element,pending(Head,[],[],Sums_out)):-
	get_one_pending_1(Multimap,Element,Multimap1),
	(Multimap1=[]->
		Sums_out=Sums
	;
		Sums_out=[(Loop,(Head_call,Multimap1))|Sums]
	).
get_one_pending_1([Element|Multimap],Element,Multimap).

% Similar to the previous predicate but specifying the Loop and whether it is maxsum or minsum that
% we want to obtain
extract_pending(Loop,sum,pending(Head,Maxs_mins,Levels,Sums),Head_call,Element,pending(Head,Maxs_mins,Levels,Sums1)):-
	lookup_lm(Sums,Loop,(Head_call,Elements)),
	select(Element,Elements,Elements1),
	(Elements1=[]->
		delete_lm(Sums,Loop,Sums1)
		;
		insert_lm(Sums,Loop,(Head_call,Elements1),Sums1)
	).
	
