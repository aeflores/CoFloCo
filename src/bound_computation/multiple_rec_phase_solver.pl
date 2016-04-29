/** <module> multiple_rec_phase_solver

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

:- module(multiple_rec_phase_solver,[compute_multiple_rec_phase_cost/5,init_multiple_rec_phase_solver/0]).

:- use_module(phase_solver,[compute_phase_cost/5,
				init_phase_solver/0,
				save_enriched_loop/3,
				enriched_loop/4,
				current_chain_prefix/1,
				max_pending_depth/1,
				current_pending_depth/1,
				get_it_sum_constraint/3,
				get_equation_loop_cost/4,
				save_new_phase_fconstr/2,
				save_new_phase_iconstr/2,
				collect_phase_results/4,
				used_term/5,
				save_used_term/4,
				save_sum_found/7,
				sum_found/8,
				save_max_min_found/5,
		        max_min_found/5,
		        empty_pending/1,
		        save_pending_list/6,
		        extract_pending/6,
		        get_one_pending/5,
		        union_pending/3,
		        basic_product/9,
		        normalize_max_min/2,
		        print_lin_exp_in_phase/3,
				transform_max_min2_head/6]).					
:- use_module(cost_equation_solver,[get_loop_cost/5]).
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
			      forward_invariant/4]).			
	
:- use_module('../utils/cofloco_utils',[
			tuple/3,
			ground_copy/2,
			repeat_n_times/3,
			bagof_no_fail/3]).	
:- use_module('../utils/cost_structures',[
			cstr_extend_variables_names/3,
			cstr_remove_cycles/2,
			cstr_join_equal_fconstr/2,
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
:-use_module('../utils/template_inference',[
			difference_constraint_farkas_multiple_ub/5,
			max_min_linear_expression_list_all/6,
			farkas_leave_ub_candidate/5
	]).	
:- use_module('../utils/polyhedra_optimizations',[
		    nad_normalize_polyhedron/2 
	]).							
:- use_module(stdlib(numeric_abstract_domains),[
			nad_maximize/3,
			nad_minimize/3,
			nad_entails/3,
			nad_project/3,
			nad_glb/3,
			nad_consistent_constraints/1]).
:- use_module(stdlib(linear_expression),[
			integrate_le/3,
			write_le/2,
			multiply_le/3,
			semi_normalize_le/3,
			sum_le/3,
			subtract_le/3,
			negate_le/2]).							
:- use_module(stdlib(fraction),[inverse_fr/2,greater_fr/2,geq_fr/2,divide_fr/3,negate_fr/2,multiply_fr/3,subtract_fr/3]).
:- use_module(stdlib(fraction_list),[max_frl/2]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_increase/3]).
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map)).
:- use_module(stdlib(multimap)).


:-use_module(library(apply_macros)).
:-use_module(library(lists)).


%! init_phase_solver is det
% clear all the intermediate results
init_multiple_rec_phase_solver:-
	retractall(phase_cost(_,_,_,_,_,_)).


% Obtain the cost of a phase given a forward invariant.
compute_multiple_rec_phase_cost(Head,Phase,Chain_prefix,(Cost_prev,Cs_prev_head,_Back_invariant),Cost_final):-
	retractall(enriched_loop(_,_,_,_)),
	retractall(current_chain_prefix(_)),
	retractall(used_term(_,_,_,_,_,_)),
	retractall(max_min_found(_,_,_,_,_)),
	retractall(sum_found(_,_,_,_,_,_,_,_)),
	assert(current_chain_prefix(Chain_prefix)),

	forward_invariant(Head,(Chain_prefix,_),Forward_hash,Forward_inv),
	maplist(save_enriched_loop(Head,Forward_inv),Phase),
	
	profiling_start_timer(equation_cost),
	maplist(get_equation_loop_cost((Forward_hash,Forward_inv)),Phase_vars,Phase,Costs),
	profiling_stop_timer_acum(equation_cost,_),
	Extended_phase=[0|Phase],
	Extended_phase_vars=[loop_vars(Head,[])|Phase_vars],
	Extended_costs=[Cost_prev|Costs],
	
	append(Forward_inv,Cs_prev_head,Cs_prev_head_total),
	nad_normalize_polyhedron(Cs_prev_head_total,Cs_prev_head_total_norm),
	assert(enriched_loop(0,Head,[],Cs_prev_head_total_norm)),
	

	maplist(cstr_join_equal_fconstr,Extended_costs,Costs_simple),
	maplist(cstr_propagate_sums,Extended_phase,Costs_simple,Costs_propagated2,Max_min_pairs_Sums_pairs),
	cstr_empty(Empty_cost),
	foldl(cstr_join,Costs_propagated2,Empty_cost,cost([],[],Iconstrs,Bases,Base)),
	%unpack result of propagation
	maplist(tuple,Max_min_pairs,Sums_pairs,Max_min_pairs_Sums_pairs),
	maplist(tuple,Maxs,Mins,Max_min_pairs),
	maplist(tuple,Max_sums,Min_sums,Sums_pairs),
	%we add pending sums for the number of iterations of each loop as they will be needed in most occasions anyway
	% this way, we can always assume they are computed
	maplist(get_it_sum_constraint(ub),Extended_phase,It_cons_max), 
    maplist(get_it_sum_constraint(lb),Extended_phase,It_cons_min),    
	maplist(append,It_cons_max,Max_sums,Max_sums1),
	maplist(append,It_cons_min,Min_sums,Min_sums1),
	
	add_ranking_functions_constraints(Head,Phase),
	%main predicate
	compute_sums_and_max_min_in_phase(Extended_phase,Extended_phase_vars,Maxs,Mins,Max_sums1,Min_sums1),
	%collect stored results
	collect_phase_results(loop_vars(Head,[]),Final_ub_fconstrs,Final_lb_fconstrs,New_iconstrs),
	append(New_iconstrs,Iconstrs,Iconstrs_final),
	cstr_join_equal_fconstr(cost(Final_ub_fconstrs,Final_lb_fconstrs,Iconstrs_final,Bases,Base),Cost_final),
	(get_param(debug,[])->
		print_phase_cost(Phase,Head,none,Cost_final)
		;
		true).

add_ranking_functions_constraints(Head,Phase):-
	rf_limit(Max),
	current_chain_prefix(Chain_prefix),
	bagof_no_fail(Rf,
		ranking_function(Head,Chain_prefix,Phase,Rf)
	  ,Rfs),
	ut_split_at_pos(Rfs,Max,Rfs_selected,_),
	maplist(get_loop_depth_itvar,Phase,Bounded),
	maplist(fconstr_new(Bounded,ub),Rfs_selected,Fconstrs),
	maplist(save_new_phase_fconstr(loop_vars(Head,[])),Fconstrs).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%! compute_sums_and_max_min_in_phase(Head:term,Call:term,Phase:phase,Maxs:list(fconstrs),Mins:list(fconstrs),Max_sums:list(fconstrs),Min_sums:list(fconstrs))
% store all the pending computations in Pending structure and compute them incrementally
% the results are stored in the database and collected later


compute_sums_and_max_min_in_phase(Ephase,Ephase_vars,Maxs,Mins,Max_sums,Min_sums):-
	empty_pending(Empty_pending),
	Ephase=[0|Phase],
	length(Phase,N),
	Max_pending is 2*N,
	assert(max_pending_depth(Max_pending)),
	%we start from depth 0
	assert(current_pending_depth(0)),
	
	maplist(transform_max_min2_head(Head,max),Ephase_vars,Ephase,Maxs,Maxs_head),
	maplist(transform_max_min2_head(Head,min),Ephase_vars,Ephase,Mins,Mins_head),
	

	foldl(save_pending_list(max,loop_vars(Head,[])),Ephase,Maxs_head,Empty_pending,Pending1),
	foldl(save_pending_list(maxsum),Ephase_vars,Ephase,Max_sums,Pending1,Pending2),
	
	get_loop_itvar(0,Loop_name),
	save_new_phase_fconstr(Head,bound(ub,[]+1,[Loop_name])),
	(get_param(compute_lbs,[])->
		foldl(save_pending_list(min,loop_vars(Head,[])),Ephase,Mins_head,Pending2,Pending3),
		foldl(save_pending_list(minsum),Ephase_vars,Ephase,Min_sums,Pending3,Pending4),
		save_new_phase_fconstr(Head,bound(lb,[]+1,[Loop_name]))
	;
		Pending4=Pending2
	),
	retract(current_pending_depth(0)),
	%special treatment of ranking functions of the whole phase
	% we add final constraints directly using the ranking functions as they are used most times
	add_general_ranking_functions(Head,Phase),
	compute_all_pending(Phase,Pending4),
	retract(max_pending_depth(Max_pending)).



%! add_general_ranking_functions(Head:term,Call:term,Phase:phase) is det
% add final constraints using the already computed ranking functions
add_general_ranking_functions(Head,Phase):-
	rf_limit(Max),
	current_chain_prefix(Chain_prefix),
	get_ranking_functions_constraints(Max,Head,Phase,Chain_prefix,Ub_fconstrs),
	maplist(save_new_phase_fconstr(Head),Ub_fconstrs).
	
%! compute_all_pending(Head:term,Call:term,Phase:phase,Pending:pending_constrs)
% the main loop of the computation:
% compute one pending element at a time unil there are no more pending elements
compute_all_pending(Phase,Pending):-
	compute_pending(Phase,Pending,Pending_out),
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
	get_one_pending(Pending,Type,loop_vars(Head,Calls),(Depth,Lin_exp,Coeff_bounded),Pending1),	
	assert(current_pending_depth(Depth)),
	compute_pending_element(Type,loop_vars(Head,Calls),Phase,Lin_exp,Coeff_bounded,New_fconstrs,New_iconstrs,Pending1,Pending_out),
	retract(current_pending_depth(Depth)),
	save_used_term(Type,loop_vars(Head,Calls),Lin_exp,Coeff_bounded),
	maplist(save_new_phase_fconstr(loop_vars(Head,[])),New_fconstrs),
	maplist(save_new_phase_iconstr(loop_vars(Head,[])),New_iconstrs).

%case distinction according to what we have to compute

compute_pending_element(maxsum(Loop),loop_vars(Head,Calls),Phase,Exp,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out):-	
	(get_param(debug,[])->
		ground_copy((Head,Exp),(_,Lin_exp_norm_ground)),
		format('computing maxsum(~p) in loop ~p ~n',[Lin_exp_norm_ground,Loop])
	;
		true),
	compute_sum(Head,Calls,Phase,Loop,Exp,max,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out).
compute_pending_element(minsum(Loop),loop_vars(Head,Calls),Phase,Exp,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	(get_param(debug,[])->
		ground_copy((Head,Exp),(_,Lin_exp_norm_ground)),
		format('computing minsum(~p) in loop ~p ~n',[Lin_exp_norm_ground,Loop])
	;
		true),
	compute_sum(Head,Calls,Phase,Loop,Exp,min,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out).	
	
compute_pending_element(Flag,loop_vars(Head,[]),Phase,Exp,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	(get_param(debug,[])->
		ground_copy((Head,Exp),(_,Lin_exp_norm_ground)),
		format('computing ~p(~p) ~n',[Flag,Lin_exp_norm_ground])
	;
		true),
	compute_max_min(Head,Phase,Exp,Flag,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_sum(+Head:term, +Calls:list(term), +Phase:phase, +Loop:loop_id, +Nlinexp:nlinexp, +Max_min:flag, +Bounded:list(itvar), -Fconstrs:list(fconstr),-Iconstrs:list(iconstr),+Pending:pending_constrs,-Pending_out:pending_constrs)
%compute  maxsum or minsum of a linear expression Nlinexp in the loop Loop of the phase Phase
% This Nlinexp is bounding Bounded
%
% The result is a list of new final or intermediate constraints that bound Bounded
% additionally, new pending computations can be added to Pending (resulting in Pending_out)

%trival case where we have 0
compute_sum(_Head,_Calls,_Phase,_Loop,[]+0,Max_min,Bounded,[Fconstr],[],Pending,Pending):-!,
	get_constr_op(Max_min,Op),
	fconstr_new(Bounded,Op,[]+0,Fconstr).
	

% Stored solution

compute_sum(Head,Calls,_Phase,Loop,Lin_exp,Max_min,Bounded,Fconstrs1,[New_iconstr|Iconstrs1],Pending,Pending):-
	get_constr_op(Max_min,Op),
	semi_normalize_le(Lin_exp,Coeff2,Lin_exp_normalized2),
	ground_copy((Head,Lin_exp_normalized2),(_,Lin_exp_norm_ground)),
	sum_found(Loop,Lin_exp_norm_ground,Max_min,loop_vars(Head,Calls),Coeff,Aux_itvar,Fconstrs1,Iconstrs1),!,
	divide_fr(Coeff2,Coeff,Coeff_final),
	new_itvar(Aux_itvar),
	astrexp_new(add([mult([Aux_itvar,Coeff_final])])-add([]),Astrexp),
	iconstr_new(Astrexp,Op,Bounded,New_iconstr),
	(get_param(debug,[])->
			ground_copy((Head,Lin_exp),(_,Lin_exp_ground)),
			format('Found stored solution to sum(~p) in loop ~p ~n',[Lin_exp_ground,Loop]);true).


%Inductive strategy
compute_sum(Head,Calls,Phase,Loop,Lin_exp,Max_min,Bounded,New_fconstrs,New_iconstrs2,Pending,Pending_out):-	
	
	(Loop=0->
	  generate_leave_candidates(Head,Calls,Lin_exp,Max_min,Loop,Exp_list)
	  ;   
	  generate_lecandidates(Head,Calls,Lin_exp,Max_min,Loop,Exp_list)
	),
	(Max_min=max->
	maplist(check_loops_maxsum(Head,Phase,Loop,Bounded,Pending),Exp_list,New_fconstrs_list,New_iconstrs_list,Pending_out_list)
	;
	maplist(check_loops_minsum(Head,Phase,Loop,Bounded,Pending),Exp_list,New_fconstrs_list,New_iconstrs_list,Pending_out_list)
	),
	ut_flat_list(New_fconstrs_list,New_fconstrs),
	%we stay with this option as long as one attempt succeeded 
	%otherwise go to simple multiplication
	
	New_fconstrs\=[],
	ut_flat_list(New_iconstrs_list,New_iconstrs),
	((New_iconstrs=[],Max_min=max)->
		empty_pending(Empty_pending)
		;
		Empty_pending=Pending
		)
	,
	foldl(union_pending,Pending_out_list,Empty_pending,Pending_aux),
	%foldl(union_pending,Pending_out_list,Pending,Pending_aux),
	% this is an heuristic
	% if we are computing a minsum or we have created some intermediate constraints, we apply the basic product strategy as well
	(
	 (Lin_exp\=[]+_ ,(New_iconstrs\=[]; Max_min=min))->
	basic_product(Head,Calls,Loop,Lin_exp,Bounded,Iconstr_extra,Max_min,Pending_aux,Pending_out),
	New_iconstrs2=[Iconstr_extra|New_iconstrs]
	;
	Pending_aux=Pending_out,
	New_iconstrs2=New_iconstrs
	),
	save_sum_found(loop_vars(Head,[]),Loop,Lin_exp,Max_min,Bounded,New_fconstrs,New_iconstrs2).

%Level sum strategy
compute_sum(Head,Calls,_Phase,Loop,Lin_exp,Max_min,Bounded,[],[Iconstr],Pending,Pending_out):-
	Loop\=0,
	(get_param(debug,[])->
			ground_copy((Head,Lin_exp),(_,Lin_exp_ground)),
			format('Applying level sum to ~p in loop ~p ~n',[Lin_exp_ground,Loop]);true),
	level_sum(Head,Calls,Loop,Lin_exp,Bounded,Iconstr,Max_min,Pending,Pending_out),
	save_sum_found(loop_vars(Head,[]),Loop,Lin_exp,Max_min,Bounded,[],[Iconstr]).

%Basic Product strategy
compute_sum(Head,Calls,_Phase,Loop,Lin_exp,Max_min,Bounded,[],[Iconstr],Pending,Pending_out):-
	Lin_exp\=[]+1,!,
	(get_param(debug,[])->
			ground_copy((Head,Lin_exp),(_,Lin_exp_ground)),
			format('Applying basic product to ~p in loop ~p ~n',[Lin_exp_ground,Loop]);true),
	basic_product(Head,Calls,Loop,Lin_exp,Bounded,Iconstr,Max_min,Pending,Pending_out),
	save_sum_found(loop_vars(Head,[]),Loop,Lin_exp,Max_min,Bounded,[],[Iconstr]).
	
compute_sum(_Head,_Calls,_Phase,_Loop,_,_Max_min,_Bounded,[],[],Pending,Pending).	


% check_loops_maxsum(Head:term,Call:term,Phase:phase,Loop:loop_id,Bounded_ini:list(itvar),Pending:pending_constrs,Exp:nlinexp,Fconstrs:list(fconstr),Iconstrs:list(iconstr),Pending_out:pending_constrs) is semidet
% check the effect of the loops of Phase on the candidate Exp and generate the corresponding constraints Fconstrs and Iconstrs
check_loops_maxsum(Head,Phase,Loop,Bounded_ini,Pending,Exp,Fconstrs,Iconstrs,Pending_out):-
	(get_param(debug,[])->print_lin_exp_in_phase(Head,[],Exp);true),
	check_loops_maxsum_1(Phase,Loop,Head,Exp,Pstrexp_pair,Bounded,Pending,Pending_out),!,
	append(Bounded_ini,Bounded,Bounded_vars),
	Pstrexp_pair=add(Pos_summands)-add(Neg_summands),
	((Pos_summands=[],Neg_summands=[]) ->
		fconstr_new(Bounded_vars,ub,Exp,Ub_fconstr),
		Fconstrs=[Ub_fconstr],
		Iconstrs=[]
		;
		new_itvar(Aux_itvar),
		astrexp_new(add([mult([Aux_itvar])|Pos_summands])-add(Neg_summands),Astrexp),
		fconstr_new([Aux_itvar],ub,Exp,Ub_fconstr),
		iconstr_new(Astrexp,ub,Bounded_vars,Ub_iconstr),
		Fconstrs=[Ub_fconstr],
		Iconstrs=[Ub_iconstr]
	).
	
% if a candidate fails		
check_loops_maxsum(_Head,_Phase,_Loop,_Bounded,_Pending,_Exp,[],[],Empty_pending):-
	empty_pending(Empty_pending).

% check_loops_minsum(Head:term,Call:term,Phase:phase,Loop:loop_id,Bounded_ini:list(itvar),Pending:pending_constrs,Exp:nlinexp,Fconstrs:list(fconstr),Iconstrs:list(iconstr),Pending_out:pending_constrs) is semidet
% check the effect of the loops of Phase on the candidate Exp and generate the corresponding constraints Fconstrs and Iconstrs
check_loops_minsum(Head,Phase,Loop,Bounded_ini,Pending,Exp,Fconstrs,Iconstrs,Pending_out):-
	(get_param(debug,[])->print_lin_exp_in_phase(Head,[],Exp);true),
	check_loops_minsum_1(Phase,Loop,Head,Exp,Pstrexp_pair,Bounded,Pending,Pending_out),!,
	append(Bounded_ini,Bounded,Bounded_vars),
	Pstrexp_pair=add(Pos_summands)-add(Neg_summands),
	((Pos_summands=[],Neg_summands=[]) ->
	    fconstr_new(Bounded_vars,lb,Exp,Lb_fconstr),
		Fconstrs=[Lb_fconstr],
		Iconstrs=[]
		;
		new_itvar(Aux_itvar),
		new_itvar(Aux_itvar2),
		astrexp_new(add([mult([Aux_itvar])|Pos_summands])-add([mult([Aux_itvar2])|Neg_summands]),Astrexp),
		negate_le(Exp,Exp_neg),
		fconstr_new([Aux_itvar2],ub,Exp_neg,Ub_fconstr),
		fconstr_new([Aux_itvar],lb,Exp,Lb_fconstr),
		iconstr_new(Astrexp,lb,Bounded_vars,Lb_iconstr),
		Fconstrs=[Ub_fconstr,Lb_fconstr],
		Iconstrs=[Lb_iconstr]
	).
check_loops_minsum(_Head,_Phase,_Loop,_Bounded,_Pending,_Exp,[],[],Empty_pending):-
	empty_pending(Empty_pending).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_loops_maxsum_1([],_,_,_,Empty_pstrexp_pair,[],Pending,Pending):-
   pstrexp_pair_empty(Empty_pstrexp_pair).
%ignore the loop that we started from	
check_loops_maxsum_1([Loop|Loops],Loop,Head,Exp,Pstrexp_pair,Bounded,Pending,Pending_out):-!,
	check_loops_maxsum_1(Loops,Loop,Head,Exp,Pstrexp_pair,Bounded,Pending,Pending_out).
		
check_loops_maxsum_1([Loop2|Loops],Loop,Head,Exp,Pstrexp_pair,Bounded,Pending,Pending_out):-	
	check_loop_maxsum(Head,Exp,Loop2,Pstrexp1_pair,Bounded1,Pending,Pending1),!,
	check_loops_maxsum_1(Loops,Loop,Head,Exp,Pstrexp2_pair,Bounded2,Pending1,Pending_out),
	pstrexp_pair_add(Pstrexp1_pair,Pstrexp2_pair,Pstrexp_pair),
	append(Bounded1,Bounded2,Bounded).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_loops_minsum_1([],_,_,_,Empty_pstrexp_pair,[],Pending,Pending):-
	pstrexp_pair_empty(Empty_pstrexp_pair).
%ignore the loop that we started from	
check_loops_minsum_1([Loop|Loops],Loop,Head,Exp,Pstrexp_pair,Bounded,Pending,Pending_out):-!,
		check_loops_minsum_1(Loops,Loop,Head,Exp,Pstrexp_pair,Bounded,Pending,Pending_out).
		
check_loops_minsum_1([Loop2|Loops],Loop,Head,Exp_diff,Pstrexp_pair,Bounded,Pending,Pending_out):-	
		check_loop_minsum(Head,Exp_diff,Loop2,Pstrexp_pair1,Bounded1,Pending,Pending1),!,
		check_loops_minsum_1(Loops,Loop,Head,Exp_diff,Pstrexp_pair2,Bounded2,Pending1,Pending_out),
		pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair),
		append(Bounded1,Bounded2,Bounded).

%! check_loop_maxsum(Head:term,Call:term,Exp_diff:nlinexp,Flag:term,Loop:loop_id,Pstrexp_pair:pstrexp_pair,Bounded:list(itvar),Pending:pending_constrs,Pending1:pending_constrs)
% check the effect of Loop on Exp_diff, Flag indicates if the original candidate was head or head-tail
% * this can modify the pending constraints Pending->Pending1
% * generates a Pstrexp_pair with the elements that have to be added to the constraint
% * sometimes we can bound some itvar from Loop, those are in Bounded
check_loop_maxsum(Head,Exp,Loop,Pstrexp_pair,Bounded,Pending,Pending1):-
	enriched_loop(Loop,Head,Calls,Cs),
	foldl(get_sum_call(Head,Exp),Calls,[]+0,Sum_calls),
	subtract_le(Exp,Sum_calls,Exp_diff),
	term_variables((Head,Calls),Vars),	
	le_print_int(Exp_diff,Exp_diff_print_int,_),
	negate_le(Exp_diff,Exp_diff_neg),
	le_print_int(Exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
%if Exp does not increase
	(nad_entails(Vars,Cs,[Exp_diff_print_int>=0])->
	 %find a collaborative loop
	    (find_maxsum_constraint(Loop,Head,Calls,Cs,Exp_diff,Bounded,Pending,Pending1)->		
	       	
		   (get_param(debug,[])->format('Loop ~p is collaborative and bounds ~p ~n',[Loop,Bounded]);true)
		   ;
		   (get_param(debug,[])->format('Loop ~p is collaborative~n',[Loop]);true),
			Pending1=Pending,
			Bounded=[]
		),
		pstrexp_pair_empty(Pstrexp_pair)
	;
	 Bounded=[],
%if add a constant	
	(nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta])->
		get_loop_itvar(Loop,Loop_name),
		(Delta=0/1-> 
			pstrexp_pair_empty(Pstrexp_pair)
			;
			Pstrexp_pair=add([mult([Loop_name,Delta])])-add([])
		),
		Pending1=Pending,
		(get_param(debug,[])->format('Loop ~p adds a constant ~p ~n',[Loop,Delta]);true)
		;
		term_variables(Head,Vars_head),
		%select_important_variables(Vars_head,Exp_diff_neg,Vars_of_Interest),
		select_important_variables(Vars,Exp_diff_neg,Vars_of_Interest),
		max_min_linear_expression_all(Exp_diff_neg, Vars_of_Interest, Cs,max, Max_increments),
%add an expression
		(Max_increments\=[]->
				new_itvar(Aux_itvar),
				Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				save_pending_list(maxsum,loop_vars(Head,Calls),Loop,Maxsums,Pending,Pending1),
				ground_copy((Head,Max_increments),(_,Max_increments_ground)),
				(get_param(debug,[])->format('Loop ~p adds an expression ~p~n',[Loop,Max_increments_ground]);true)
			    ;
%reset			    
				max_min_linear_expression_all(Sum_calls, Vars_head, Cs,max, Max_resets),
				Max_resets\=[],
				
   				new_itvar(Aux_itvar),
   				Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
				maplist(fconstr_new([Aux_itvar],ub),Max_resets,Maxsums),
				save_pending_list(maxsum,loop_vars(Head,Calls),Loop,Maxsums,Pending,Pending1),
				(get_param(debug,[])->format('Loop ~p has a reset to  ~p~n',[Loop,Max_resets]);true)
		)
	)
	).

check_loop_maxsum(_Head,_Exp,Loop,[],[],_Pending,_Pending1):-	
	    (get_param(debug,[])->format('Loop ~p has undefined behavior ~n',[Loop]);true),
		fail.	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! check_loop_minsum(Head:term,Call:term,Exp_diff:nlinexp,Loop:loop_id,Pstrexp_pair:pstrexp_pair,Bounded:list(itvar),Pending:pending_constrs,Pending1:pending_constrs)
% similar to check_loop_maxsum but checking the different possibilities in opposite order
% for minsum there are only head-tail candidates
check_loop_minsum(Head,Exp,Loop,Pstrexp_pair,[],Pending,Pending1):-	
	enriched_loop(Loop,Head,Calls,Cs),
	term_variables((Head,Calls),Vars),
	
	foldl(get_sum_call(Head,Exp),Calls,[]+0,Sum_calls),
	subtract_le(Exp,Sum_calls,Exp_diff),
	
	le_print_int(Exp_diff,Exp_diff_print_int,_),
%increasing
	nad_entails(Vars,Cs,[Exp_diff_print_int=<0]),
	negate_le(Exp_diff,Exp_diff_neg),
	le_print_int(Exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
%add a constant		
	(nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta])->
		(is_zero(Delta)->
			pstrexp_pair_empty(Pstrexp_pair)
			;
			get_loop_itvar(Loop,Loop_name),
			Pstrexp_pair=add([mult([Loop_name,Delta])])-add([])
		),
		Pending1=Pending,
		(get_param(debug,[])->format('Loop ~p adds a constant ~p ~n',[Loop,Delta]);true)
		;
		%term_variables(Head,Vars_head),
		select_important_variables(Vars,Exp_diff_neg,Vars_of_Interest),
		max_min_linear_expression_all(Exp_diff_neg, Vars_of_Interest, Cs,min, Max_increments),
%add an expression
	    Max_increments\=[],
		new_itvar(Aux_itvar),
		Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
		maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
		save_pending_list(minsum,Loop,((Head,Calls),Maxsums),Pending,Pending1),
		(get_param(debug,[])->format('Loop ~p adds an expression ~p~n',[Loop,Max_increments]);true)
	).

%collaborative loop	with constraint
check_loop_minsum(Head,Exp,Loop,Pstrexp_pair,Bounded,Pending,Pending1):-
		enriched_loop(Loop,Head,Calls,Cs),
		foldl(get_sum_call(Head,Exp),Calls,[]+0,Sum_calls),
		subtract_le(Exp,Sum_calls,Exp_diff),
		pstrexp_pair_empty(Pstrexp_pair),
		find_minsum_constraint(Loop,Head,Calls,Cs,Exp_diff,Bounded,Pending,Pending1),!,
		(get_param(debug,[])->format('Loop ~p is collaborative with a constraint ~p ~n',[Loop,Bounded]);true).
% we don't substract loops that can decrease the bound
% in theory this could happen, in practice it doesn't seem to happen so we skip it and fail in those cases		
	
check_loop_minsum(_Head,_Exp_diff,Loop,_,_,_Pending,_):-	
	    (get_param(debug,[])->format('Loop ~p has undefined behavior ~n',[Loop]);true),
		fail.	


get_sum_call(Head,Exp,Call,Lin_exp,Lin_exp1):-
	copy_term((Head,Exp),(Call,Exp1)),
	sum_le(Exp1,Lin_exp,Lin_exp1).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%! compute_max_min(Head:term,Call:term,Phase:phase,Lin_exp:nlinexp,Max_min:flag,Bounded:list(itvar),New_fconstrs:list(fconstr),New_iconstrs:list(iconstr),Pending:pending_constrs,Pending:pending_constrs)
% Compute the maximum or minimum value of Lin_exp in any iteration of the loops of Phase
% this computation is recorded with a set on new final and intermediate constraints
%
% * first try to find a similar linear expression whose maximum/minimum has already been computed (cacheing)
% * if not, try using transitive invariants (we have them precomputed)
% * finally, try the incremental approach 
compute_max_min(Head,Phase,Lin_exp,Max_min,Bounded,New_fconstrs,New_iconstrs,Pending,Pending):-
	max_min_found(Head,Phase,(Lin_exp_normalized2,Coeff2,Constant2),Max_min,Res),
	normalize_max_min(Lin_exp,(Lin_exp_normalized,Coeff,Constant)),
	% there is a linear expression that has been computed and is a multiple of the one we are computing
	Lin_exp_normalized2==Lin_exp_normalized,!,
	% we failed to compute a maximum or minimum
	(Res=none->
	   New_fconstrs=[],
	   New_iconstrs=[]
	;
	
	divide_fr(Coeff,Coeff2,New_coeff),
	multiply_fr(New_coeff,Constant2,Constant3),
	subtract_fr(Constant,Constant3,Final_constant),
	get_constr_op(Max_min,Op),
	%if there a final constraint and the new coefficients and constant are 1 and 0
	% we can simply generate final constraints
	((Res=final(Maxs_out),0=Final_constant,New_coeff=1)->
		maplist(fconstr_new(Bounded,Op),Maxs_out,New_fconstrs),
		New_iconstrs=[]
		;
		%otherwise, we generate two constraints
		% the first can be final or intermediate depending on the stored value
		(Res=final(Maxs_out)->
			new_itvar(Aux_itvar),
			maplist(fconstr_new([Aux_itvar],Op),Maxs_out,New_fconstrs),
			New_iconstrs1=[]
		;
			Res=inter(Astrexp2),
			New_fconstrs=[],
			new_itvar(Aux_itvar),
			iconstr_new(Astrexp2,Op,[Aux_itvar],Iconstr1),
			New_iconstrs1=[Iconstr1]
		),
		% the second one is intermediate and multiplies by the new coefficient and adds the new constant
		(greater_fr(Final_constant,0)->
		   astrexp_new(add([mult([Aux_itvar,New_coeff]),mult([Final_constant])])-add([]),Astrexp)
		   ;
		   astrexp_new(add([mult([Aux_itvar,New_coeff])])-add([mult([-1,Final_constant])]),Astrexp)
		),
		iconstr_new(Astrexp,Op,Bounded,Iconstr2),
		New_iconstrs=[Iconstr2|New_iconstrs1]
	)
	),
	(get_param(debug,[])->
			ground_copy((Head,Lin_exp),(_,Lin_exp_ground)),
			format('Found stored solution to max/min(~p) ~n',[Lin_exp_ground]);true).


% a constant does not need to be maximized/minimized
compute_max_min(_Head,_Phase,[]+C,Max_min,Bounded,New_fconstrs,[],Pending,Pending):-!,
	get_constr_op(Max_min,Op),
	maplist(fconstr_new(Bounded,Op),[[]+C],New_fconstrs).
	



%use  increments and resets procedure	
compute_max_min(Head,Phase,Lin_exp,Max_min,Bounded,[Fconstr],[Iconstr],Pending,Pending_out):-
	get_constr_op(Max_min,Op),
	%we have to consider the case where the value is not reseted
	new_itvar(Aux_itvar),
	fconstr_new([Aux_itvar],Op,Lin_exp,Fconstr),
	% check the effect of the loops
	(Max_min=max->
	check_loops_max(Phase,Head,Lin_exp,Resets,Pstrexp_pair2,Pending,Pending_out),
	(Resets=[] ->
	   Max_resets=Aux_itvar
	   ;
	   Max_resets=max([Aux_itvar|Resets])
	   ),
	Pstrexp_pair1=add([mult([Max_resets])])-add([])
	;
	check_loops_min(Phase,Head,Lin_exp,Resets,Pstrexp_pair2,Pending,Pending_out),
	(Resets=[] ->
	   Min_resets=Aux_itvar
	   ;
	   Min_resets=min([Aux_itvar|Resets])
	   ),
	Pstrexp_pair1=add([mult([Min_resets])])-add([])
	),
	pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair),
	astrexp_new(Pstrexp_pair,Astrexp),
	iconstr_new(Astrexp,Op,Bounded,Iconstr),
    save_max_min_found(Head,Phase,Lin_exp,Max_min,inter(Astrexp)).

    
%failed    
compute_max_min(Head,Phase,Lin_exp,Max_min,_Bounded,[],[],Pending,Pending):-
	save_max_min_found(Head,Phase,Lin_exp,Max_min,none).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%			


check_loops_max([],_Head,_Lin_exp,[],Empty_pstrexp_pair,Pending,Pending):-
	pstrexp_pair_empty(Empty_pstrexp_pair).
	
check_loops_max([Loop|Loops],Head,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	check_loop_max(Loop,Head,Lin_exp,Resets1,Pstrexp_pair1,Pending,Pending_aux),
	check_loops_max(Loops,Head,Lin_exp,Resets2,Pstrexp_pair2,Pending_aux,Pending_out),
	append(Resets1,Resets2,Resets),
	pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair).

%! check_loops_max(Loop:loop_id,Head:term,Call:term,Lin_exp:alinexp,Resets:list(itvar),Pstrexp_pair:pstrexp_pair,Pending:pending_constrs,Pending_out:pending_constrs)
% check the different possible behaviors of Loop with respect to Lin_exp
% * the loop does not increase Lin_exp: do nothing
% * the loop increases Lin_exp by a constant Delta: add maxsum(Loop,Delta) to the cost (in Pstrexp)
% * the loop increases Lin_exp by a linear expression Max_increment: add maxsum(Loop,Max_increment) to the cost
% * the loop resets Lin_exp to Max_resets: add Max_resets to the resets

	
check_loop_max(Loop,Head,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	%FIXME for multiple recursion
	enriched_loop(Loop,Head,Calls,Cs),
	maplist(get_difference_version(Head,Lin_exp),Calls,Lin_exp_diffs),
	term_variables((Head,Calls),Vars),
	exclude(is_positive(Vars,Cs),Lin_exp_diffs,Lin_exp_diffs_non_pos),
% the lin_exp does not increase
	(Lin_exp_diffs_non_pos=[]->
		(get_param(debug,[])->format('Loop ~p does not increase the expression~n',[Loop]);true),
		Resets=[],
		pstrexp_pair_empty(Pstrexp_pair),
		Pending_out=Pending
		;
% add a constant
		maplist(negate_le,Lin_exp_diffs_non_pos,Lin_exp_diffs_neg),
		(foldl(get_maximum_increase(Cs),Lin_exp_diffs_neg,0,Delta)->
			(get_param(debug,[])->format('Loop ~p  increases the expression by ~p ~n',[Loop,Delta]);true),
			get_loop_itvar(Loop,Loop_name),
			Pstrexp_pair=add([mult([Loop_name,Delta])])-add([]),
			Resets=[],
			Pending_out=Pending
		;
			term_variables(Head,Vars_head),
			select_important_variables(Vars_head,Lin_exp,Vars_of_Interest),
			max_min_linear_expression_list_all(Lin_exp_diffs_neg,Vars, Vars_of_Interest, Cs,max, Max_increments),
%add an expression		
			(Max_increments\=[]->
				(get_param(debug,[])->
				    ground_copy((Head,Max_increments),(_,Max_increments_ground)),
				    format('Loop ~p  increases the expression by ~p ~n',[Loop,Max_increments_ground]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				save_pending_list(maxsum,Loop,((Head,Calls),Maxsums),Pending,Pending_out),
				Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
				Resets=[]
			;
%reset		
				maplist(get_tail_version(Head,Lin_exp),Calls,Lin_exp_tails),
				max_min_linear_expression_list_all(Lin_exp_tails, Vars_head, Cs,max, Maxs_resets),
				Maxs_resets\=[],!,
				(get_param(debug,[])->
				    ground_copy((Head,Maxs_resets),(_,Maxs_resets_ground)),
				    format('Loop ~p  resets the expression to ~p ~n',[Loop,Maxs_resets_ground]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Maxs_resets,Maxtops),			
				save_pending_list(max,Loop,(Head,Maxtops),Pending,Pending_out),
				pstrexp_pair_empty(Pstrexp_pair),
				Resets=[Aux_itvar]
			)
		)
	).
				
				

is_positive(Vars,Cs,Lin_exp):-
	le_print_int(Lin_exp,Lin_exp_int,_),
	nad_entails(Vars,Cs,[Lin_exp_int>=0]).
	
get_maximum_increase(Cs,Lin_exp_neg,Delta,Delta2):-
	le_print_int(Lin_exp_neg,Exp_diff_neg_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta1]),
	greater_fr(Delta1,0),
	max_fr(Delta,Delta1,Delta2).				
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_loops_min([],_Head,_Lin_exp,[],Empty_pstrexp_pair,Pending,Pending):-
	pstrexp_pair_empty(Empty_pstrexp_pair).
	
check_loops_min([Loop|Loops],Head,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	check_loop_min(Loop,Head,Lin_exp,Resets1,Pstrexp_pair1,Pending,Pending_aux),
	check_loops_min(Loops,Head,Lin_exp,Resets2,Pstrexp_pair2,Pending_aux,Pending_out),
	append(Resets1,Resets2,Resets),
	pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair).

%! check_loop_min(Loop:loop_id,Head:term,Call:term,Lin_exp:alinexp,Resets:list(itvar),Pstrexp_pair:pstrexp_pair,Pending:pending_constrs,Pending_out:pending_constrs)
% check the different possible behaviors of Loop with respect to Lin_exp
% similar to check_loops_max
check_loop_min(_Loop,_Head,_Lin_exp,_Resets,_Pstrexp_pair,_Pending,_Pending_out):-
	fail.

/*

	enriched_loop(Loop,Head,[Call],Cs),
	Calls=[Call],
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	le_print_int(Lin_exp_diff,Exp_diff_int,Exp_diff_denominator),
	%negate_le(Lin_exp_diff,Lin_exp_diff_neg),
	%le_print_int(Lin_exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
	term_variables((Head,Call),Vars),
% the Lin_exp does not decrease
	(nad_entails(Vars,Cs,[Exp_diff_int=<0])->
		Resets=[],
		pstrexp_pair_empty(Pstrexp_pair),
		Pending_out=Pending
		;
% decreases by a constant
		((nad_maximize([Exp_diff_int=Exp_diff_denominator*D|Cs],[D],[Delta]),greater_fr(Delta,0))->
			get_loop_itvar(Loop,Loop_name),
			Pstrexp_pair=add([])-add([mult([Loop_name,Delta])]),
			Resets=[],
			Pending_out=Pending
		;
			term_variables(Head,Vars_head),
			select_important_variables(Vars_head,Lin_exp,Vars_of_Interest),
			max_min_linear_expression_all(Lin_exp_diff, Vars_of_Interest, Cs,max, Max_increments),
%decreases by an expression		
			(Max_increments\=[]->
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				save_pending_list(maxsum,Loop,((Head,Calls),Maxsums),Pending,Pending_out),
				Pstrexp_pair=add([])-add([mult([Aux_itvar])]),
				Resets=[]
			;
%reset		
				copy_term((Head,Lin_exp),(Call,Lin_exp_p)),
				max_min_linear_expression_all(Lin_exp_p, Vars_head, Cs,min, Mins_resets),
				Mins_resets\=[],!,
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],lb),Mins_resets,Maxtops),
				save_pending_list(max,Loop,(Head,Maxtops),Pending,Pending_out),
				pstrexp_pair_empty(Pstrexp_pair),
				Resets=[Aux_itvar]
			)
		)
	).
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% auxiliary predicates for maxsum and minsum


level_sum(Head,Calls,Loop,Lin_exp,Bounded,Aux_exp,Max_min,Pending,Pending_out):-	
	get_constr_op(Max_min,Op),
	enriched_loop(Loop,Head,Calls,Cs),
	new_itvar(Aux_itvar),
	get_loop_depth_itvar(Loop,Loop_itvar),
	astrexp_new(add([mult([Loop_itvar,Aux_itvar])])-add([]),Astrexp),
	(is_head_expression(Head,Lin_exp)->
		fconstr_new([Aux_itvar],Op,Lin_exp,Fconstr),
		Max_fconstrs=[Fconstr]
	;
	 Head=..[_|Vars_head],
	 max_min_linear_expression_all(Lin_exp, Vars_head, Cs,Max_min, Maxs_exps),
	 maplist(fconstr_new([Aux_itvar],Op),Maxs_exps,Max_fconstrs)
	 ),
	save_pending_list(maxsum,loop_vars(Head,[]),0,Max_fconstrs,Pending,Pending_out),
    Aux_exp=bound(Op,Astrexp,Bounded).	
%! find_maxsum_constraint(Loop:loop_id,Head:term,Call:term,Cs:polyhedron,Exp_diff:nlinexp,Flag:flag,Bounded:list(itvar),Pending:pending_constrs,Pending_out:pending_constrs)
% try to find a pending maxsum that can be bounded by Exp_diff
% we check that Exp_diff>= Exp2 and in case we are dealing with a head candidate
% we also check Exp_original>=Exp2
find_maxsum_constraint(Loop,Head,Calls,Cs,Exp_diff,Bounded,Pending,Pending_out):-
		extract_pending(Loop,maxsum,Pending,loop_vars(Head,Calls),(_Depth,Exp2,Bounded),Pending_out),
		term_variables((Head,Calls),Vars),
		subtract_le(Exp_diff,Exp2,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),
		!,
		save_used_term(maxsum(Loop),loop_vars(Head,Calls),Exp2,Bounded).



%! find_minsum_constraint(Loop:loop_id,Head:term,Call:term,Cs:polyhedron,Exp_diff:nlinexp,Flag:flag,Bounded:list(itvar),Pending:pending_constrs,Pending_out:pending_constrs)
% try to find a pending minsum that can be bounded by Exp_diff
% we check that Exp_diff=< Exp2 	
find_minsum_constraint(Loop,Head,Calls,Cs,Exp_diff,Bounded,Pending,Pending):-
		extract_pending(Loop,minsum,Pending,loop_vars(Head,Calls),(_Depth,Exp2,Bounded),_Pending_out),
		term_variables((Head,Calls),Vars),
		subtract_le(Exp2,Exp_diff,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),!,
		save_used_term(minsum(Loop),loop_vars(Head,Calls),Exp2,Bounded).
%this is important for lower bounds!	

find_minsum_constraint(Loop,Head,Calls,Cs,Exp_diff,Bounded,Pending,Pending):-
		used_term(minsum,Loop,Head,Calls,Exp2,Bounded),	
		term_variables((Head,Calls),Vars),
		subtract_le(Exp2,Exp_diff,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),!.


%! get_ranking_functions_constraints(Max:int,Head:term,Call:term,Phase:phase,Chain:chain,Fconstrs:list(fconstr))
% generate at most Max upper bound final constraints from the ranking functions
% -the ranking function itself
% -the difference between the ranking function at the beginning and at the end of the phase
get_ranking_functions_constraints(Max,Head,Phase,Chain,Fconstrs):-
	bagof_no_fail(Rf,
		ranking_function(Head,Chain,Phase,Rf)
	  ,Rfs),
	ut_split_at_pos(Rfs,Max,Rfs_selected,_),
	maplist(get_loop_itvar,Phase,Bounded),
	maplist(fconstr_new(Bounded,ub),Rfs_selected,Fconstrs).



	
%! 	generate_lecandidates(Head:term,Call:term,Lin_exp:nlinexp,Max_min:flag,Loop:loop_id,Total_exps:list(nlinexp))
% generate linear expressions that are candidates to represent the
% sum of all the instances of Lin_exp in Loop 
%
% use Farkas lemma
generate_lecandidates(Head,Calls,Lin_exp,max,Loop,Diff_list_selected_set):-
	enriched_loop(Loop,Head,Calls,Cs),	
	rf_limit(Max_candidates),
	difference_constraint_farkas_multiple_ub(Head,Calls,Cs,Lin_exp,Diff_list),
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_),
	from_list_sl(Diff_list_selected,Diff_list_selected_set),
	Diff_list_selected_set\=[].

	
	
generate_lecandidates(_Head,_Calls,_Lin_exp,min,_Loop,_Diff_list):-
	fail.
%	enriched_loop(Loop,Head,Calls,Cs),	
%	enriched_loop(0,Head,[],Cs2),
%	nad_glb(Cs,Cs2,Cs_total),
%	cs_prev(Head,Cs_prev),
%	rf_limit(Max_candidates),
%	difference_constraint_farkas_lb(Head,Calls,Cs_total,Cs_prev,Lin_exp,Diff_list),
%	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_).
	
generate_leave_candidates(Head,[],Lin_exp,max,0,Diff_list_selected_set):-
	enriched_loop(Loop2,Head,Calls,Cs),	Loop2\=0,
	rf_limit(Max_candidates),
	farkas_leave_ub_candidate(Head,Calls,Cs,Lin_exp,Diff_list),
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_),
	from_list_sl(Diff_list_selected,Diff_list_selected_set),
	Diff_list_selected_set\=[].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% general auxiliary predicates

is_zero(0).
is_zero(0/1).

rf_limit(N):-
	get_param(n_rankings,[N]).
	
get_difference_version(Head,Lin_exp,Call,Lin_exp_diff):-
	copy_term((Head,Lin_exp),(Call,Lin_expp)),
	subtract_le(Lin_exp,Lin_expp,Lin_exp_diff).		
get_tail_version(Head,Lin_exp,Call,Lin_expp):-
	copy_term((Head,Lin_exp),(Call,Lin_expp)).
	
le_print_int(Lin_exp,Exp,Den):-
		integrate_le(Lin_exp,Den,Lin_exp_nat),
		write_le(Lin_exp_nat,Exp).
get_constr_op(max,ub).
get_constr_op(min,lb).	

select_important_variables(Vars_head,Lin_exp,Vars_of_Interest):-
	from_list_sl(Vars_head,Vars_head_set),
	term_variables(Lin_exp,Vars_exp),
	from_list_sl(Vars_exp,Vars_exp_set),
	difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest).
	
put_inside_mult(Factor,mult([Factor])).

				
is_head_expression(Head,Exp):-
	copy_term((Head,Exp),(Head2,Exp2)),
	numbervars(Head2,0,_),
	ground(Exp2).
	
