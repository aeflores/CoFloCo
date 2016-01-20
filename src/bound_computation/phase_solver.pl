/** <module> phase_solver

This module computes the cost structure of a phase in terms of the variables 
at the beginning and the end of the phase.

 Additional data structures used in this module are:
  
 Pending_constrs contains the information of the constraints that are pending to be computed
 It has the form
 pending(Maxs,Mins,Maxsums,Minsums)
 where
  * Maxs=list_set(Elem)
  * Mins=list_set(Elem)
  * Maxsums=multimap(loop_id,Elem)
  * Minsums=multimap(loop_id,Elem)
  And Elem=(Depth:int,Linexp:nlinexp,Bounded:list(itvar))
 an Elem (Depth,Linexp,Bounded) represents a constraint "Linexp OP Bounded"
 where OP is =< or >= depending on whether the elem is in Maxs/Maxsums or Mins/Minsums
 Depth represents the depth of the recursion and is used to avoid infinite computations

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
			new_itvar/1,
			get_loop_itvar/2,
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
			difference_constraint_farkas_ub/6,
			difference_constraint_farkas_lb/5
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
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_increase/3]).
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map)).
:- use_module(stdlib(multimap)).


:-use_module(library(apply_macros)).
:-use_module(library(lists)).

%! phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cstr)
% store the cost structure of a phase given a local invariant
% for cacheing purposes
:- dynamic  phase_cost/5.

%! current_chain(Chain:chain)
% the chain to which the phase being computed belongs
% used to 
:- dynamic  current_chain/1.

%! init_phase_solver is det
% clear all the intermediate results
init_phase_solver:-
	retractall(phase_cost(_,_,_,_,_,_)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_phases_cost(+Phases:list(phase),+Chain:chain,+Head:term,+Call:term,-Costs:list(cstr)) is det
% compute cost structures for the phases Phases that belong to Chain.
% the constraints of the cost structure are expressed in terms of the variables at the beginnig and end of the chain (Head and Call)
compute_phases_cost([],_,_,_,[]).
compute_phases_cost([Phase|More],Chain,Head,Call,[Cost|Costs]):-
	forward_invariant(Head,([Phase|More],_),Forward_inv_hash,Forward_inv),
	assert(current_chain(Chain)),
	%obtain a cost structure in terms of the variableUb_fconstrsnning and end of the phase
	compute_phase_cost(Phase,Head,Call,(Forward_inv_hash,Forward_inv),Cost),
	retract(current_chain(Chain)),
	%(get_param(debug,[])->print_phase_cost(Phase,Head,Call,Cost);true),
	compute_phases_cost(More,Chain,Head,Call,Costs).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! compute_phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cstr) is det
% Obtain the cost of a phase given a forward invariant.
compute_phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost):-
	phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv2),Cost),
	Forward_inv2==Forward_inv,!,
	counter_increase(compressed_phases1,1,_).
	
% in a non-iterative phase, we just obtain the cost of the equation
compute_phase_cost(Non_it,Head,Call,(Forward_hash,Forward_inv),Cost):-
	number(Non_it),	
	profiling_start_timer(equation_cost),
	get_loop_cost(Head,Call1,(Forward_hash,Forward_inv),Non_it,Cost),
	(Call1\=none->Call1=Call;true),
	profiling_stop_timer_acum(equation_cost,_),
	assert(phase_cost(Non_it,Head,Call,(Forward_hash,Forward_inv),Cost)).

compute_phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost):-
    %get the cost of each iterative component of the phase	
	profiling_start_timer(equation_cost),
	maplist(get_equation_loop_cost(Head,Call,(Forward_hash,Forward_inv)),Phase,Costs),
	profiling_stop_timer_acum(equation_cost,_),
	compute_iterative_phase_cost(Costs,Head,Call,Forward_inv,Phase,Cost),
	assert(phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost)).

get_equation_loop_cost(Head,Call,(Forward_hash,Forward_inv),Eq_id,Cost2):-
	get_loop_cost(Head,Call,(Forward_hash,Forward_inv),Eq_id,Cost),
	cstr_extend_variables_names(Cost,it(Eq_id),Cost2).
	

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% auxiliary dynamic predicates

%recording the resulting cost of the phase and recovering

%! new_phase_fconstr(Head:term,Call:term,Phase:phase,Fconstr)
% temporary storage of final constraints for the phase Phase
:-dynamic new_phase_fconstr/4.

%! new_phase_iconstr(Head:term,Call:term,Phase:phase,Iconstr)
% temporary storage of intermediate for the phase Phase
:-dynamic new_phase_iconstr/4.


save_new_phase_fconstr(Head,Call,Phase,FConstr):-
	assert(new_phase_fconstr(Head,Call,Phase,FConstr)).
save_new_phase_iconstr(Head,Call,Phase,IConstr):-
	assert(new_phase_iconstr(Head,Call,Phase,IConstr)).
	
collect_phase_results(Head,Call,Phase,Ub_fconstrs,Lb_fconstrs,Iconstrs):-
	bagof_no_fail(Top,(new_phase_fconstr(Head,Call,Phase,Top)),Fconstrs),
	partition(is_ub_bconstr,Fconstrs,Ub_fconstrs,Lb_fconstrs),
	bagof_no_fail(Aux,(new_phase_iconstr(Head,Call,Phase,Aux)),Iconstrs),
	retractall(new_phase_fconstr(_,_,_,_)),
	retractall(new_phase_iconstr(_,_,_,_)).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%cacheing computation of sums, maxs and mins

%FIXME simplify this
%! sum_found(Loop:loop_id,Lin_exp_norm_ground:alinexp_ground,Max_min:flag,Head:term,Call:term,Coeff,Aux_itvar:Var,Fconstrs:list(fconstr),IConstrs:list(iconstr))
%  a sum has been found for the linear expression Lin_exp_norm_ground*Coeff and it corresponds to the constraints Fconstrs and IConstrs
% one can use this sum by simply unifying Aux_itvar with the itvar that we want to bound
:-dynamic sum_found/9.
%FIXME simplify this
%! max_min_found(Head:term,Call:term,Phase:phase,(Lin_exp_normalized2,Coeff2,Constant2),Max_min:flag,Res:?)
% a max or min has been found for the linear expression Lin_exp_normalized2*Coeff2+Constant2 and is Res
% we can use this information to compute maxs or mins for similar expressions
:-dynamic max_min_found/6.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%temporary information that we want available during the computation of the phase cost

%! forward_invariant_temp(Head:term,Call:term,Inv:polyhedron)
% the forward invariant valid for the current chain, it gives us additional information
:-dynamic forward_invariant_temp/3.

%! max_pending_depth(N:int)
% maximum number or 'recursive' definitions of cost 
% it depends on the number of loops in the phase and could be adjusted
:-dynamic max_pending_depth/1.

%! current_pending_depth(N:int)
% how many recursive calls we have so far for a given expression
:-dynamic current_pending_depth/1.

	
%! compute_iterative_phase_cost(+Costs:list(cstr),+Head:term,+Call:term,+Forward_inv:polyhedron,+Phase:phase,-Cost_final:cstr) is det
% Compute the cost of an iterative phase by combining the cost of each of its loops
compute_iterative_phase_cost(Costs,Head,Call,Forward_inv,Phase,Cost_final):-
	assert(forward_invariant_temp(Head,Call,Forward_inv)),
	maplist(cstr_remove_cycles,Costs,Costs_simple),
	maplist(cstr_propagate_sums,Phase,Costs_simple,Costs_propagated2,Max_min_pairs_Sums_pairs),
	cstr_empty(Empty_cost),
	foldl(cstr_join,Costs_propagated2,Empty_cost,cost([],[],Iconstrs,Bases,Base)),
	%unpack result of propagation
	maplist(tuple,Max_min_pairs,Sums_pairs,Max_min_pairs_Sums_pairs),
	maplist(tuple,Maxs,Mins,Max_min_pairs),
	maplist(tuple,Max_sums,Min_sums,Sums_pairs),
	%we add pending sums for the number of iterations of each loop as they will be needed in most occasions anyway
	% this way, we can always assume they are computed
	maplist(get_it_sum_constraint(ub),Phase,It_cons_max), 
    maplist(get_it_sum_constraint(lb),Phase,It_cons_min),    
	maplist(append,It_cons_max,Max_sums,Max_sums1),
	maplist(append,It_cons_min,Min_sums,Min_sums1),
	%main predicate
	compute_sums_and_max_min_in_phase(Head,Call,Phase,Maxs,Mins,Max_sums1,Min_sums1),
	%collect stored results
	collect_phase_results(Head,Call,Phase,Final_ub_fconstrs,Final_lb_fconstrs,New_iconstrs),
	retractall(forward_invariant_temp(_,_,_)),
	append(New_iconstrs,Iconstrs,Iconstrs_final),
	cstr_remove_cycles(cost(Final_ub_fconstrs,Final_lb_fconstrs,Iconstrs_final,Bases,Base),Cost_final),!.
	
get_it_sum_constraint(ub,Loop,[bound(ub,[]+1,[Loop_name])]):-
	get_loop_itvar(Loop,Loop_name).
get_it_sum_constraint(lb,Loop,[bound(lb,[]+1,[Loop_name])]):-
	get_loop_itvar(Loop,Loop_name).	
	
%! compute_sums_and_max_min_in_phase(Head:term,Call:term,Phase:phase,Maxs:list(fconstrs),Mins:list(fconstrs),Max_sums:list(fconstrs),Min_sums:list(fconstrs))
% store all the pending computations in Pending structure and compute them incrementally
% the results are stored in the database and collected later
compute_sums_and_max_min_in_phase(Head,Call,Phase,Maxs,Mins,Max_sums,Min_sums):-
	empty_pending(Empty_pending),
	length(Phase,N),
	Max_pending is 2*N,
	assert(max_pending_depth(Max_pending)),
	retractall(max_min_found(_,_,_,_,_,_)),
	retractall(sum_found(_,_,_,_,_,_,_,_,_)),
	%we start from depth 0
	assert(current_pending_depth(0)),
	foldl(save_pending_list(max),Phase,Maxs,Empty_pending,Pending1),
	foldl(save_pending_list(min),Phase,Mins,Pending1,Pending2),
	foldl(save_pending_list(maxsum),Phase,Max_sums,Pending2,Pending3),
	foldl(save_pending_list(minsum),Phase,Min_sums,Pending3,Pending4),
	retract(current_pending_depth(0)),
	%special treatment of ranking functions of the whole phase
	% we add final constraints directly using the ranking functions as they are used most times
	add_general_ranking_functions(Head,Call,Phase),
	
	compute_all_pending(Head,Call,Phase,Pending4),
	retract(max_pending_depth(Max_pending)).

%! add_general_ranking_functions(Head:term,Call:term,Phase:phase) is det
% add final constraints using the already computed ranking functions
add_general_ranking_functions(Head,Call,Phase):-
	rf_limit(Max),
	current_chain(Chain),
	get_ranking_functions_constraints(Max,Head,Call,Phase,Chain,Ub_fconstrs),
	maplist(save_new_phase_fconstr(Head,Call,Phase),Ub_fconstrs),
	(get_param(compute_lbs,[])->
	   get_ranking_functions_lower_constraints(Max,Head,Call,Phase,Chain,Lb_fconstrs),
	   maplist(save_new_phase_fconstr(Head,Call,Phase),Lb_fconstrs)
	   ;
	   true
	 ).
	
%! compute_all_pending(Head:term,Call:term,Phase:phase,Pending:pending_constrs)
% the main loop of the computation:
% compute one pending element at a time unil there are no more pending elements
compute_all_pending(Head,Call,Phase,Pending):-
	compute_pending(Head,Call,Phase,Pending,Pending_out),
	compute_all_pending(Head,Call,Phase,Pending_out).

compute_all_pending(_,_,_,_).

%! compute_pending(Head:term,Call:term,Phase:phase,Pending:pending_constrs,Pending_out:pending_constrs)
% extract one pending constraint from Pending and compute it
% each pending element has a Depth associated to avoid infinite computations, each new pending element created will have
% an increased depth and no pending elements will be added beyond the maximum depth
%
% The result of computing a pending element is a set of final constraints (New_fconstrs) and intermediate constraints (New_iconstrs)
% that are stored in the database
compute_pending(Head,Call,Phase,Pending,Pending_out):-
	get_one_pending(Pending,Type,(Depth,Lin_exp,Coeff_bounded),Pending1),
	(get_param(debug,[])->print_pending_info(Head,Call,Type,Lin_exp,Pending1);true),
	assert(current_pending_depth(Depth)),
	compute_pending_element(Type,Head,Call,Phase,Lin_exp,Coeff_bounded,New_fconstrs,New_iconstrs,Pending1,Pending_out),
	retract(current_pending_depth(Depth)),
	maplist(save_new_phase_fconstr(Head,Call,Phase),New_fconstrs),
	maplist(save_new_phase_iconstr(Head,Call,Phase),New_iconstrs).

%case distinction according to what we have to compute

compute_pending_element(maxsum(Loop),Head,Call,Phase,Exp,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	compute_sum(Head,Call,Phase,Loop,Exp,max,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out).
compute_pending_element(minsum(Loop),Head,Call,Phase,Exp,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	compute_sum(Head,Call,Phase,Loop,Exp,min,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out).	
compute_pending_element(max,Head,Call,Phase,Exp,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	compute_max_min(Head,Call,Phase,Exp,max,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out).	
compute_pending_element(min,Head,Call,Phase,Exp,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	compute_max_min(Head,Call,Phase,Exp,min,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out).	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_sum(+Head:term, +Call:term, +Phase:phase, +Loop:loop_id, +Nlinexp:nlinexp, +Max_min:flag, +Bounded:list(itvar), -Fconstrs:list(fconstr),-Iconstrs:list(iconstr),+Pending:pending_constrs,-Pending_out:pending_constrs)
%compute  maxsum or minsum of a linear expression Nlinexp in the loop Loop of the phase Phase
% This Nlinexp is bounding Bounded
%
% The result is a list of new final or intermediate constraints that bound Bounded
% additionally, new pending computations can be added to Pending (resulting in Pending_out)

%trival case where we have 0
compute_sum(_Head,_Call,_Phase,_Loop,[]+0,Max_min,Bounded,[Fconstr],[],Pending,Pending):-!,
	get_constr_op(Max_min,Op),
	fconstr_new(Bounded,Op,[]+0,Fconstr).
	
%maxsum: partial ranking function (a special case of linear sum)
compute_sum(Head,Call,Phase,Loop,[]+1,max,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out):-!,
    current_chain(Chain),
    %obtain the ranking functions for the loop and their difference version
    % if rf=x+y the difference version is (x+y)-(x'+y')
	bagof_no_fail(Rf,
	Deps^Deps_type^Loops^
	(
		partial_ranking_function(Head,Chain,Phase,Loops,Rf,Deps,Deps_type),
		contains_sl(Loops,Loop)		
	),Rfs),
	maplist(get_difference_version(Head,Call),Rfs,Rfs_diff),
	append(Rfs,Rfs_diff,Rfs_all),
	% check the effects of other loops and build resulting bound constraints
	% we try this for each ranking function
	maplist(check_loops_maxsum(Head,Call,Phase,Loop,Bounded,Pending),Rfs_all,New_fconstrs_list,New_iconstrs_list,Pending_out_list),
	ut_flat_list(New_fconstrs_list,New_fconstrs),
	ut_flat_list(New_iconstrs_list,New_iconstrs),
	% we join all the pending constraints generated by the succesful computations
	empty_pending(Empty_pending),
	foldl(union_pending,Pending_out_list,Empty_pending,Pending_out_aux),
	%if all the computations have failed, we keep the initial pending_constrs 
	% we do it this way because check_loops_maxsum can remove pending elements
	% and we want to discard them if they are removed in all the alternatives
	(empty_pending(Pending_out_aux)->
		Pending_out=Pending
		;
		Pending_out=Pending_out_aux
	).

% minsum: partial ranking function (a special case of linear sum)
%/*
compute_sum(Head,Call,Phase,Loop,[]+1,min,Bounded,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	current_chain(Chain),
	bagof_no_fail(Lb,get_partial_lower_bound(Head,Call,Chain,Loop,Lb),Lbs),
	maplist(check_loops_minsum(Head,Call,Phase,Loop,Bounded,Pending),Lbs,New_fconstrs_list,New_iconstrs_list,Pending_out_list),
	ut_flat_list(New_fconstrs_list,New_fconstrs),
	ut_flat_list(New_iconstrs_list,New_iconstrs),
	New_fconstrs\=[],!,
	empty_pending(Empty_pending),
	foldl(union_pending,Pending_out_list,Empty_pending,Pending_out_aux),
	(empty_pending(Pending_out_aux)->
		Pending_out=Pending
		;
		Pending_out=Pending_out_aux
	).		
%*/
% Stored solution
compute_sum(Head,Call,_Phase,Loop,Lin_exp,Max_min,Bounded,Fconstrs1,[New_iconstr|Iconstrs1],Pending,Pending):-
	get_constr_op(Max_min,Op),
	semi_normalize_le(Lin_exp,Coeff2,Lin_exp_normalized2),
	ground_copy((Head,Call,Lin_exp_normalized2),(_,_,Lin_exp_norm_ground)),
	sum_found(Loop,Lin_exp_norm_ground,Max_min,Head,Call,Coeff,Aux_itvar,Fconstrs1,Iconstrs1),!,
	divide_fr(Coeff2,Coeff,Coeff_final),
	new_itvar(Aux_itvar),
	astrexp_new(add([mult([Aux_itvar,Coeff_final])])-add([]),Astrexp),
	iconstr_new(Astrexp,Op,Bounded,New_iconstr).


%triangular strategy
% valid for minsums of expressions that are not constant	
compute_sum(Head,Call,Phase,Loop,Lin_exp,min,Bounded_ini,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	Lin_exp\=[]+_,
	get_enriched_loop(Loop,Head,Call,Cs),
	%obtain an expressions only in terms of the initial variables of the loop
	(is_head_expression(Head,Lin_exp)->
		Exp=Lin_exp
	;
	 Head=..[_|Vars_head],
	 max_min_linear_expression_all(Lin_exp, Vars_head, Cs,min, Mins),
	 member(Exp,Mins)
	),
	%the cost is increased or decreased by a constant
	get_difference_version(Head,Call,Exp,Exp_diff),	
	le_print_int(Exp_diff,Exp_diff_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_int=Exp_diff_denominator*D|Cs],[D],[Delta]),
	%a flag that indicates whether the cost increases or decreases
	(
	(greater_fr(Delta,0),Dir=pos)
	;
	(greater_fr(0,Delta),Dir=neg)
	),	
	%check the effect of other loops, 
	delete(Phase,Loop,Phase_rest),
	check_loops_triangle_minsum(Phase_rest,Dir,Head,Call,Pending,Exp,Included_loops,Bounded,Increments,Other_loops,Pending_aux),
	append(Bounded_ini,Bounded,Bounded_vars),
	% generate an intermediate constraint that is the sum of all the iterations of the Included_loops
	get_it_sum_aux([Loop|Included_loops],Aux_all_iter_iconstr,All_iterations_name),
	%obtain the minimum initial value of the expression taking the Other_loops into account
	new_itvar(Initial_name),
	compute_max_min(Head,Call,Other_loops,Exp,min,[Initial_name],New_fconstrs1,New_iconstrs1,Pending_aux,Pending_aux1),
	max_frl([Delta|Increments],Min_increment),
	%depending on whether we increment or decrement
	(Dir=pos->
		multiply_fr(Min_increment,1/2,Min_increment_scaled),
		New_fconstrs2=[],
	    New_iconstrs2=[],
	    Pending_aux1=Pending_out,
	    % we substract the decrements
	    astrexp_new(add([mult([All_iterations_name,Initial_name]),mult([All_iterations_name,Min_increment_scaled])])-add([mult([All_iterations_name,All_iterations_name,Min_increment_scaled])]),Astrexp)
	;
		multiply_fr(Min_increment,-1/2,Min_increment_scaled),
		negate_le(Exp,Exp_neg),
		new_itvar(Initial_name_neg),
		%we add the increments, but we substract the negation of the initial value in case this one is negative	
		compute_max_min(Head,Call,Other_loops,Exp_neg,max,[Initial_name_neg],New_fconstrs2,New_iconstrs2,Pending_aux1,Pending_out),
		astrexp_new(add([mult([All_iterations_name,Initial_name]),mult([All_iterations_name,All_iterations_name,Min_increment_scaled])])-add([mult([Initial_name_neg,All_iterations_name]),mult([All_iterations_name,Min_increment_scaled])]),Astrexp)
	),
	iconstr_new(Astrexp,lb,Bounded_vars,Main_iconstr),
	ut_flat_list([New_fconstrs1,New_fconstrs2],New_fconstrs),!,
	ut_flat_list([New_iconstrs1,New_iconstrs2,Aux_all_iter_iconstr,Main_iconstr],New_iconstrs),!,
	save_sum_found(Head,Call,Loop,Lin_exp,min,Bounded_ini,New_fconstrs,New_iconstrs).	
	

%Inductive strategy
compute_sum(Head,Call,Phase,Loop,Lin_exp,Max_min,Bounded,New_fconstrs,New_iconstrs2,Pending,Pending_out):-
	Lin_exp\=[]+_,
	
	generate_lecandidates(Head,Call,Lin_exp,Max_min,Loop,Exp_list),
	(Max_min=max->
	maplist(check_loops_maxsum(Head,Call,Phase,Loop,Bounded,Pending),Exp_list,New_fconstrs_list,New_iconstrs_list,Pending_out_list)
	;
	maplist(check_loops_minsum(Head,Call,Phase,Loop,Bounded,Pending),Exp_list,New_fconstrs_list,New_iconstrs_list,Pending_out_list)
	),
	ut_flat_list(New_fconstrs_list,New_fconstrs),
	%we stay with this option as long as one attempt succeeded 
	%otherwise go to simple multiplication
	New_fconstrs\=[],
	ut_flat_list(New_iconstrs_list,New_iconstrs),
	empty_pending(Empty_pending),
	foldl(union_pending,Pending_out_list,Empty_pending,Pending_aux),
	% this is an heuristic
	% if we are computing a minsum or we have created some intermediate constraints, we apply the basic product strategy as well
	((New_iconstrs\=[];Exp_list=[_]; Max_min=min)->
	basic_product(Head,Call,Loop,Lin_exp,Bounded,Iconstr_extra,Max_min,Pending_aux,Pending_out),
	New_iconstrs2=[Iconstr_extra|New_iconstrs]
	;
	Pending_aux=Pending_out,
	New_iconstrs2=New_iconstrs
	),
	save_sum_found(Head,Call,Loop,Lin_exp,Max_min,Bounded,New_fconstrs,New_iconstrs2).


%Basic Product strategy
compute_sum(Head,Call,_Phase,Loop,Lin_exp,Max_min,Bounded,[],[Iconstr],Pending,Pending_out):-
	Lin_exp\=[]+1,!,
	basic_product(Head,Call,Loop,Lin_exp,Bounded,Iconstr,Max_min,Pending,Pending_out),
	save_sum_found(Head,Call,Loop,Lin_exp,Max_min,Bounded,[],[Iconstr]).
	
compute_sum(_Head,_Call,_Phase,_Loop,_,_Max_min,_Bounded,[],[],Pending,Pending).	

%! get_it_sum_aux(+Involved_loops:list(loop_id),-Iconstrs:list(iconstr),-All_iterations_var:itvar) is det
% create new intermediate variable All_iterations_var and two intermediate constraints Iconstrs that
% bound it to the sum of number of iterations of Involved_loops
get_it_sum_aux(Involved_loops,Iconstrs,All_iterations_var):-
	maplist(get_loop_itvar,Involved_loops,Involved_it_vars),
	maplist(put_inside_mult,Involved_it_vars,It_summands),
	astrexp_new(add(It_summands)-add([]),Astrexp),
	new_itvar(All_iterations_var),	
	copy_term(Astrexp,Astrexp2),
	iconstr_new(Astrexp,lb,[All_iterations_var],Lb_iconstr),
	iconstr_new(Astrexp2,ub,[All_iterations_var],Ub_iconstr),
	Iconstrs=[Lb_iconstr,Ub_iconstr].
	
%! check_loops_triangle_minsum(Loops:loop_id,Pos_neg:flag,Head:term,Call:term,Pending:pending_constrs,Exp:nlinexp,Included_loops:list(loop_id),Bounded:list(itvar),Increments:list(rational),Other_loops:list(loop_id),Pending_out:pending_constr) is det
% examine the behavior of Loops with respecto to Exp
% * Included_loops are a list of  loops that are included
% * Bounded are a list of itvars that are bounded by the expression Exp
% * Increments is list of how much Exp is incremented or decremented in the included loops
% * Other_loops list of loops that are not included
% For each included loop we remove a pending constraint, Pending_sum is the resulting pending constraints
%
% We include loops that increment or decrement Exp by a constant and contain a pending constraint bounded by Exp
% we put the rest of the loops in Other_loops
check_loops_triangle_minsum([],_Pos_neg,_Head,_Call,Pending,_Exp,[],[],[],[],Pending).
check_loops_triangle_minsum([Loop|Loops],Pos_neg,Head,Call,Pending,Exp,[Loop|Included_loops],Bounded_total,[Increment|Increments],Other_loops,Pending_out):-
	check_loop_triangle_minsum(Loop,Pos_neg,Head,Call,Pending,Exp,Bounded,Increment,Pending_aux),!,
	check_loops_triangle_minsum(Loops,Pos_neg,Head,Call,Pending_aux,Exp,Included_loops,Bounded_aux,Increments,Other_loops,Pending_out),
	append(Bounded,Bounded_aux,Bounded_total).
	
check_loops_triangle_minsum([Loop|Loops],Pos_neg,Head,Call,Pending,Exp,Included_loops,Bounded_total,Increments,[Loop|Other_loops],Pending_out):-
	check_loops_triangle_minsum(Loops,Pos_neg,Head,Call,Pending,Exp,Included_loops,Bounded_total,Increments,Other_loops,Pending_out).
	
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
	find_minsum_constraint(Loop,Head,Call,Cs,Exp,Bounded,Pending,Pending1),!,
	(get_param(debug,[])->format('Loop ~p is triangle collaborative with ~p ~n',[Loop,Delta]);true).
	


% check_loops_maxsum(Head:term,Call:term,Phase:phase,Loop:loop_id,Bounded_ini:list(itvar),Pending:pending_constrs,Exp:nlinexp,Fconstrs:list(fconstr),Iconstrs:list(iconstr),Pending_out:pending_constrs) is semidet
% check the effect of the loops of Phase on the candidate Exp and generate the corresponding constraints Fconstrs and Iconstrs
check_loops_maxsum(Head,Call,Phase,Loop,Bounded_ini,Pending,Exp,Fconstrs,Iconstrs,Pending_out):-
	(get_param(debug,[])->print_lin_exp_in_phase(Head,Call,Exp);true),
	%distinguish head and head-tail candidates with a flag
	(is_head_expression(Head,Exp)->
			get_difference_version(Head,Call,Exp,Exp_diff),
			Flag=head(Exp)
			;
			Flag=diff,
			Exp=Exp_diff
	),
	check_loops_maxsum_1(Phase,Loop,Head,Call,Exp_diff,Flag,Pstrexp_pair,Bounded,Pending,Pending_out),!,
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
check_loops_maxsum(_Head,_Call,_Phase,_Loop,_Bounded,_Pending,_Exp,[],[],Empty_pending):-
	empty_pending(Empty_pending).

% check_loops_minsum(Head:term,Call:term,Phase:phase,Loop:loop_id,Bounded_ini:list(itvar),Pending:pending_constrs,Exp:nlinexp,Fconstrs:list(fconstr),Iconstrs:list(iconstr),Pending_out:pending_constrs) is semidet
% check the effect of the loops of Phase on the candidate Exp and generate the corresponding constraints Fconstrs and Iconstrs
check_loops_minsum(Head,Call,Phase,Loop,Bounded_ini,Pending,Exp,Fconstrs,Iconstrs,Pending_out):-
	(get_param(debug,[])->print_lin_exp_in_phase(Head,Call,Exp);true),
	check_loops_minsum_1(Phase,Loop,Head,Call,Exp,Pstrexp_pair,Bounded,Pending,Pending_out),!,
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
check_loops_minsum(_Head,_Call,_Phase,_Loop,_Bounded,_Pending,_Exp,[],[],Empty_pending):-
	empty_pending(Empty_pending).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
check_loops_maxsum_1([],_,_,_,_,_Flag,Empty_pstrexp_pair,[],Pending,Pending):-
   pstrexp_pair_empty(Empty_pstrexp_pair).
%ignore the loop that we started from	
check_loops_maxsum_1([Loop|Loops],Loop,Head,Call,Exp,Flag,Pstrexp_pair,Bounded,Pending,Pending_out):-!,
	check_loops_maxsum_1(Loops,Loop,Head,Call,Exp,Flag,Pstrexp_pair,Bounded,Pending,Pending_out).
		
check_loops_maxsum_1([Loop2|Loops],Loop,Head,Call,Exp_diff,Flag,Pstrexp_pair,Bounded,Pending,Pending_out):-	
	check_loop_maxsum(Head,Call,Exp_diff,Flag,Loop2,Pstrexp1_pair,Bounded1,Pending,Pending1),!,
	check_loops_maxsum_1(Loops,Loop,Head,Call,Exp_diff,Flag,Pstrexp2_pair,Bounded2,Pending1,Pending_out),
	pstrexp_pair_add(Pstrexp1_pair,Pstrexp2_pair,Pstrexp_pair),
	append(Bounded1,Bounded2,Bounded).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_loops_minsum_1([],_,_,_,_,Empty_pstrexp_pair,[],Pending,Pending):-
	pstrexp_pair_empty(Empty_pstrexp_pair).
%ignore the loop that we started from	
check_loops_minsum_1([Loop|Loops],Loop,Head,Call,Exp,Pstrexp_pair,Bounded,Pending,Pending_out):-!,
		check_loops_minsum_1(Loops,Loop,Head,Call,Exp,Pstrexp_pair,Bounded,Pending,Pending_out).
		
check_loops_minsum_1([Loop2|Loops],Loop,Head,Call,Exp_diff,Pstrexp_pair,Bounded,Pending,Pending_out):-	
		check_loop_minsum(Head,Call,Exp_diff,Loop2,Pstrexp_pair1,Bounded1,Pending,Pending1),!,
		check_loops_minsum_1(Loops,Loop,Head,Call,Exp_diff,Pstrexp_pair2,Bounded2,Pending1,Pending_out),
		pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair),
		append(Bounded1,Bounded2,Bounded).




%! check_loop_maxsum(Head:term,Call:term,Exp_diff:nlinexp,Flag:term,Loop:loop_id,Pstrexp_pair:pstrexp_pair,Bounded:list(itvar),Pending:pending_constrs,Pending1:pending_constrs)
% check the effect of Loop on Exp_diff, Flag indicates if the original candidate was head or head-tail
% * this can modify the pending constraints Pending->Pending1
% * generates a Pstrexp_pair with the elements that have to be added to the constraint
% * sometimes we can bound some itvar from Loop, those are in Bounded
check_loop_maxsum(Head,Call,Exp_diff,Flag,Loop,Pstrexp_pair,Bounded,Pending,Pending1):-
	get_enriched_loop(Loop,Head,Call,Cs),
	term_variables((Head,Call),Vars),	
	le_print_int(Exp_diff,Exp_diff_print_int,_),
	negate_le(Exp_diff,Exp_diff_neg),
	le_print_int(Exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
%if Exp does not increase
	(nad_entails(Vars,Cs,[Exp_diff_print_int>=0])->
	 %find a collaborative loop
	    (find_maxsum_constraint(Loop,Head,Call,Cs,Exp_diff,Flag,Bounded,Pending,Pending1)->			
		   true
		   ;
			Pending1=Pending,
			Bounded=[]
		),
		pstrexp_pair_empty(Pstrexp_pair),
		(get_param(debug,[])->format('Loop ~p is collaborative~n',[Loop]);true)
	;
	 Bounded=[],
%if add a constant	
	(nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta])->
		get_loop_itvar(Loop,Loop_name),
		Pstrexp_pair=add([mult([Loop_name,Delta])])-add([]),
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
				save_pending_list(maxsum,Loop,Maxsums,Pending,Pending1),
				(get_param(debug,[])->format('Loop ~p adds an expression ~p~n',[Loop,Max_increments]);true)
			    ;
%reset			    
			    Flag=head(Exp),
				copy_term((Head,Exp),(Call,Exp_end)),
				max_min_linear_expression_all(Exp_end, Vars_head, Cs,max, Max_resets),
				Max_resets\=[],
				
   				new_itvar(Aux_itvar),
   				Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
				maplist(fconstr_new([Aux_itvar],ub),Max_resets,Maxsums),
				save_pending_list(maxsum,Loop,Maxsums,Pending,Pending1),
				(get_param(debug,[])->format('Loop ~p has a reset to  ~p~n',[Loop,Max_resets]);true)
		)
	)
	).

check_loop_maxsum(_Head,_Call,_Exp_diff,_,Loop,[],[],_Pending,_Pending1):-	
	    (get_param(debug,[])->format('Loop ~p has undefined behavior ~n',[Loop]);true),
		fail.	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! check_loop_minsum(Head:term,Call:term,Exp_diff:nlinexp,Loop:loop_id,Pstrexp_pair:pstrexp_pair,Bounded:list(itvar),Pending:pending_constrs,Pending1:pending_constrs)
% similar to check_loop_maxsum but checking the different possibilities in opposite order
% for minsum there are only head-tail candidates
check_loop_minsum(Head,Call,Exp_diff,Loop,Pstrexp_pair,[],Pending,Pending1):-	
	get_enriched_loop(Loop,Head,Call,Cs),
	term_variables((Head,Call),Vars),
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
		save_pending_list(minsum,Loop,Maxsums,Pending,Pending1),
		(get_param(debug,[])->format('Loop ~p adds an expression ~p~n',[Loop,Max_increments]);true)
	).

%collaborative loop	with constraint
check_loop_minsum(Head,Call,Exp_diff,Loop,Pstrexp_pair,Bounded,Pending,Pending1):-
		get_enriched_loop(Loop,Head,Call,Cs),
		pstrexp_pair_empty(Pstrexp_pair),
		find_minsum_constraint(Loop,Head,Call,Cs,Exp_diff,Bounded,Pending,Pending1),!,
		(get_param(debug,[])->format('Loop ~p is collaborative with a constraint~n',[Loop]);true).
% we don't substract loops that can decrease the bound
% in theory this could happen, in practice it doesn't seem to happen so we skip it and fail in those cases		
	
check_loop_minsum(_Head,_Call,_Exp_diff,Loop,_,_,_Pending,_):-	
	    (get_param(debug,[])->format('Loop ~p has undefined behavior ~n',[Loop]);true),
		fail.	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_max_min(Head:term,Call:term,Phase:phase,Lin_exp:nlinexp,Max_min:flag,Bounded:list(itvar),New_fconstrs:list(fconstr),New_iconstrs:list(iconstr),Pending:pending_constrs,Pending:pending_constrs)
% Compute the maximum or minimum value of Lin_exp in any iteration of the loops of Phase
% this computation is recorded with a set on new final and intermediate constraints
%
% * first try to find a similar linear expression whose maximum/minimum has already been computed (cacheing)
% * if not, try using transitive invariants (we have them precomputed)
% * finally, try the incremental approach 
compute_max_min(Head,Call,Phase,Lin_exp,Max_min,Bounded,New_fconstrs,New_iconstrs,Pending,Pending):-
	max_min_found(Head,Call,Phase,(Lin_exp_normalized2,Coeff2,Constant2),Max_min,Res),
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
	).

% a constant does not need to be maximized/minimized
compute_max_min(_Head,_Call,_Phase,[]+C,Max_min,Bounded,New_fconstrs,[],Pending,Pending):-!,
	get_constr_op(Max_min,Op),
	maplist(fconstr_new(Bounded,Op),[[]+C],New_fconstrs).
	
%use transitive invariant
compute_max_min(Head,Call,Phase,Lin_exp,Max_min,Bounded,New_fconstrs,[],Pending,Pending):-
	get_constr_op(Max_min,Op),
	max_min_top_expression_in_phase(Head,Call,Phase,bound(Op,Lin_exp,Bounded),Maxs_out),
	maplist(fconstr_new(Bounded,Op),Maxs_out,New_fconstrs),
	New_fconstrs\=[],!,
	save_max_min_found(Head,Call,Phase,Lin_exp,Max_min,final(Maxs_out)).


%use  increments and resets procedure	
compute_max_min(Head,Call,Phase,Lin_exp,Max_min,Bounded,[Fconstr],[Iconstr],Pending,Pending_out):-
	get_constr_op(Max_min,Op),
	%we have to consider the case where the value is not reseted
	new_itvar(Aux_itvar),
	fconstr_new([Aux_itvar],Op,Lin_exp,Fconstr),
	% check the effect of the loops
	(Max_min=max->
	check_loops_max(Phase,Head,Call,Lin_exp,Resets,Pstrexp_pair2,Pending,Pending_out),
	(Resets=[] ->
	   Max_resets=Aux_itvar
	   ;
	   Max_resets=max([Aux_itvar|Resets])
	   ),
	Pstrexp_pair1=add([mult([Max_resets])])-add([])
	;
	check_loops_min(Phase,Head,Call,Lin_exp,Resets,Pstrexp_pair2,Pending,Pending_out),
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
    save_max_min_found(Head,Call,Phase,Lin_exp,Max_min,inter(Astrexp)).

    
%failed    
compute_max_min(Head,Call,Phase,Lin_exp,Max_min,_Bounded,[],[],Pending,Pending):-
	save_max_min_found(Head,Call,Phase,Lin_exp,Max_min,none).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%			


check_loops_max([],_Head,_Call,_Lin_exp,[],Empty_pstrexp_pair,Pending,Pending):-
	pstrexp_pair_empty(Empty_pstrexp_pair).
	
check_loops_max([Loop|Loops],Head,Call,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	check_loop_max(Loop,Head,Call,Lin_exp,Resets1,Pstrexp_pair1,Pending,Pending_aux),
	check_loops_max(Loops,Head,Call,Lin_exp,Resets2,Pstrexp_pair2,Pending_aux,Pending_out),
	append(Resets1,Resets2,Resets),
	pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair).

%! check_loops_max(Loop:loop_id,Head:term,Call:term,Lin_exp:alinexp,Resets:list(itvar),Pstrexp_pair:pstrexp_pair,Pending:pending_constrs,Pending_out:pending_constrs)
% check the different possible behaviors of Loop with respect to Lin_exp
% * the loop does not increase Lin_exp: do nothing
% * the loop increases Lin_exp by a constant Delta: add maxsum(Loop,Delta) to the cost (in Pstrexp)
% * the loop increases Lin_exp by a linear expression Max_increment: add maxsum(Loop,Max_increment) to the cost
% * the loop resets Lin_exp to Max_resets: add Max_resets to the resets
check_loop_max(Loop,Head,Call,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	get_enriched_loop(Loop,Head,Call,Cs),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	le_print_int(Lin_exp_diff,Exp_diff_int,_),
	negate_le(Lin_exp_diff,Lin_exp_diff_neg),
	le_print_int(Lin_exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
	term_variables((Head,Call),Vars),
% the lin_exp does not increase
	(nad_entails(Vars,Cs,[Exp_diff_int>=0])->
		Resets=[],
		pstrexp_pair_empty(Pstrexp_pair),
		Pending_out=Pending
		;
% add a constant
		((nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta]),greater_fr(Delta,0))->
			get_loop_itvar(Loop,Loop_name),
			Pstrexp_pair=add([mult([Loop_name,Delta])])-add([]),
			Resets=[],
			Pending_out=Pending
		;
			term_variables(Head,Vars_head),
			select_important_variables(Vars,Lin_exp,Vars_of_Interest),
			max_min_linear_expression_all(Lin_exp_diff_neg, Vars_of_Interest, Cs,max, Max_increments),
%add an expression		
			(Max_increments\=[]->
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				save_pending_list(maxsum,Loop,Maxsums,Pending,Pending_out),
				Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
				Resets=[]
			;
%reset		
				copy_term((Head,Lin_exp),(Call,Lin_exp_p)),
				max_min_linear_expression_all(Lin_exp_p, Vars_head, Cs,max, Maxs_resets),
				Maxs_resets\=[],!,
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Maxs_resets,Maxtops),
				save_pending_list(max,Loop,Maxtops,Pending,Pending_out),
				pstrexp_pair_empty(Pstrexp_pair),
				Resets=[Aux_itvar]
			)
		)
	).
				
				
				
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_loops_min([],_Head,_Call,_Lin_exp,[],Empty_pstrexp_pair,Pending,Pending):-
	pstrexp_pair_empty(Empty_pstrexp_pair).
	
check_loops_min([Loop|Loops],Head,Call,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	check_loop_min(Loop,Head,Call,Lin_exp,Resets1,Pstrexp_pair1,Pending,Pending_aux),
	check_loops_min(Loops,Head,Call,Lin_exp,Resets2,Pstrexp_pair2,Pending_aux,Pending_out),
	append(Resets1,Resets2,Resets),
	pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair).

%! check_loop_min(Loop:loop_id,Head:term,Call:term,Lin_exp:alinexp,Resets:list(itvar),Pstrexp_pair:pstrexp_pair,Pending:pending_constrs,Pending_out:pending_constrs)
% check the different possible behaviors of Loop with respect to Lin_exp
% similar to check_loops_max
check_loop_min(Loop,Head,Call,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	get_enriched_loop(Loop,Head,Call,Cs),
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
				save_pending_list(maxsum,Loop,Maxsums,Pending,Pending_out),
				Pstrexp_pair=add([])-add([mult([Aux_itvar])]),
				Resets=[]
			;
%reset		
				copy_term((Head,Lin_exp),(Call,Lin_exp_p)),
				max_min_linear_expression_all(Lin_exp_p, Vars_head, Cs,min, Mins_resets),
				Mins_resets\=[],!,
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],lb),Mins_resets,Maxtops),
				save_pending_list(max,Loop,Maxtops,Pending,Pending_out),
				pstrexp_pair_empty(Pstrexp_pair),
				Resets=[Aux_itvar]
			)
		)
	).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! basic_product(Head,Call,Loop,Lin_exp,Bounded,Aux_exp,Max_min,Pending,Pending_out)
% Implement the basic product strategy:
% maxsum(A)=< maxsum(1)*max(A)
% minsum(A)=< minsum(1)*min(A)
basic_product(Head,Call,Loop,Lin_exp,Bounded,Aux_exp,Max_min,Pending,Pending_out):-	
	get_constr_op(Max_min,Op),
	get_enriched_loop(Loop,Head,Call,Cs),
	new_itvar(Aux_itvar),
	get_loop_itvar(Loop,Loop_itvar),
	astrexp_new(add([mult([Loop_itvar,Aux_itvar])])-add([]),Astrexp),
	(is_head_expression(Head,Lin_exp)->
		fconstr_new([Aux_itvar],Op,Lin_exp,Fconstr),
		Max_fconstrs=[Fconstr]
	;
	 Head=..[_|Vars_head],
	 max_min_linear_expression_all(Lin_exp, Vars_head, Cs,Max_min, Maxs_exps),
	 maplist(fconstr_new([Aux_itvar],Op),Maxs_exps,Max_fconstrs)
	 ),
	save_pending_list(Max_min,Loop,Max_fconstrs,Pending,Pending_out),
    Aux_exp=bound(Op,Astrexp,Bounded).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% auxiliary predicates for maxsum and minsum

%! find_maxsum_constraint(Loop:loop_id,Head:term,Call:term,Cs:polyhedron,Exp_diff:nlinexp,Flag:flag,Bounded:list(itvar),Pending:pending_constrs,Pending_out:pending_constrs)
% try to find a pending maxsum that can be bounded by Exp_diff
% we check that Exp_diff>= Exp2 and in case we are dealing with a head candidate
% we also check Exp_original>=Exp2
find_maxsum_constraint(Loop,Head,Call,Cs,Exp_diff,Flag,Bounded,Pending,Pending_out):-
		extract_pending(Loop,maxsum,Pending,(_Depth,Exp2,Bounded),Pending_out),
		term_variables((Head,Call),Vars),
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
		
%! find_minsum_constraint(Loop:loop_id,Head:term,Call:term,Cs:polyhedron,Exp_diff:nlinexp,Flag:flag,Bounded:list(itvar),Pending:pending_constrs,Pending_out:pending_constrs)
% try to find a pending minsum that can be bounded by Exp_diff
% we check that Exp_diff=< Exp2 	
find_minsum_constraint(Loop,Head,Call,Cs,Exp_diff,Bounded,Pending,Pending):-
		extract_pending(Loop,minsum,Pending,(_Depth,Exp2,Bounded),_Pending_out),
		term_variables((Head,Call),Vars),
		subtract_le(Exp2,Exp_diff,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),!.	
%! get_ranking_functions_constraints(Max:int,Head:term,Call:term,Phase:phase,Chain:chain,Fconstrs:list(fconstr))
% generate at most Max upper bound final constraints from the ranking functions
% -the ranking function itself
% -the difference between the ranking function at the beginning and at the end of the phase
get_ranking_functions_constraints(Max,Head,Call,Phase,Chain,Fconstrs):-
	bagof_no_fail(Rf,
		ranking_function(Head,Chain,Phase,Rf)
	  ,Rfs),
	ut_split_at_pos(Rfs,Max,Rfs_selected,_),
	maplist(get_difference_version(Head,Call),Rfs_selected,Rfs_diff),
	maplist(get_loop_itvar,Phase,Bounded),
	append(Rfs_selected,Rfs_diff,Rfs_total),
	maplist(fconstr_new(Bounded,ub),Rfs_total,Fconstrs).
	
%! get_ranking_functions_lower_constraints(Max:int,Head:term,Call:term,Phase:phase,Chain:chain,Fconstrs:list(fconstr))
% generate at most Max lower bound final constraints from the ranking functions
% -the difference between the initial and the final value of the rf divided by the maximum decrease
% per iteration is a good lb candidate 
get_ranking_functions_lower_constraints(Max,Head,Call,Phase,Chain,Fconstrs):-
	bagof_no_fail(Df,
		get_lower_bound_val(Head,Call,Chain,Phase,Df)
	,Dfs),
	ut_split_at_pos(Dfs,Max,Dfs_selected,_),
	maplist(get_loop_itvar,Phase,Bounded),
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
	
get_partial_lower_bound(Head,Call,Chain,Loop,Lb):-
	partial_ranking_function(Head,Chain,_Phase,Loops,Rf,_,_),
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
	
%! 	generate_lecandidates(Head:term,Call:term,Lin_exp:nlinexp,Max_min:flag,Loop:loop_id,Total_exps:list(nlinexp))
% generate linear expressions that are candidates to represent the
% sum of all the instances of Lin_exp in Loop 
%
% use Farkas lemma
generate_lecandidates(Head,Call,Lin_exp,max,Loop,Total_exps):-
	get_enriched_loop(Loop,Head,Call,Cs),	
	rf_limit(Max_candidates),
	difference_constraint_farkas_ub(Head,Call,Cs,Lin_exp,Diff_list,Diff_list2),
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_),
	ut_split_at_pos(Diff_list2,Max_candidates,Diff_list_selected2,_),
	append(Diff_list_selected,Diff_list_selected2,Total_exps).
	
	
generate_lecandidates(Head,Call,Lin_exp,min,Loop,Diff_list_selected):-
	get_enriched_loop(Loop,Head,Call,Cs),	
	rf_limit(Max_candidates),
	difference_constraint_farkas_lb(Head,Call,Cs,Lin_exp,Diff_list),
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_).	

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! max_min_top_expression_in_phase(Head:term,Call:term,Phase:phase,bound(Op,Lin_exp,_Bounded),Maxs_out)
% auxiliary predicate for computing max and min of a linexp using the transitive invariant
max_min_top_expression_in_phase(Head,Call,Phase,bound(Op,Lin_exp,_Bounded),Maxs_out):-
	get_constr_op(Max_min,Op),
	phase_transitive_closure(Phase,_,Head_total,Head,Cs_star_trans),
	phase_loop(Phase,_,Head,Call,Cs),
	ut_flat_list([Cs_star_trans,Cs],Context),
	term_variables(Head_total,Vars_of_Interest),
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,Max_min, Maxs_out),
	Head_total=Head.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicates for storing results that have already been computed

%! save_sum_found(Head:term,Call:term,Loop:loop_id,Lin_exp:alinexp,Max_min:flag,Bounded:list(itvar),Fconstrs:list(fconstr),Iconstrs:list(iconstr))
% Store the costraints resulting from the computation of "Maxmin"sum(Lin_exp)
% We take only the constraints that contain Bounded and substitute the set Bounded by a variable Var so it
% can be later unified with an itvar
%
% we normalize the linear expression so any multiple of the original constraint 
% can reuse the stored result
save_sum_found(Head,Call,Loop,Lin_exp,Max_min,Bounded,Fconstrs,Iconstrs):-
	from_list_sl(Bounded,Bounded_set),
	substitute_bounded_by_var(Iconstrs,Bounded_set,Var,Iconstrs1),
	substitute_bounded_by_var(Fconstrs,Bounded_set,Var,Fconstrs1),
	semi_normalize_le(Lin_exp,Coeff,Lin_exp_normalized),
	ground_copy((Head,Call,Lin_exp_normalized),(_,_,Lin_exp_norm_ground)),
	assert(sum_found(Loop,Lin_exp_norm_ground,Max_min,Head,Call,Coeff,Var,Fconstrs1,Iconstrs1)).

%! save_max_min_found(Head:term,Call:term,Phase:phase,Lin_exp:alinexp,Max_min:flag,Exp:final_inter_none)
% final_inter_none:= final(list(alinexp)) | inter(astrexp) | none
% Store the value Exp from the maximization/minimization of a linear expression Lin_exp
% we normalize the linear expression to be able to reuse the result in more cases:
% any multiple plus any constant
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
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicates to handle the pending_constrs data structure

empty_pending(pending([],[],[],[])).

%! save_pending_list(Type:flag,Loop:loop_id,Fconstrs:list(fconstr),Pending:pending_constrs,Pending_out:pending_constrs)
% add the final constraints Fconstrs to the pending constrs Pending
% They are added with Depth+1 where Depth is the current Depth
% If Depth is above the limit, the constraints are not added and will be ignored
% Type in {max, min, maxsum, minsum}
save_pending_list(Type,Loop,Fconstrs,Pending,Pending_out):-
	current_pending_depth(Depth),
	max_pending_depth(Max_depth),Depth<Max_depth,!,
	Depth_new is Depth+1,
	foldl(save_pending(Type,Loop,Depth_new),Fconstrs,Pending,Pending_out).
save_pending_list(_Type,_Loop,_Fconstrs,Pending,Pending).

%!union_pending(Pending1:pending_constrs,Pending2:pending_constrs,Pending3:pending_constrs)
% join Pending1 and Pending2 into Pending3
union_pending(pending(Maxs1,Mins1,Maxsums1,Minsums1),pending(Maxs2,Mins2,Maxsums2,Minsums2),pending(Maxs3,Mins3,Maxsums3,Minsums3)):-
	union_sl(Maxs1,Maxs2,Maxs3),
	union_sl(Mins1,Mins2,Mins3),
	join_mm(Maxsums1,Maxsums2,Maxsums3),
	join_mm(Minsums1,Minsums2,Minsums3).
	
%! save_pending(Type:flag,Loop:loop_id,Depth:int,Fconstr:fconstr,Pending:pending_constrs,Pending_out:pending_constrs)
% add Fconstr to Pending with flag Type, Loop and Depth
save_pending(max,_,Depth,bound(ub,Lin_exp,Bounded),Pending,Pending_out):-
	Pending=pending(Maxs,Mins,Maxsums,Minsums),
	insert_sl(Maxs,(Depth,Lin_exp,Bounded),Maxs1),
	Pending_out=pending(Maxs1,Mins,Maxsums,Minsums).
save_pending(min,_,Depth,bound(lb,Lin_exp,Bounded),Pending,Pending_out):-
	Pending=pending(Maxs,Mins,Maxsums,Minsums),
	insert_sl(Mins,(Depth,Lin_exp,Bounded),Mins1),
	Pending_out=pending(Maxs,Mins1,Maxsums,Minsums).	

save_pending(maxsum,Loop,Depth,bound(ub,Lin_exp,Bounded),Pending,Pending_out):-
	Pending=pending(Maxs,Mins,Maxsums,Minsums),
	(lookup_lm(Maxsums,Loop,Maxsum_set)->
		true
		;
		empty_sl(Maxsum_set)
	),	
	insert_sl(Maxsum_set,(Depth,Lin_exp,Bounded),Maxsum_set1),
	insert_lm(Maxsums,Loop,Maxsum_set1,Maxsums1),
	Pending_out=pending(Maxs,Mins,Maxsums1,Minsums).	

save_pending(minsum,Loop,Depth,bound(lb,Lin_exp,Bounded),Pending,Pending_out):-
	Pending=pending(Maxs,Mins,Maxsums,Minsums),
	(lookup_lm(Minsums,Loop,Minsum_set)->
		true
		;
		empty_sl(Minsum_set)
	),	
	insert_sl(Minsum_set,(Depth,Lin_exp,Bounded),Minsum_set1),
	insert_lm(Minsums,Loop,Minsum_set1,Minsums1),
	Pending_out=pending(Maxs,Mins,Maxsums,Minsums1).

%! get_one_pending(Pending:pending_constrs,Type:term,Elem:(int,nlinexp,list(itvar)),Pending_out:pending_constrs) is semidet
% get one pending constraint from Pending
% it fails if Pending is empty
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

% Similar to the previous predicate but specifying the Loop and whether it is maxsum or minsum that
% we want to obtain
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

			
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% general auxiliary predicates

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
get_constr_op(max,ub).
get_constr_op(min,lb).	

select_important_variables(Vars_head,Lin_exp,Vars_of_Interest):-
	from_list_sl(Vars_head,Vars_head_set),
	term_variables(Lin_exp,Vars_exp),
	from_list_sl(Vars_exp,Vars_exp_set),
	difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest).
	
put_inside_mult(Factor,mult([Factor])).


get_enriched_loop(Loop,Head,Call,Total_cs):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),	
	forward_invariant_temp(Head,Call,Forward_inv),
	append(Forward_inv,Cs,Total_cs).
				
is_head_expression(Head,Exp):-
	copy_term((Head,Exp),(Head2,Exp2)),
	numbervars(Head2,0,_),
	ground(Exp2).
	
% debugging predicates 
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

print_pending_elem((_,Lin_exp,Bounded)):-
	write_le(Lin_exp,Lin_exp_print),
	format('~p  ~p ~n',[Lin_exp_print,Bounded]).
print_pending_elems_loop((Loop,Elems)):-
	format('Loop:~p ~n',[Loop]),
	maplist(print_pending_elem,Elems).