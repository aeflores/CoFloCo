/** <module> phase_max_min_strategy

This module implements the max_min_strategy. This strategy obtains the maximum or minimum value
of a linear expression in a phase. It does so by checking whether the expression is incremented,
decremented or reset.
The constraint generated is:

For the maximum case: the maximum of all the resets and the expression plus the sum of all the increments
For the minimim case: the minimum of all the resets and the expression minus the sum of all the decrements

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
:- module(phase_max_min_strategy,[
		max_min_strategy/8
	]).
	
:- use_module(phase_common).
:- use_module(phase_solver,[
	state_save_pending_list/7,
	state_get_property/3,
	state_save_new_fconstrs/4,
	state_save_new_iconstrs/3
	]).
:- use_module('../../refinement/loops',[
	loop_ioVars/2
	]).		
:- use_module('../../refinement/chains',[
	phase_get_phase_loop/2,
	phase_get_transitive_closure/2
	]).				        
	        
:- use_module('../constraints_maximization',[max_min_linear_expression_all/5]).		
:- use_module('../../IO/params',[get_param/2]).			
:- use_module('../../IO/output',[
	write_lin_exp_in_phase/3,
	print_or_log/2
	]).				
:- use_module('../../utils/cofloco_utils',[ground_copy/2]).	
:- use_module('../../utils/cost_structures',[
	new_itvar/1,
	get_loop_itvar/2,
	astrexp_new/2,
	pstrexp_pair_empty/1,
	pstrexp_pair_add/3,
	fconstr_new/4,
	iconstr_new/4
	]).	
:- use_module('../../utils/template_inference',[max_min_linear_expression_list_all/6]).									
:- use_module(stdlib(numeric_abstract_domains),[
	nad_maximize/3,
	nad_entails/3
	]).		
:- use_module(stdlib(linear_expression),[negate_le/2]).							
:- use_module(stdlib(fraction),[
	greater_fr/2,
	max_fr/3
	]).
:- use_module(stdlib(list_map),[
	lookup_lm/3
	]).	
:- use_module(stdlib(utils),[ut_flat_list/2]).		
:- use_module(library(apply_macros)).
:- use_module(library(lists)).	
	

max_min_strategy(Constr,Depth,Loop_vars,Loop_id,Phase_loops,State,State2,Changes):-
	Phase_loops=[(_,Loop)|_],
	loop_ioVars(Loop,IOvars),
	generate_max_min_candidate(Constr,Loop_vars,Loop_id,Phase_loops,Candidate),
	(
	%use transitive invariant
	transitive_invariant_strategy(Candidate,Loop_vars,IOvars,State,State2,Changes),
	(get_param(debug,[])->print_or_log('   - Found a solution using transitive invariants ~n',[]);true)
	;
	%use  increments and resets procedure	
	max_min_strategy_aux(Candidate,Depth,Loop_vars,Phase_loops,State,State2,Changes)
	).
		
%use  increments and resets procedure	
max_min_strategy_aux(bound(Op,Lin_exp,Bounded),Depth,Loop_vars,Phase_loops,State,State4,Changes):-
	Loop_vars=loop_vars(Head,_),
	(get_param(debug,[])->print_or_log('   - Applying max/min strategy ~n',[]);true),
	%we have to consider the case where the value is not reseted
	new_itvar(Aux_itvar),
	fconstr_new([Aux_itvar],Op,Lin_exp,Fconstr),
	% check the effect of the loops
	(Op=ub->
		generate_loops_maxmin_classification(Phase_loops,Head,Op,Depth,Lin_exp,Resets,Pstrexp_pair2,State,State2),
		(Resets=[] ->
	   	Max_resets=Aux_itvar
	   	;
	   	Max_resets=max([Aux_itvar|Resets])
	   	),
		Pstrexp_pair1=add([mult([Max_resets])])-add([])
	;
		generate_loops_maxmin_classification(Phase_loops,Head,Op,Depth,Lin_exp,Resets,Pstrexp_pair2,State,State2),	
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
	
	state_save_new_fconstrs(State2,Loop_vars,[Fconstr],State3),
	state_save_new_iconstrs(State3,[Iconstr],State4),
	Changes=[new_fconstrs(Loop_vars,[Fconstr]),new_iconstrs([Iconstr])].
    

generate_max_min_candidate(Constr,loop_vars(Head,Calls),Loop_id,Phase_loops,Candidate):-
	lookup_lm(Phase_loops,Loop_id,Loop),
	Loop=loop(Head,Calls,Cs,_),
	Constr=bound(Op,Lin_exp,Bounded),
	%obtain an expressions only in terms of the initial variables of the loop
	loop_ioVars(Loop,IOvars),
	(is_input_head_expression(Head,IOvars,Lin_exp)->
		Exp=Lin_exp
	;
	 IOvars=ioVars(Head,Input_vars_head,_),
	 (Op=ub->
	 	max_min_linear_expression_all(Lin_exp, Input_vars_head, Cs,max, Exps)
	 	;
	 	max_min_linear_expression_all(Lin_exp, Input_vars_head, Cs,min, Exps)
	 ),
		member(Exp,Exps)
	),
	Candidate=bound(Op,Exp,Bounded).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Transitive invariants
transitive_invariant_strategy(bound(Op,Lin_exp,Bounded),loop_vars(Head,_),IOvars,State,State2,Changes):-
	get_constr_op(Max_min,Op),
	state_get_property(State,phase,Phase),
	phase_get_transitive_closure(Phase,Inv),
	copy_term(Inv,inv(Head_total,Head,Cs_star_trans,_)),
	phase_get_phase_loop(Phase,Phase_loop),
	copy_term(Phase_loop,phase_loop(Head,_,Cs)),
	ut_flat_list([Cs_star_trans,Cs],Context),
	copy_term(IOvars,ioVars(Head_total,Vars_of_Interest,_)),
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,Max_min, Maxs_out),
	Head_total=Head,
	maplist(fconstr_new(Bounded,Op),Maxs_out,New_fconstrs),
	New_fconstrs\=[],!,
	state_save_new_fconstrs(State,loop_vars(Head,[]),New_fconstrs,State2),
	Changes=[new_fconstrs(loop_vars(Head,[]),New_fconstrs)].
	
	    
    
generate_loops_maxmin_classification([],_Head,_Op,_Depth,_Lin_exp,[],Empty_pstrexp_pair,State,State):-
	pstrexp_pair_empty(Empty_pstrexp_pair).

generate_loops_maxmin_classification([(Loop_id,Loop)|Loops],Head,ub,Depth,Lin_exp,Resets,Pstrexp_pair,State,State2):-
	number(Loop_id),!,
	check_loop_max((Loop_id,Loop),Head,Depth,Lin_exp,Resets1,Pstrexp_pair1,State,State_aux),
	generate_loops_maxmin_classification(Loops,Head,ub,Depth,Lin_exp,Resets2,Pstrexp_pair2,State_aux,State2),
	append(Resets1,Resets2,Resets),
	pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair).	

generate_loops_maxmin_classification([(Loop_id,Loop)|Loops],Head,lb,Depth,Lin_exp,Resets,Pstrexp_pair,State,State2):-
	number(Loop_id),!,
	check_loop_min((Loop_id,Loop),Head,Depth,Lin_exp,Resets1,Pstrexp_pair1,State,State_aux),
	generate_loops_maxmin_classification(Loops,Head,lb,Depth,Lin_exp,Resets2,Pstrexp_pair2,State_aux,State2),
	append(Resets1,Resets2,Resets),
	pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair).	
		
generate_loops_maxmin_classification([(Loop_id,_Loop)|Loops],Head,Op,Depth,Lin_exp,Resets,Pstrexp_pair,State,State2):-
	\+number(Loop_id),%it is a chain
	generate_loops_maxmin_classification(Loops,Head,Op,Depth,Lin_exp,Resets,Pstrexp_pair,State,State2).

	
%! generate_loops_maxmin_classification(Loop:loop_id,Head:term,Call:term,Lin_exp:alinexp,Resets:list(itvar),Pstrexp_pair:pstrexp_pair,Pending:pending_constrs,Pending_out:pending_constrs)
% check the different possible behaviors of Loop with respect to Lin_exp
% * the loop does not increase Lin_exp: do nothing
% * the loop increases Lin_exp by a constant Delta: add maxsum(Loop,Delta) to the cost (in Pstrexp)
% * the loop increases Lin_exp by a linear expression Max_increment: add maxsum(Loop,Max_increment) to the cost
% * the loop resets Lin_exp to Max_resets: add Max_resets to the resets
check_loop_max((Loop_id,Loop),Head,Depth,Lin_exp,Resets,Pstrexp_pair,State,State2):-
	%for linear recursion
	Loop=loop(Head,[Call],Cs,_),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	le_print_int(Lin_exp_diff,Exp_diff_int,_),
	negate_le(Lin_exp_diff,Lin_exp_diff_neg),
	le_print_int(Lin_exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
	term_variables((Head,Call),Vars),
% the lin_exp does not increase
	(nad_entails(Vars,Cs,[Exp_diff_int>=0])->
		(get_param(debug,[])->print_or_log('     - Loop ~p does not increase the expression~n',[Loop_id]);true),
		Resets=[],
		pstrexp_pair_empty(Pstrexp_pair),
		State2=State
		;
% add a constant
		((nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta]),greater_fr(Delta,0))->
			(get_param(debug,[])->print_or_log('     - Loop ~p  increases the expression by ~p ~n',[Loop_id,Delta]);true),
			get_loop_itvar(Loop_id,Loop_name),
			Pstrexp_pair=add([mult([Loop_name,Delta])])-add([]),
			Resets=[],
			State2=State
		;
			loop_ioVars(Loop,ioVars(_,Input_vars_head,_)),
			select_important_variables(Vars,Lin_exp,Vars_of_Interest),
			max_min_linear_expression_all(Lin_exp_diff_neg, Vars_of_Interest, Cs,max, Max_increments),
%add an expression		
			(Max_increments\=[]->
				(get_param(debug,[])->
					maplist(write_lin_exp_in_phase(loop_vars(Head,[Call])),Max_increments,Max_increments_print),
				    print_or_log('     - Loop ~p  increases the expression by ~p ~n',[Loop_id,Max_increments_print]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				Depth2 is Depth+1,
				state_save_pending_list(State,sum,Depth2,loop_vars(Head,[Call]),Loop_id,Maxsums,State2),
				Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
				Resets=[]
			;
%reset		
trace,
				copy_term((Head,Lin_exp),(Call,Lin_exp_p)),
				max_min_linear_expression_all(Lin_exp_p, Input_vars_head, Cs,max, Maxs_resets),
				Maxs_resets\=[],!,
				(get_param(debug,[])->
				    maplist(write_lin_exp_in_phase(loop_vars(Head,[Call])),Maxs_resets,Maxs_resets_print),
				    print_or_log('     - Loop ~p  resets the expression to ~p ~n',[Loop_id,Maxs_resets_print]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Maxs_resets,Maxtops),
				Depth2 is Depth+1,
				state_save_pending_list(State,max_min,Depth2,loop_vars(Head,[Call]),Loop_id,Maxtops,State2),
				pstrexp_pair_empty(Pstrexp_pair),
				Resets=[Aux_itvar]
			)
		)
	).
				
%FIXME this can be improved				
check_loop_max((Loop_id,Loop),Head,Depth,Lin_exp,Resets,Pstrexp_pair,State,State2):-
	%for multiple recursion
	Loop=loop(Head,Calls,Cs,_),
	Calls=[_,_|_],
	maplist(get_difference_version_aux(Head,Lin_exp),Calls,Lin_exp_diffs),
	term_variables((Head,Calls),Vars),
	exclude(is_positive(Vars,Cs),Lin_exp_diffs,Lin_exp_diffs_non_pos),
% the lin_exp does not increase
	(Lin_exp_diffs_non_pos=[]->
		(get_param(debug,[])->print_or_log('     - Loop ~p does not increase the expression~n',[Loop_id]);true),
		Resets=[],
		pstrexp_pair_empty(Pstrexp_pair),
		State2=State
		;
% add a constant
		maplist(negate_le,Lin_exp_diffs_non_pos,Lin_exp_diffs_neg),
		(foldl(get_maximum_increase(Cs),Lin_exp_diffs_neg,0,Delta)->
			(get_param(debug,[])->print_or_log('     - Loop ~p  increases the expression by ~p ~n',[Loop_id,Delta]);true),
			get_loop_itvar(Loop_id,Loop_name),
			Pstrexp_pair=add([mult([Loop_name,Delta])])-add([]),
			Resets=[],
			State2=State
		;
			loop_ioVars(Loop,ioVars(_,Input_vars_head,_)),
			select_important_variables(Input_vars_head,Lin_exp,Vars_of_Interest),
			max_min_linear_expression_list_all(Lin_exp_diffs_neg,Vars, Vars_of_Interest, Cs,max, Max_increments),
%add an expression		
			(Max_increments\=[]->
				(get_param(debug,[])->
				    maplist(write_lin_exp_in_phase(loop_vars(Head,Calls)),Max_increments,Max_increments_print),
				    print_or_log('     - Loop ~p  increases the expression by ~p ~n',[Loop_id,Max_increments_print]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				Depth2 is Depth+1,
				state_save_pending_list(State,sum,Depth2,loop_vars(Head,Calls),Loop_id,Maxsums,State2),
				Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
				Resets=[]
			;
%reset		
				maplist(get_tail_version(Head,Lin_exp),Calls,Lin_exp_tails),
				max_min_linear_expression_list_all(Lin_exp_tails,Vars, Input_vars_head, Cs,max, Maxs_resets),
				Maxs_resets\=[],!,
				(get_param(debug,[])->
				    maplist(write_lin_exp_in_phase(loop_vars(Head,Calls)),Maxs_resets,Maxs_resets_print),
				    print_or_log('     - Loop ~p  resets the expression to ~p ~n',[Loop_id,Maxs_resets_print]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Maxs_resets,Maxtops),		
				Depth2 is Depth+1,
				state_save_pending_list(State,max_min,Depth2,loop_vars(Head,Calls),Loop_id,Maxtops,State2),
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


	
	
%! check_loop_min(Loop:loop_id,Head:term,Lin_exp:alinexp,Resets:list(itvar),Pstrexp_pair:pstrexp_pair,Pending:pending_constrs,Pending_out:pending_constrs)
% check the different possible behaviors of Loop with respect to Lin_exp
% similar to generate_loops_maxmin_classification
check_loop_min((Loop_id,Loop),Head,Depth,Lin_exp,Resets,Pstrexp_pair,State,State2):-
	Loop=loop(Head,Calls,Cs,_),
	Calls=[Call],
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	le_print_int(Lin_exp_diff,Exp_diff_int,Exp_diff_denominator),
	%negate_le(Lin_exp_diff,Lin_exp_diff_neg),
	%le_print_int(Lin_exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
	term_variables((Head,Call),Vars),
% the Lin_exp does not decrease
	(nad_entails(Vars,Cs,[Exp_diff_int=<0])->
		(get_param(debug,[])->print_or_log('     - Loop ~p does not decrease the expression~n',[Loop_id]);true),
		Resets=[],
		pstrexp_pair_empty(Pstrexp_pair),
		State2=State
		;
% decreases by a constant
		((nad_maximize([Exp_diff_int=Exp_diff_denominator*D|Cs],[D],[Delta]),greater_fr(Delta,0))->
			(get_param(debug,[])->print_or_log('     - Loop ~p  decreases the expression by ~p ~n',[Loop_id,Delta]);true),
			get_loop_itvar(Loop_id,Loop_name),
			Pstrexp_pair=add([])-add([mult([Loop_name,Delta])]),
			Resets=[],
			State2=State
		;
			loop_ioVars(Loop,ioVars(_,Input_vars_head,_)),
			select_important_variables(Input_vars_head,Lin_exp,Vars_of_Interest),
			max_min_linear_expression_all(Lin_exp_diff, Vars_of_Interest, Cs,max, Max_increments),
%decreases by an expression		
			(Max_increments\=[]->
				(get_param(debug,[])->
					maplist(write_lin_exp_in_phase(loop_vars(Head,[Call])),Max_increments,Max_increments_print),
					print_or_log('     - Loop ~p  decreases the expression by ~p ~n',[Loop_id,Max_increments_print]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				Depth2 is Depth+1,
				state_save_pending_list(State,sum,Depth2,loop_vars(Head,Calls),Loop_id,Maxsums,State2),
				Pstrexp_pair=add([])-add([mult([Aux_itvar])]),
				Resets=[]
			;
%reset		
				copy_term((Head,Lin_exp),(Call,Lin_exp_p)),
				max_min_linear_expression_all(Lin_exp_p, Input_vars_head, Cs,min, Mins_resets),
				Mins_resets\=[],!,
				(get_param(debug,[])->
					maplist(write_lin_exp_in_phase(loop_vars(Head,[Call])),Mins_resets,Mins_resets_print),
					print_or_log('     - Loop ~p  resets the expression to ~p ~n',[Loop_id,Mins_resets_print]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],lb),Mins_resets,Maxtops),
				Depth2 is Depth+1,
				state_save_pending_list(State,max_min,Depth2,loop_vars(Head,Calls),Loop_id,Maxtops,State2),
				pstrexp_pair_empty(Pstrexp_pair),
				Resets=[Aux_itvar]
			)
		)
	).   
	
	
check_loop_min((Loop_id,Loop),Head,Depth,Lin_exp,Resets,Pstrexp_pair,State,State2):-
	%for multiple recursion
	Loop=loop(Head,Calls,Cs,_),
	Calls=[_,_|_],
	maplist(get_difference_version_aux(Head,Lin_exp),Calls,Lin_exp_diffs),
	term_variables((Head,Calls),Vars),
	exclude(is_positive(Vars,Cs),Lin_exp_diffs,Lin_exp_diffs_non_pos),
% the lin_exp does not increase
	(Lin_exp_diffs_non_pos=[]->
		(get_param(debug,[])->print_or_log('     - Loop ~p does not increase the expression~n',[Loop_id]);true),
		Resets=[],
		pstrexp_pair_empty(Pstrexp_pair),
		State2=State
		;
% remove a constant
		(foldl(get_maximum_increase(Cs),Lin_exp_diffs_non_pos,0,Delta)->
		    (get_param(debug,[])->print_or_log('     - Loop ~p  decreases the expression by ~p ~n',[Loop_id,Delta]);true),
			get_loop_itvar(Loop_id,Loop_name),
			Pstrexp_pair=add([mult([Loop_name,Delta])])-add([]),
			Resets=[],
			State2=State
		;
			get_input_output_vars(Head,Input_vars_head,_),
			select_important_variables(Input_vars_head,Lin_exp,Vars_of_Interest),
			max_min_linear_expression_list_all(Lin_exp_diffs_non_pos,Vars, Vars_of_Interest, Cs,max, Max_increments),
%add an expression		
			(Max_increments\=[]->
				(get_param(debug,[])->
				    maplist(write_lin_exp_in_phase(loop_vars(Head,Calls)),Max_increments,Max_increments_print),
				    print_or_log('     - Loop ~p  increases the expression by ~p ~n',[Loop_id,Max_increments_print]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				Depth2 is Depth+1,
				state_save_pending_list(State,sum,Depth2,loop_vars(Head,Calls),Loop_id,Maxsums,State2),
				Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
				Resets=[]
			;
%reset		
				maplist(get_tail_version(Head,Lin_exp),Calls,Lin_exp_tails),
				max_min_linear_expression_list_all(Lin_exp_tails,Vars, Input_vars_head, Cs,min, Mins_resets),
				Mins_resets\=[],!,
				(get_param(debug,[])->
				    maplist(write_lin_exp_in_phase(loop_vars(Head,Calls)),Mins_resets,Mins_resets_print),
				    print_or_log('     - Loop ~p  resets the expression to ~p ~n',[Loop_id,Mins_resets_print]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],lb),Mins_resets,Maxtops),			
				Depth2 is Depth+1,
				state_save_pending_list(State,max_min,Depth2,loop_vars(Head,Calls),Loop_id,Maxtops,State2),
				pstrexp_pair_empty(Pstrexp_pair),
				Resets=[Aux_itvar]
			)
		)
	).	 
	
is_negative(Vars,Cs,Lin_exp):-
	le_print_int(Lin_exp,Lin_exp_int,_),
	nad_entails(Vars,Cs,[Lin_exp_int=<0]).
	