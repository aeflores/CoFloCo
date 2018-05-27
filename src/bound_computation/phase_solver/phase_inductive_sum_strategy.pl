/** <module> phase_inductive_sum_strategy

This module implements the inductive_sum_strategy
-inductive_sum_strategy computes the sum of lin_exp over all the CE evaluations of a phase
and optionally over tails in multiple recursion

The strategy generate a candidate using a linear template and Farkas' Lemma 
and then checks whether the candidate is increased, decreased, reset and add the corresponding terms to the constraints
For sums of constants in the linear case, we use the already computed ranking functions.

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


:- module(phase_inductive_sum_strategy,[
	inductive_sum_strategy/8,
	find_minsum_constraint/8
	]).
	
:- use_module(phase_common).	
:- use_module(phase_solver,[
	state_get_property/3,
	state_get_one_pending/3,
	state_save_new_fconstrs/4,
	state_save_new_iconstrs/3,
	state_get_used_constr/2,
	type_of_loop/2,
	state_save_pending_list/7,
	state_get_candidate_result/3,
	state_save_candidate_result/3
	]).
			        
:- use_module('../constraints_maximization',[max_min_linear_expression_all/5]).		
:- use_module('../../refinement/loops',[
	loop_get_rfs/2,
	loop_head/2,
	loop_calls/2,
	loop_ioVars/2,
	loop_constraints/2
	]).	
:- use_module('../../refinement/chains',[
	phase_get_termination_flag/2
	]).			


:- use_module('../../IO/params',[get_param/2]).		
:- use_module('../../IO/output',[
	print_candidate_in_phase/3,
	write_lin_exp_in_phase/3,
	print_or_log/2,
	interesting_example_warning/2
	]).		

:- use_module('../../utils/cofloco_utils',[
	tuple/3,
	ground_copy/2
	]).
:- use_module('../../utils/cost_structures',[
	new_itvar/1,
	get_loop_itvar/2,
	astrexp_new/2,
	pstrexp_pair_empty/1,
	pstrexp_pair_add/3,
	fconstr_new/4,
	iconstr_new/4
	]).			
:-use_module('../../utils/template_inference',[
	difference_constraint_farkas_ub/6,
	difference_constraint_farkas_ub_leaf/7,
	difference_constraint_farkas_lb/6
	]).		
					
:- use_module(stdlib(numeric_abstract_domains),[
	nad_maximize/3,
	nad_entails/3,
	nad_consistent_constraints/1
	]).
:- use_module(stdlib(linear_expression),[
	integrate_le/3,
	write_le/2,
	sum_le/3,
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
:- use_module(stdlib(list_map),[
	lookup_lm/3
	]).	
:- use_module(stdlib(set_list)).
:- use_module(library(apply_macros)).
:- use_module(library(lists)).	


inductive_sum_strategy(Constr,Depth,Loop_vars,Loop_id,Phase_loops,State,State2,Changes):-
	(get_param(debug,[])->print_or_log('   - Applying inductive sum strategy ~n',[]);true),
	Constr=bound(Op,Lin_exp,Bounded),
	lookup_lm(Phase_loops,Loop_id,Loop),
	((Lin_exp=[]+_C, Loop_vars=loop_vars(Head,[Call]))->
		generate_rf_candidates(Op,Head,Call,Loop,Candidates)
	;
		state_get_property(State,phase,Phase),
		phase_get_termination_flag(Phase,Term_flag),
		generate_lecandidates(Loop_vars,Lin_exp,Op,Loop,Term_flag,Candidates)
	),
	foldl(check_loops_sum(Op,Loop_vars,Phase_loops,Loop_id,Bounded,Depth),Candidates,(State,[]),(State2,Changes)).

generate_rf_candidates(ub,Head,_Call,Loop,Candidates):-
	loop_get_rfs(Loop,ranking_functions([(1,Rfs_aux)])),
	loop_head(Loop,Head_aux),
	copy_term((Head_aux,Rfs_aux),(Head,Rfs)),
	maplist(parse_le_fast,Rfs,Rfs_le),
	maplist(tuple(head),Rfs_le,Head_candidates),
	maplist(tuple(tail),Rfs_le,Tail_candidates),
	append(Head_candidates,Tail_candidates,Candidates).

%FIXME lower bounds: standarize the format of the function	
generate_rf_candidates(lb,Head,Call,Loop,Tail_candidates):-
	(get_param(compute_lbs,[])->
		loop_get_rfs(Loop,ranking_functions([(1,Rfs_aux)])),
		foldl(get_partial_lower_bound(Head,Call,Loop),Rfs_aux,[],Lbs)
		;
		Lbs=[]
	),
	maplist(tuple(tail),Lbs,Tail_candidates).

get_partial_lower_bound(Head,Call,Loop,Rf,Lbs,[Lb_final|Lbs]):-
	loop_head(Loop,Head_aux),
	loop_calls(Loop,[Call_aux]),
	parse_le_fast(Rf,Rf_le),
	get_difference_version(Head_aux,Call_aux,Rf_le,Rf_diff),
	integrate_le(Rf_diff,Den,Rf_diff_nat),
	write_le(Rf_diff_nat,Rf_diff_nat_print),
	loop_constraints(Loop,Cs),
	Constraint= (Den* D = Rf_diff_nat_print),
	Cs_1 = [ Constraint | Cs],
	nad_maximize(Cs_1,[D],[Delta]),!,
	inverse_fr(Delta,Delta_inv),
	multiply_le(Rf_le,Delta_inv,Lb),
	copy_term((Head_aux,Call_aux,Lb),(Head,Call,Lb_final)).
get_partial_lower_bound(_Head,_Call,_Loop,_Rf,Lbs,Lbs).	
%! 	generate_lecandidates(Head:term,Call:term,Lin_exp:nlinexp,Max_min:flag,Loop:loop_id,Total_exps:list(nlinexp))
% generate linear expressions that are candidates to represent the
% sum of all the instances of Lin_exp in Loop 
%
% use Farkas lemma
generate_lecandidates(loop_vars(Head,Calls),Lin_exp,ub,Loop,Term_flag,Candidates):-!,
	Loop=loop(Head,Calls,Cs,_),
	loop_ioVars(Loop,IOvars),
	get_param(n_candidates,[Max_candidates]),
	%add extra for leafs
%	(Calls=[]->
%	   enriched_loop(_Loop2,Head,Calls2,Cs2),
%	   Calls2=[_|_],
%	   difference_constraint_farkas_ub_leaf(Head,Calls,Cs,Lin_exp,(Calls2,Cs2),Diff_list)
%	   ;
	   difference_constraint_farkas_ub(Head,Calls,IOvars,Cs,Lin_exp,Diff_list),
%	),
	%check that the candidates are correct
	(get_param(debug,[])->
		maplist(check_candidate(Head,Calls,Loop,Lin_exp,'>='),Diff_list)
		;
		true
	),
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_),
	maplist(tuple(head),Diff_list_selected,Head_candidates),
	
	% the strategy without resets is not applicable in non-terminating chains
	(Term_flag=non_terminating->
		Tail_candidates=[]
		;
		maplist(tuple(tail),Diff_list_selected,Tail_candidates)
	),
	%% For finding interesting examples
	interesting_example_warning(no_candidate,(Lin_exp,loop_vars(Head,Calls),Loop,Head_candidates)),
	append(Head_candidates,Tail_candidates,Candidates).


generate_lecandidates(loop_vars(Head,Calls),Lin_exp,lb,Loop,terminating,Tail_candidates):-
	Loop=loop(Head,Calls,Cs,_),
	loop_ioVars(Loop,IOvars),
	get_param(n_candidates,[Max_candidates]),
	difference_constraint_farkas_lb(Head,Calls,IOvars,Cs,Lin_exp,Diff_list),
	%check that the candidates are correct
	(get_param(debug,[])-> maplist(check_candidate(Head,Calls,Loop,Lin_exp,'=<'),Diff_list);true),
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_),
	maplist(tuple(tail),Diff_list_selected,Tail_candidates).	


% this is only executed in debug mode, to detect problems with
% the candidate generation
check_candidate(Head,Calls,Loop,Linexp,Op,Exp):-
	Loop=loop(Head,Calls,Cs,_),
	foldl(get_sum_call(Head,Exp),Calls,[]+0,Sum_calls),
	term_variables((Head,Calls),Vars),	
	subtract_le(Exp,Sum_calls,Exp_diff),
	subtract_le(Exp_diff,Linexp,Exp_diff2),
	
	le_print_int(Linexp,Linexp_print_int,_),

	le_print_int(Exp_diff,Exp_diff_print_int,_),
	le_print_int(Exp_diff2,Exp_diff_print_int2,_),
	Constr=..[Op,Exp_diff_print_int,0],
	Constr2=..[Op,Exp_diff_print_int2,0],
	nad_entails(Vars,[Linexp_print_int=<0|Cs],[Constr]),
	nad_entails(Vars,[Linexp_print_int>=0|Cs],[Constr2]),!.
	
check_candidate(Head,Calls,Loop,Linexp,_Op,Exp):-
	write_lin_exp_in_phase(loop_vars(Head,Calls),Linexp,Linexp_print),
	write_lin_exp_in_phase(loop_vars(Head,Calls),Exp,Exp_print),
	throw(incorrect_candidate(Loop,Linexp_print,Exp_print)).

	
% check_loops_maxsum(+Loop_vars:loop_vars,+Phase:phase,+Loop:loop_id,+Bounded_ini:list(itvar),+Pending:pending_constrs,+Candidate:nlinexp,-Fconstrs:list(fconstr),-Iconstrs:list(iconstr),-Pending_out:pending_constrs) is semidet
% check the effect of the loops (and tails) of Phase on the candidate Exp and generate the corresponding constraints Fconstrs and Iconstrs

%if the candidate has been classified before

check_loops_sum(Op,Loop_vars,_Phase_loops,Loop_id,Bounded_ini,_Depth,Candidate,(State,Changes),(State3,Changes2)):-
	Loop_vars=loop_vars(Head,_Calls),
	state_get_candidate_result(State,candidate(Loop_vars,Candidate,Op),candidate_result(Candidate,Op,Loop_vars,Classification)),!,
	Candidate=(Type,Lin_exp),
	print_candidate_in_phase(Head,Type,Lin_exp),
	(Classification=[]-> 
		State3=State,
		Changes2=Changes,
	   (get_param(debug,[])->
		   	print_or_log('       - We failed to classify this candidate before ~n',[]);true)
		
		;
		substitute_loop_classification(Classification,Loop_id,Bounded_ini,Classification2),
		generate_constrs_from_classification(Classification2,Op,Candidate,Loop_vars,State,Fconstrs,Iconstrs),
		state_save_new_fconstrs(State,Loop_vars,Fconstrs,State2),
		state_save_new_iconstrs(State2,Iconstrs,State3),
		Changes2=[new_fconstrs(Loop_vars,Fconstrs),new_iconstrs(Iconstrs)|Changes],
		(get_param(debug,[])->
		   	print_or_log('       - The candidate was classified before. We reuse its previous classification ~n',[]);true)
	).
	


check_loops_sum(Op,Loop_vars,Phase_loops,Loop_id,Bounded_ini,Depth,Candidate,(State,Changes),(State5,Changes2)):-
	Candidate=(Type,Lin_exp),
	Loop_vars=loop_vars(Head,_Calls),
	print_candidate_in_phase(Head,Type,Lin_exp),
	generate_loops_sum_classification(Phase_loops,Op,Depth,Loop_id,Head,Candidate,Classification,State,State2),!,
	generate_constrs_from_classification([class(cnt,Loop,Bounded_ini)|Classification],Op,Candidate,Loop_vars,State,Fconstrs,Iconstrs),
	state_save_new_fconstrs(State2,Loop_vars,Fconstrs,State3),
	state_save_new_iconstrs(State3,Iconstrs,State4),
	Changes2=[new_fconstrs(Loop_vars,Fconstrs),new_iconstrs(Iconstrs)|Changes],

	state_save_candidate_result(State4,	candidate_result(Candidate,Op,Loop_vars,[class(cnt,Loop,Bounded_ini)|Classification]),State5).

% if a candidate fails	
check_loops_sum(Op,Loop_vars,_Phase_loops,_Loop_id,_Bounded_ini,_Depth,Candidate,(State,Changes),(State2,Changes)):-	
	state_save_candidate_result(State,candidate_result(Candidate,Op,Loop_vars,[]),State2).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

generate_loops_sum_classification([],_Op,_Depth,_Loop_id,_Head,_Candidate,[],State,State).

%ignore the loop that we started from	
generate_loops_sum_classification([(Loop_id,_Loop)|Phase_loops],Op,Depth,Loop_id,Head,Candidate,Classification,State,State2):-!,
	generate_loops_sum_classification(Phase_loops,Op,Depth,Loop_id,Head,Candidate,Classification,State,State2).

generate_loops_sum_classification([Loop_pair|Phase_loops],ub,Depth,Loop_id,Head,Candidate,[Class|Classification],State,State3):-
	classify_loop_sum_ub(Head,Candidate,Loop_pair,Depth,Class,State,State2),!,
	generate_loops_sum_classification(Phase_loops,ub,Depth,Loop_id,Head,Candidate,Classification,State2,State3).
	
generate_loops_sum_classification([Loop_pair|Phase_loops],lb,Depth,Loop_id,Head,Candidate,[Class|Classification],State,State3):-
	classify_loop_sum_lb(Head,Candidate,Loop_pair,Depth,Class,State,State2),!,
	generate_loops_sum_classification(Phase_loops,lb,Depth,Loop_id,Head,Candidate,Classification,State2,State3).


%! classify_loop_sum_ub(+Head:term,+Candidate:(type,nlinexp),+Loop:loop_id,-Class:class_term,+Pending:pending_constrs,-Pending1:pending_constrs) is semidet
% check the effect of Loop on the Candidate
% try to classify the candidate in the different classes in order
% * this can modify the pending constraints Pending->Pending1
% * generates a class_term that is used later to generate the corresponding constraints
classify_loop_sum_ub(Head,(Type,Exp),(Loop_id,Loop),Depth,Class,State,State2):-
	type_of_loop(Loop_id,Loop_type),
	Loop=loop(Head,Calls,Cs,_),
	foldl(get_sum_call(Head,Exp),Calls,[]+0,Sum_calls),
	subtract_le(Exp,Sum_calls,Exp_diff),
	term_variables((Head,Calls),Vars),	
	le_print_int(Exp_diff,Exp_diff_print_int,_),
	negate_le(Exp_diff,Exp_diff_neg),
	le_print_int(Exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
%if Exp does not increase
	(nad_entails(Vars,Cs,[Exp_diff_print_int>=0])->
	 %find a collaborative loop
	    (find_maxsum_constraint(Loop_id,Head,Calls,Cs,Exp_diff,Exp,Type,Bounded,State,State2)->			
		   Class=class(cnt,Loop_id,Bounded),
		   (get_param(debug,[])->
		   	print_or_log('       - ~p ~p is collaborative and bounds ~p ~n',[Loop_type,Loop_id,Bounded]);true)
		   ;
		   
		   	State2=State,
			Class=class(cnt,Loop_id,[]),
			(get_param(debug,[])->print_or_log('       - ~p ~p is collaborative~n',[Loop_type,Loop_id]);true)
		)
	;
	% If we have Inductive strategy with resets, we can ignore the leafs
	((Calls=[],Type=head)->
			State2=State,	
			Class=class(cnt,Loop_id,[]),
			(get_param(debug,[])->print_or_log('       - Chain ~p is ignored~n',[Loop_id]);true)
	;
	
%if add a constant	
	(nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta])->
		get_loop_itvar(Loop_id,Loop_name),
		Class=class(add,Loop_id,[mult([Loop_name,Delta])]),
		State2=State,
		(get_param(debug,[])->print_or_log('       - ~p ~p adds a constant ~p ~n',[Loop_type,Loop_id,Delta]);true)
		;
		loop_ioVars(Loop,ioVars(_,Input_vars_head,_)),
		%select_important_variables(Vars_head,Exp_diff_neg,Vars_of_Interest),
		select_important_variables(Vars,Exp_diff_neg,Vars_of_Interest),
		max_min_linear_expression_all(Exp_diff_neg, Vars_of_Interest, Cs,max, Max_increments),
%add an expression
		(Max_increments\=[]->
				new_itvar(Aux_itvar),
				Class=class(add,Loop_id,[mult([Aux_itvar])]),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
					
				Depth2 is Depth+1,
				state_save_pending_list(State,sum,Depth2,loop_vars(Head,Calls),Loop_id,Maxsums,State2),
				(get_param(debug,[])->
					maplist(write_lin_exp_in_phase(loop_vars(Head,Calls)),Max_increments,Max_increments_print),
					print_or_log('       - ~p ~p adds an expression ~p~n',[Loop_type,Loop_id,Max_increments_print]);true)
			    ;
%reset			    
			    Type=head,
				max_min_linear_expression_all(Sum_calls, Input_vars_head, Cs,max, Max_resets),
				Max_resets\=[],
				
   				new_itvar(Aux_itvar),
   				Class=class(add,Loop_id,[mult([Aux_itvar])]),
				maplist(fconstr_new([Aux_itvar],ub),Max_resets,Maxsums),
				Depth2 is Depth+1,
				state_save_pending_list(State,sum,Depth2,loop_vars(Head,Calls),Loop_id,Maxsums,State2),
				(get_param(debug,[])->
					maplist(write_lin_exp_in_phase(loop_vars(Head,Calls)),Max_resets,Max_resets_print),
					print_or_log('       - ~p ~p has a reset to  ~p~n',[Loop_type,Loop_id,Max_resets_print]);true)
		)
	)
	)
	).

classify_loop_sum_ub(_,_,(Loop_id,_Loop),_Depth,_Class,_State,_State2):-
	    type_of_loop(Loop_id,Loop_type),
	    (get_param(debug,[])->print_or_log('       - ~p ~p has undefined behavior ~n',[Loop_type,Loop_id]);true),
		fail.	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! classify_loop_sum_lb(+Head:term,+Candidate:(type,nlinexp),+Loop:loop_id,-Class:class_term,+Pending:pending_constrs,-Pending1:pending_constrs) is semidet
% similar to classify_loop_sum_ub but checking the different possibilities in opposite order
% for minsum there are only head-tail candidatesq
classify_loop_sum_lb(Head,(_Type,Exp),(Loop_id,Loop),Depth,Class,State,State2):-	
	type_of_loop(Loop_id,Loop_type),
	Loop=loop(Head,Calls,Cs,_),
	foldl(get_sum_call(Head,Exp),Calls,[]+0,Sum_calls),
	subtract_le(Exp,Sum_calls,Exp_diff),
	term_variables((Head,Calls),Vars),
	le_print_int(Exp_diff,Exp_diff_print_int,_),
%increasing
	nad_entails(Vars,Cs,[Exp_diff_print_int=<0]),
	negate_le(Exp_diff,Exp_diff_neg),
	le_print_int(Exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
%add a constant		
	(nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta])->
		(is_zero(Delta)->
			Class=class(cnt,Loop_id,[])
			;
			get_loop_itvar(Loop_id,Loop_name),
			Class=class(add,Loop_id,[mult([Loop_name,Delta])])
		),
		State2=State,
		(get_param(debug,[])->print_or_log('       - ~p ~p adds a constant ~p ~n',[Loop_type,Loop_id,Delta]);true)
		;
		%term_variables(Head,Vars_head),
		select_important_variables(Vars,Exp_diff_neg,Vars_of_Interest),
		max_min_linear_expression_all(Exp_diff_neg, Vars_of_Interest, Cs,min, Max_increments),
%add an expression
	    Max_increments\=[],
		new_itvar(Aux_itvar),
		Class=class(add,Loop_id,[mult([Aux_itvar])]),
		maplist(fconstr_new([Aux_itvar],lb),Max_increments,Maxsums),
		Depth2 is Depth+1,
		state_save_pending_list(State,sum,Depth2,loop_vars(Head,Calls),Loop_id,Maxsums,State2),
		(get_param(debug,[])->
			maplist(write_lin_exp_in_phase(loop_vars(Head,Calls)),Max_increments,Max_increments_print),
			print_or_log('       - ~p ~p adds an expression ~p~n',[Loop_type,Loop_id,Max_increments_print]);true)
	).

%collaborative loop	with constraint
classify_loop_sum_lb(Head,(_Type,Exp),(Loop_id,Loop),_Depth,Class,State,State2):-
		type_of_loop(Loop_id,Loop_type),
		Loop=loop(Head,Calls,Cs,_),
		foldl(get_sum_call(Head,Exp),Calls,[]+0,Sum_calls),
		subtract_le(Exp,Sum_calls,Exp_diff),
		find_minsum_constraint(Loop_id,Head,Calls,Cs,Exp_diff,Bounded,State,State2),!,
		Class=class(cnt,Loop,Bounded),
		(get_param(debug,[])->
			print_or_log('       - ~p ~p is collaborative and bounds ~p~n',[Loop_type,Loop,Bounded]);true).
% we don't substract loops that can decrease the bound
% in theory this could happen, in practice it doesn't seem to happen so we skip it and fail in those cases		
	
classify_loop_sum_lb(_Head,_Candidate,(Loop_id,_),_Depth,_Class,_State,_State2):-	
	    type_of_loop(Loop_id,Loop_type),
	    (get_param(debug,[])->print_or_log('       - ~p ~p has undefined behavior ~n',[Loop_type,Loop_id]);true),
		fail.	
		
			
get_sum_call(Head,Exp,Call,Lin_exp,Lin_exp1):-
	copy_term((Head,Exp),(Call,Exp1)),
	sum_le(Exp1,Lin_exp,Lin_exp1).		
		
		
%! find_maxsum_constraint(Loop:loop_id,Head:term,Call:term,Cs:polyhedron,Exp_diff:nlinexp,Exp_original:nlinexp,Flag:flag,Bounded:list(itvar),Pending:pending_constrs,Pending_out:pending_constrs)
% try to find a pending maxsum that can be bounded by Exp_diff
% we check that Exp_diff>= Exp2 and in case we are dealing with a head candidate
% we also check Exp_original>=Exp2
find_maxsum_constraint(Loop_id,Head,Calls,Cs,Exp_diff,Exp_original,Type,Bounded,State,State2):-
		state_get_one_pending(State,pending(sum,Loop_id,_Depth,loop_vars(Head,Calls),bound(ub,Exp2,Bounded)),_State1),
		term_variables((Head,Calls),Vars),
		subtract_le(Exp_diff,Exp2,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),
		(Type=head->
			%make a copy with all the variables in Calls set to 0
		   subtract_le(Exp_original,Exp2,Exp_diff_base_case),
		   le_print_int(Exp_diff_base_case,Exp_diff_base_case_print,_),
		   nad_entails(Vars,Cs,[Exp_diff_base_case_print>=0]),
		   State2=State
		  ;
		  State2=State).
%FIXME this code has not been adapted yet
find_maxsum_constraint(Loop_id,Head,Calls,Cs,Exp_diff,Exp_original,Type,Bounded,State,State):-
		state_get_used_constr(State,used(sum,Loop_id,loop_vars(Head,Calls),bound(ub,Exp2,Bounded))),
		term_variables((Head,Calls),Vars),
		subtract_le(Exp_diff,Exp2,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),
		(Type=head->
			%make a copy with all the variables in Calls set to 0
		   subtract_le(Exp_original,Exp2,Exp_diff_base_case),
		   le_print_int(Exp_diff_base_case,Exp_diff_base_case_print,_),
		   nad_entails(Vars,Cs,[Exp_diff_base_case_print>=0])
		  ;
		  true
		 ).
	

/*
find_maxsum_constraint(Loop,Head,Call,Cs,Exp_diff,Flag,Bounded,Pending,Pending):-
		phase_solver:used_pending_constraint(Loop,loop_vars(Head,[Call]),bound(ub,Exp2,Bounded)),
		term_variables((Head,Call),Vars),
		subtract_le(Exp_diff,Exp2,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),
		(Flag=head(Exp_original)->
		   subtract_le(Exp_original,Exp2,Exp_diff_base_case),
		   le_print_int(Exp_diff_base_case,Exp_diff_base_case_print,_),
		   nad_entails(Vars,Cs,[Exp_diff_base_case_print>=0])
		  ;
		  true),!.
*/	

%! find_minsum_constraint(Loop:loop_id,Head:term,Call:term,Cs:polyhedron,Exp_diff:nlinexp,Flag:flag,Bounded:list(itvar),Pending:pending_constrs,Pending_out:pending_constrs)
% try to find a pending minsum that can be bounded by Exp_diff
% we check that Exp_diff=< Exp2 	
find_minsum_constraint(Loop_id,Head,Calls,Cs,Exp_diff,Bounded,State,State):-
		state_get_one_pending(State,pending(sum,Loop_id,_Depth,loop_vars(Head,Calls),bound(lb,Exp2,Bounded)),_State2),
		term_variables((Head,Calls),Vars),
		subtract_le(Exp2,Exp_diff,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),!.
%this is important for lower bounds!	

find_minsum_constraint(Loop_id,Head,Calls,Cs,Exp_diff,Bounded,State,State):-
		state_get_used_constr(State,used(sum,Loop_id,loop_vars(Head,Calls),bound(lb,Exp2,Bounded))),
		term_variables((Head,Calls),Vars),
		subtract_le(Exp2,Exp_diff,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),!.		
		
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%		
generate_constrs_from_classification(Classification,ub,(Type,Lin_exp),Loop_vars,State,Fconstrs,Iconstrs):-
	partition(is_class(cnt),Classification,Cnt_class,Other_classes),
	foldl(join_class_elements,Cnt_class,[],Bounded_vars),
	from_list_sl(Bounded_vars,Bounded_set),
	((Type=head;state_get_property(State,phase_type,multiple))->
		Sum=Lin_exp
		;
		Loop_vars=loop_vars(Head,[Call]),
		get_difference_version(Head,Call,Lin_exp,Sum)
	),
	(Other_classes=[] ->
		fconstr_new(Bounded_set,ub,Sum,Ub_fconstr),
		Fconstrs=[Ub_fconstr],
		Iconstrs=[]
		;
		new_itvar(Aux_itvar),
		partition(is_class(add),Other_classes,Add_class,Sub_class),
		foldl(join_class_elements,Add_class,[mult([Aux_itvar])],Pos_summands),
		foldl(join_class_elements,Sub_class,[],Neg_summands),
		astrexp_new(add(Pos_summands)-add(Neg_summands),Astrexp),
		fconstr_new([Aux_itvar],ub,Sum,Ub_fconstr),
		iconstr_new(Astrexp,ub,Bounded_set,Ub_iconstr),
		Fconstrs=[Ub_fconstr],
		Iconstrs=[Ub_iconstr]
	).
generate_constrs_from_classification(Classification,lb,(tail,Lin_exp),Loop_vars,State,Fconstrs,Iconstrs):-
	partition(is_class(cnt),Classification,Cnt_class,Other_classes),
	foldl(join_class_elements,Cnt_class,[],Bounded_vars),
	from_list_sl(Bounded_vars,Bounded_set),
	(state_get_property(State,phase_type,multiple)->
		Sum=Lin_exp
		;
		Loop_vars=loop_vars(Head,[Call]),
		get_difference_version(Head,Call,Lin_exp,Sum)
	),
	(Other_classes=[] ->
		fconstr_new(Bounded_set,lb,Sum,Ub_fconstr),
		Fconstrs=[Ub_fconstr],
		Iconstrs=[]
		;
		new_itvar(Aux_itvar),
		new_itvar(Aux_itvar2),
		partition(is_class(add),Other_classes,Add_class,Sub_class),
		foldl(join_class_elements,Add_class,[mult([Aux_itvar])],Pos_summands),
		foldl(join_class_elements,Sub_class,[mult([Aux_itvar2])],Neg_summands),
		astrexp_new(add(Pos_summands)-add(Neg_summands),Astrexp),
		negate_le(Sum,Sum_neg),
		fconstr_new([Aux_itvar2],ub,Sum_neg,Ub_fconstr),
		fconstr_new([Aux_itvar],lb,Sum,Lb_fconstr),
		iconstr_new(Astrexp,lb,Bounded_vars,Lb_iconstr),
		Fconstrs=[Ub_fconstr,Lb_fconstr],
		Iconstrs=[Lb_iconstr]
	).



is_class(Class,class(Class,_,_)).
join_class_elements(class(_Class,_Loop,Element),Accum,Accum2):-
	append(Element,Accum,Accum2).

%it should never reach the end of the list
substitute_loop_classification([class(cnt,Loop,_)|Classification],Loop,Bounded2,[class(cnt,Loop,Bounded2)|Classification]):-!.
substitute_loop_classification([Class|Classification],Loop,Bounded2,[Class|Classification2]):-
	substitute_loop_classification(Classification,Loop,Bounded2,Classification2).
		