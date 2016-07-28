/** <module> phase_inductive_sum_strategy

This module implements 2 strategies: inductive_sum_strategy and inductive_level_sum_strategy
-inductive_sum_strategy computes the sum of lin_exp over all the CE evaluations of a phase

-inductive_level_sum_strategy computes the sum of lin_exp over all the CE evaluations of a phase at a depth (a level of the execution tree)

Both strategies generate a candidate using a linear template and Farkas' Lemma 
and then check whether the candidate is increased, decreased, reset and add the corresponding terms to the constraints
For sums of constants we use the already computed ranking functions.

If we have linear recursion, we can generate 'tail' candidates that depend on the final values of the variables of the phase
For multiple recursion, we only generate (for now) 'head' candidates that depend on the input values.

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
		init_inductive_sum_strategy/0,
		inductive_sum_strategy/8,
		inductive_level_sum_strategy/7,
		find_minsum_constraint/8
	]).
:- use_module(phase_common).	
:- use_module(phase_solver,[
				used_pending_constraint/3,
				save_used_pending_constraint/3,
				enriched_loop/4,
				current_chain_prefix/1,
		        empty_pending/1,
		        save_pending_list/6,
		        extract_pending/6,
		        union_pending/3]).
:- use_module('../../db',[get_input_output_vars/3]).			        
:- use_module('../constraints_maximization',[max_min_linear_expression_all/5]).		
:- use_module('../../IO/params',[get_param/2]).		
:- use_module('../../IO/output',[print_candidate_in_phase/3,write_lin_exp_in_phase/3,print_or_log/2]).		
:- use_module('../../ranking_functions',[partial_ranking_function/7]).	
:- use_module('../../utils/cofloco_utils',[
			tuple/3,
			ground_copy/2,
			bagof_no_fail/3]).
:- use_module('../../utils/cost_structures',[
			new_itvar/1,
			get_loop_itvar/2,
			astrexp_new/2,
			pstrexp_pair_empty/1,
			pstrexp_pair_add/3,
			itvar_shorten_name/3,
			fconstr_new/4,
			iconstr_new/4]).			
:-use_module('../../utils/template_inference',[
			difference_constraint_farkas_ub/6,
			difference_constraint_farkas_multiple_ub/5,
			difference_constraint_farkas_lb/5,
			farkas_leave_ub_candidate/5
	]).		
					
:- use_module(stdlib(numeric_abstract_domains),[
			nad_maximize/3,
			nad_entails/3,
			nad_consistent_constraints/1]).
:- use_module(stdlib(linear_expression),[
			integrate_le/3,
			write_le/2,
			sum_le/3,
			multiply_le/3,
			semi_normalize_le/3,
			subtract_le/3,
			negate_le/2]).							
:- use_module(stdlib(fraction),[inverse_fr/2,greater_fr/2,geq_fr/2,divide_fr/3,negate_fr/2,multiply_fr/3,subtract_fr/3]).


:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list)).
:- use_module(library(apply_macros)).
:- use_module(library(lists)).	

:-dynamic candidate_result/5.

init_inductive_sum_strategy:-
	retractall(candidate_result(_,_,_,_,_)).

inductive_sum_strategy(Constr,Loop_vars,Loop,Phase,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	(get_param(debug,[])->print_or_log('   - Applying inductive sum strategy ~n',[]);true),
	Constr=bound(Op,Lin_exp,Bounded),
	((Lin_exp=[]+_C, Loop_vars=loop_vars(Head,[_Call]))->
		generate_rf_candidates(Op,Head,Loop,Candidates)
	;
		generate_lecandidates(Loop_vars,Lin_exp,Op,Loop,Candidates)
	),
	(Op=ub->
	maplist(check_loops_maxsum(Loop_vars,Phase,Loop,Bounded,Pending),Candidates,New_fconstrs_list,New_iconstrs_list,Pending_out_list)
	;
	maplist(check_loops_minsum(Loop_vars,Phase,Loop,Bounded,Pending),Candidates,New_fconstrs_list,New_iconstrs_list,Pending_out_list)
	),
	ut_flat_list(New_fconstrs_list,New_fconstrs),
	New_fconstrs\=[],
	ut_flat_list(New_iconstrs_list,New_iconstrs),
	empty_pending(Empty_pending),
	foldl(union_pending,Pending_out_list,Empty_pending,Pending_out).
	
inductive_level_sum_strategy(Constr,Head,Phase,New_fconstrs,New_iconstrs,Pending,Pending_out):-
	(get_param(debug,[])->print_or_log('   - Applying inductive level-sum strategy ~n',[]);true),
	Constr=bound(Op,Lin_exp,Bounded),
	Op=ub,
	generate_leave_candidates(Head,Lin_exp,Op,Candidates),
	maplist(check_loops_maxsum(loop_vars(Head,[]),Phase,0,Bounded,Pending),Candidates,New_fconstrs_list,New_iconstrs_list,Pending_out_list),	
	ut_flat_list(New_fconstrs_list,New_fconstrs),
	New_fconstrs\=[],
	ut_flat_list(New_iconstrs_list,New_iconstrs),
	empty_pending(Empty_pending),
	foldl(union_pending,Pending_out_list,Empty_pending,Pending_out).

generate_rf_candidates(ub,Head,Loop,Candidates):-
	current_chain_prefix(Chain_prefix),
    %obtain the ranking functions for the loop and their difference version
    % if rf=x+y the difference version is (x+y)-(x'+y')
	bagof_no_fail(Rf,
	Deps^Deps_type^Loops^Phase^
	(
		partial_ranking_function(Head,Chain_prefix,Phase,Loops,Rf,Deps,Deps_type),
		contains_sl(Loops,Loop:1)		
	),Rfs),
	maplist(tuple(head),Rfs,Head_candidates),
	maplist(tuple(tail),Rfs,Tail_candidates),
	append(Head_candidates,Tail_candidates,Candidates).

%FIXME lower bounds: standarize the format of the function	
generate_rf_candidates(lb,Head,Loop,Tail_candidates):-
	(get_param(compute_lbs,[])->
		current_chain_prefix(Chain_prefix),
		bagof_no_fail(Lb,get_partial_lower_bound(Head,Chain_prefix,Loop,Lb),Lbs)
		;
		Lbs=[]
	),
	maplist(tuple(tail),Lbs,Tail_candidates).

get_partial_lower_bound(Head,Chain,Loop,Lb):-
	copy_term(Head,Call),
	partial_ranking_function(Head,Chain,_Phase,Loops,Rf,_,_),
	contains_sl(Loops,Loop:1),	
	get_difference_version(Head,Call,Rf,Rf_diff),
	integrate_le(Rf_diff,Den,Rf_diff_nat),
	write_le(Rf_diff_nat,Rf_diff_nat_print),
	enriched_loop(Loop,Head,[Call],Cs),
	Constraint= (Den* D = Rf_diff_nat_print),
	Cs_1 = [ Constraint | Cs],
	nad_maximize(Cs_1,[D],[Delta]),
	inverse_fr(Delta,Delta_inv),
	multiply_le(Rf,Delta_inv,Lb).
%! 	generate_lecandidates(Head:term,Call:term,Lin_exp:nlinexp,Max_min:flag,Loop:loop_id,Total_exps:list(nlinexp))
% generate linear expressions that are candidates to represent the
% sum of all the instances of Lin_exp in Loop 
%
% use Farkas lemma
generate_lecandidates(loop_vars(Head,[Call]),Lin_exp,ub,Loop,Candidates):-!,
	enriched_loop(Loop,Head,[Call],Cs),	
	get_param(n_candidates,[Max_candidates]),
	difference_constraint_farkas_ub(Head,Call,Cs,Lin_exp,Diff_list,Diff_list2),
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_),
	ut_split_at_pos(Diff_list2,Max_candidates,Diff_list_selected2,_),
	maplist(tuple(tail),Diff_list_selected,Head_candidates),
	maplist(tuple(head),Diff_list_selected2,Tail_candidates),
	append(Head_candidates,Tail_candidates,Candidates).

generate_lecandidates(loop_vars(Head,Calls),Lin_exp,ub,Loop,Head_candidates):-
	Calls=[_,_|_],
	enriched_loop(Loop,Head,Calls,Cs),	
	get_param(n_candidates,[Max_candidates]),
	difference_constraint_farkas_multiple_ub(Head,Calls,Cs,Lin_exp,Diff_list),
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_),
	from_list_sl(Diff_list_selected,Diff_list_selected_set),
	maplist(tuple(head),Diff_list_selected_set,Head_candidates),
	Diff_list_selected_set\=[].
	
%FIXME lower bounds: standarize the format of the function	
generate_lecandidates(loop_vars(Head,[Call]),Lin_exp,lb,Loop,Tail_candidates):-
	enriched_loop(Loop,Head,[Call],Cs),	
	get_param(n_candidates,[Max_candidates]),
	difference_constraint_farkas_lb(Head,Call,Cs,Lin_exp,Diff_list),
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_),
	maplist(tuple(tail),Diff_list_selected,Tail_candidates).	

generate_leave_candidates(Head,Lin_exp,ub,Head_candidates):-
	%take any loop
	enriched_loop(_Loop,Head,Calls,Cs),
	nad_consistent_constraints(Cs),
	get_param(n_candidates,[Max_candidates]),
	farkas_leave_ub_candidate(Head,Calls,Cs,Lin_exp,Diff_list),!,
	
	ut_split_at_pos(Diff_list,Max_candidates,Diff_list_selected,_),
	from_list_sl(Diff_list_selected,Diff_list_selected_set),
	maplist(tuple(head),Diff_list_selected_set,Head_candidates),
	Diff_list_selected_set\=[].
	
% check_loops_maxsum(Head:term,Call:term,Phase:phase,Loop:loop_id,Bounded_ini:list(itvar),Pending:pending_constrs,Exp:nlinexp,Fconstrs:list(fconstr),Iconstrs:list(iconstr),Pending_out:pending_constrs) is semidet
% check the effect of the loops of Phase on the candidate Exp and generate the corresponding constraints Fconstrs and Iconstrs

%if the candidate has been classified before
check_loops_maxsum(Loop_vars,_,Loop,Bounded_ini,Pending,Candidate,Fconstrs,Iconstrs,Pending):-
	Loop_vars=loop_vars(Head,_Calls),
	ground_copy((Head,Candidate),(_,Candidate_gr)),
	candidate_result(Candidate_gr,Candidate,ub,Loop_vars,Classification),!,
	Candidate=(Type,Lin_exp),
	print_candidate_in_phase(Head,Type,Lin_exp),
	(Classification=[]-> 
	   (get_param(debug,[])->
		   	print_or_log('       - We failed to classify this candidate before ~n',[]);true),
		Fconstrs=[],Iconstrs=[]
		;
		substitute_loop_classification(Classification,Loop,Bounded_ini,Classification2),
		generate_constrs_from_classification(Classification2,ub,Candidate,Loop_vars,Fconstrs,Iconstrs),
		(get_param(debug,[])->
		   	print_or_log('       - The candidate was classified before. We reuse its previous classification ~n',[]);true)
	).

check_loops_maxsum(Loop_vars,Phase,Loop,Bounded_ini,Pending,Candidate,Fconstrs,Iconstrs,Pending_out):-
	Candidate=(Type,Lin_exp),
	Loop_vars=loop_vars(Head,_Calls),
	print_candidate_in_phase(Head,Type,Lin_exp),
	check_loops_maxsum_1(Phase,Loop,Head,Candidate,Classification,Pending,Pending_out),!,
	generate_constrs_from_classification([class(cnt,Loop,Bounded_ini)|Classification],ub,Candidate,Loop_vars,Fconstrs,Iconstrs),
	save_candidate_result(Candidate,ub,Loop_vars,[class(cnt,Loop,Bounded_ini)|Classification]).

% if a candidate fails		
check_loops_maxsum(Loop_vars,_Phase,_Loop,_Bounded,_Pending,Candidate,[],[],Empty_pending):-
	empty_pending(Empty_pending),
	save_candidate_result(Candidate,ub,Loop_vars,[]).


check_loops_minsum(Loop_vars,_,Loop,Bounded_ini,Pending,Candidate,Fconstrs,Iconstrs,Pending):-
	Loop_vars=loop_vars(Head,_Calls),
	ground_copy((Head,Candidate),(_,Candidate_gr)),
	candidate_result(Candidate_gr,Candidate,lb,Loop_vars,Classification),!,
	Candidate=(Type,Lin_exp),
	print_candidate_in_phase(Head,Type,Lin_exp),
	(Classification=[]-> 
	   (get_param(debug,[])->
		   	print_or_log('       - We failed to classify this candidate before ~n',[]);true),
		Fconstrs=[],Iconstrs=[]
		;
		substitute_loop_classification(Classification,Loop,Bounded_ini,Classification2),
		generate_constrs_from_classification(Classification2,lb,Candidate,Loop_vars,Fconstrs,Iconstrs),
		(get_param(debug,[])->
		   	print_or_log('       - The candidate was classified before. We reuse its previous classification ~n',[]);true)
	).

check_loops_minsum(Loop_vars,Phase,Loop,Bounded_ini,Pending,Candidate,Fconstrs,Iconstrs,Pending_out):-
	Candidate=(Type,Lin_exp),
	Loop_vars=loop_vars(Head,_),
	print_candidate_in_phase(Head,Type,Lin_exp),
	check_loops_minsum_1(Phase,Loop,Head,Candidate,Classification,Pending,Pending_out),!,
	generate_constrs_from_classification([class(cnt,Loop,Bounded_ini)|Classification],lb,Candidate,Loop_vars,Fconstrs,Iconstrs),
	save_candidate_result(Candidate,lb,Loop_vars,[class(cnt,Loop,Bounded_ini)|Classification]).

check_loops_minsum(Loop_vars,_Phase,_Loop,_Bounded,_Pending,Candidate,[],[],Empty_pending):-
	empty_pending(Empty_pending),
	save_candidate_result(Candidate,lb,Loop_vars,[]).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

generate_constrs_from_classification(Classification,ub,(Type,Lin_exp),Loop_vars,Fconstrs,Iconstrs):-
	partition(is_class(cnt),Classification,Cnt_class,Other_classes),
	foldl(join_class_elements,Cnt_class,[],Bounded_vars),
	from_list_sl(Bounded_vars,Bounded_set),
	(Type=head->
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
generate_constrs_from_classification(Classification,lb,(tail,Lin_exp),Loop_vars,Fconstrs,Iconstrs):-
	partition(is_class(cnt),Classification,Cnt_class,Other_classes),
	foldl(join_class_elements,Cnt_class,[],Bounded_vars),
	from_list_sl(Bounded_vars,Bounded_set),
	Loop_vars=loop_vars(Head,[Call]),
	get_difference_version(Head,Call,Lin_exp,Sum),
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
	
	
save_candidate_result(Candidate,Op,Loop_vars,Classification):-
	Loop_vars=loop_vars(Head,_Calls),
	ground_copy((Head,Candidate),(_,Candidate_gr)),
	assertz(candidate_result(Candidate_gr,Candidate,Op,Loop_vars,Classification)).	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_loops_maxsum_1([],_,_,_,[],Pending,Pending).
%ignore the loop that we started from	
check_loops_maxsum_1([Loop|Loops],Loop,Head,Candidate,Classification,Pending,Pending_out):-!,
	check_loops_maxsum_1(Loops,Loop,Head,Candidate,Classification,Pending,Pending_out).
		
check_loops_maxsum_1([Loop2|Loops],Loop,Head,Candidate,[Class|Classification],Pending,Pending_out):-	
	check_loop_maxsum(Head,Candidate,Loop2,Class,Pending,Pending1),!,
	check_loops_maxsum_1(Loops,Loop,Head,Candidate,Classification,Pending1,Pending_out).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_loops_minsum_1([],_,_,_,[],Pending,Pending).
%ignore the loop that we started from	
check_loops_minsum_1([Loop|Loops],Loop,Head,Candidate,Classification,Pending,Pending_out):-!,
		check_loops_minsum_1(Loops,Loop,Head,Candidate,Classification,Pending,Pending_out).
		
check_loops_minsum_1([Loop2|Loops],Loop,Head,Candidate,[Class|Classification],Pending,Pending_out):-	
		check_loop_minsum(Head,Candidate,Loop2,Class,Pending,Pending1),!,
		check_loops_minsum_1(Loops,Loop,Head,Candidate,Classification,Pending1,Pending_out).




%! check_loop_maxsum(Head:term,Call:term,Exp_diff:nlinexp,Flag:term,Loop:loop_id,Pstrexp_pair:pstrexp_pair,Bounded:list(itvar),Pending:pending_constrs,Pending1:pending_constrs)
% check the effect of Loop on Exp_diff, Flag indicates if the original candidate was head or head-tail
% * this can modify the pending constraints Pending->Pending1
% * generates a Pstrexp_pair with the elements that have to be added to the constraint
% * sometimes we can bound some itvar from Loop, those are in Bounded
check_loop_maxsum(Head,(Type,Exp),Loop,Class,Pending,Pending1):-
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
	    (find_maxsum_constraint(Loop,Head,Calls,Cs,Exp_diff,Type,Bounded,Pending,Pending1)->			
		   Class=class(cnt,Loop,Bounded),
		   (get_param(debug,[])->
		   	maplist(itvar_shorten_name(no_list),Bounded,Bounded_short),
		   	print_or_log('       - Loop ~p is collaborative and bounds ~p ~n',[Loop,Bounded_short]);true)
		   ;
		   
			Pending1=Pending,
			Class=class(cnt,Loop,[]),
			(get_param(debug,[])->print_or_log('       - Loop ~p is collaborative~n',[Loop]);true)
		)
	;
%if add a constant	
	(nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta])->
		get_loop_itvar(Loop,Loop_name),
		Class=class(add,Loop,[mult([Loop_name,Delta])]),
		Pending1=Pending,
		(get_param(debug,[])->print_or_log('       - Loop ~p adds a constant ~p ~n',[Loop,Delta]);true)
		;
		get_input_output_vars(Head,Input_vars_head,_),
		%select_important_variables(Vars_head,Exp_diff_neg,Vars_of_Interest),
		select_important_variables(Vars,Exp_diff_neg,Vars_of_Interest),
		max_min_linear_expression_all(Exp_diff_neg, Vars_of_Interest, Cs,max, Max_increments),
%add an expression
		(Max_increments\=[]->
				new_itvar(Aux_itvar),
				Class=class(add,Loop,[mult([Aux_itvar])]),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				save_pending_list(sum,loop_vars(Head,Calls),Loop,Maxsums,Pending,Pending1),
				(get_param(debug,[])->
					maplist(write_lin_exp_in_phase(loop_vars(Head,Calls)),Max_increments,Max_increments_print),
					print_or_log('       - Loop ~p adds an expression ~p~n',[Loop,Max_increments_print]);true)
			    ;
%reset			    
			    Type=head,
				max_min_linear_expression_all(Sum_calls, Input_vars_head, Cs,max, Max_resets),
				Max_resets\=[],
				
   				new_itvar(Aux_itvar),
   				Class=class(add,Loop,[mult([Aux_itvar])]),
				maplist(fconstr_new([Aux_itvar],ub),Max_resets,Maxsums),
				save_pending_list(sum,loop_vars(Head,Calls),Loop,Maxsums,Pending,Pending1),
				(get_param(debug,[])->
					maplist(write_lin_exp_in_phase(loop_vars(Head,Calls)),Max_resets,Max_resets_print),
					print_or_log('       - Loop ~p has a reset to  ~p~n',[Loop,Max_resets_print]);true)
		)
	)
	).

check_loop_maxsum(_Head,_Candidate,Loop,_,_Pending,_Pending1):-	
	    (get_param(debug,[])->print_or_log('       - Loop ~p has undefined behavior ~n',[Loop]);true),
		fail.	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! check_loop_minsum(Head:term,Call:term,Exp_diff:nlinexp,Loop:loop_id,Pstrexp_pair:pstrexp_pair,Bounded:list(itvar),Pending:pending_constrs,Pending1:pending_constrs)
% similar to check_loop_maxsum but checking the different possibilities in opposite order
% for minsum there are only head-tail candidatesq
check_loop_minsum(Head,(_Type,Exp),Loop,Class,Pending,Pending1):-	
	enriched_loop(Loop,Head,Calls,Cs),
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
			Class=class(cnt,Loop,[])
			;
			get_loop_itvar(Loop,Loop_name),
			Class=class(add,Loop,[mult([Loop_name,Delta])])
		),
		Pending1=Pending,
		(get_param(debug,[])->print_or_log('       - Loop ~p adds a constant ~p ~n',[Loop,Delta]);true)
		;
		%term_variables(Head,Vars_head),
		select_important_variables(Vars,Exp_diff_neg,Vars_of_Interest),
		max_min_linear_expression_all(Exp_diff_neg, Vars_of_Interest, Cs,min, Max_increments),
%add an expression
	    Max_increments\=[],
		new_itvar(Aux_itvar),
		Class=class(add,Loop,[mult([Aux_itvar])]),
		maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
		save_pending_list(sum,loop_vars(Head,Calls),Loop,Maxsums,Pending,Pending1),
		(get_param(debug,[])->
			maplist(write_lin_exp_in_phase(loop_vars(Head,Calls)),Max_increments,Max_increments_print),
			print_or_log('       - Loop ~p adds an expression ~p~n',[Loop,Max_increments_print]);true)
	).

%collaborative loop	with constraint
check_loop_minsum(Head,(_Type,Exp),Loop,Class,Pending,Pending1):-
		enriched_loop(Loop,Head,Calls,Cs),
		foldl(get_sum_call(Head,Exp),Calls,[]+0,Sum_calls),
		subtract_le(Exp,Sum_calls,Exp_diff),
		find_minsum_constraint(Loop,Head,Calls,Cs,Exp_diff,Bounded,Pending,Pending1),!,
		Class=class(cnt,Loop,Bounded),
		(get_param(debug,[])->
			maplist(itvar_shorten_name(no_list),Bounded,Bounded_short),
			print_or_log('       - Loop ~p is collaborative and bounds ~p~n',[Loop,Bounded_short]);true).
% we don't substract loops that can decrease the bound
% in theory this could happen, in practice it doesn't seem to happen so we skip it and fail in those cases		
	
check_loop_minsum(_Head,_Candidate,Loop,_,_Pending,_):-	
	    (get_param(debug,[])->print_or_log('       - Loop ~p has undefined behavior ~n',[Loop]);true),
		fail.	
		
		
		
		
%! find_maxsum_constraint(Loop:loop_id,Head:term,Call:term,Cs:polyhedron,Exp_diff:nlinexp,Flag:flag,Bounded:list(itvar),Pending:pending_constrs,Pending_out:pending_constrs)
% try to find a pending maxsum that can be bounded by Exp_diff
% we check that Exp_diff>= Exp2 and in case we are dealing with a head candidate
% we also check Exp_original>=Exp2
find_maxsum_constraint(Loop,Head,Calls,Cs,Exp_diff,Type,Bounded,Pending,Pending_out):-
		extract_pending(Loop,sum,Pending,loop_vars(Head,Calls),(_Depth,bound(ub,Exp2,Bounded)),Pending1),
		term_variables((Head,Calls),Vars),
		subtract_le(Exp_diff,Exp2,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),
		(Type=head->
			%make a copy with all the variables in Calls set to 0
		   copy_term((Exp_diff,Head,Calls),(Exp_original,Head,Calls2)),
		   term_variables(Calls2,Vars_calls2),
		   maplist(=(0),Vars_calls2),
		   subtract_le(Exp_original,Exp2,Exp_diff_base_case),
		   le_print_int(Exp_diff_base_case,Exp_diff_base_case_print,_),
		   nad_entails(Vars,Cs,[Exp_diff_base_case_print>=0]),
		   Pending_out=Pending1
		  ;
		  Pending_out=Pending),
		!,
		save_used_pending_constraint(Loop,loop_vars(Head,Calls),bound(ub,Exp2,Bounded)).

%FIXME this code has not been adapted yet
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
find_minsum_constraint(Loop,Head,Calls,Cs,Exp_diff,Bounded,Pending,Pending):-
		extract_pending(Loop,sum,Pending,loop_vars(Head,Calls),(_Depth,bound(lb,Exp2,Bounded)),_Pending_out),
		term_variables((Head,Calls),Vars),
		subtract_le(Exp2,Exp_diff,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),!,
		save_used_pending_constraint(Loop,loop_vars(Head,Calls),bound(lb,Exp2,Bounded)).
%this is important for lower bounds!	

find_minsum_constraint(Loop,Head,Calls,Cs,Exp_diff,Bounded,Pending,Pending):-
		phase_solver:used_pending_constraint(Loop,loop_vars(Head,Calls),bound(lb,Exp2,Bounded)),
		term_variables((Head,Calls),Vars),
		subtract_le(Exp2,Exp_diff,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),!.		
		
		
get_sum_call(Head,Exp,Call,Lin_exp,Lin_exp1):-
	copy_term((Head,Exp),(Call,Exp1)),
	sum_le(Exp1,Lin_exp,Lin_exp1).		
		
		
		