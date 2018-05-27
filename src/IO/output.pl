/** <module> output

This module prints the results of the analysis

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


:- module(output,[
	init_output/0,
    print_help/0,
    print_header/3,
    print_or_log/2,
    print_or_log_nl/0,
    print_warning/2,
    print_warning_in_error_stream/2,
    interesting_example_warning/2,
	print_chains/1,
	print_chains_graph/1,
	print_sccs/1,
	print_merging_cover_points/3,
	%  print_new_scc/2,
	print_partially_evaluated_sccs/1,
	print_equations_refinement/1,
	print_loops/1,
	print_external_patterns/1,
	print_ranking_functions/2,
	print_termination_arguments/1,
	print_changes_map/2,
	
	print_phase_solving_state/1,	
	print_selected_pending_constraint/3,
	
	print_phase_computation_changes/1,
	print_product_strategy_message/3,
	print_candidate_in_phase/3,
	write_lin_exp_in_phase/3,
	print_removed_redundant_constr_message/2,
	print_joined_itvar_sets_message/1,
	print_cycle_in_cstr_warning/0,
	print_changed_to_chain_method_warning/1,
	print_removed_possibly_redundant_cstrs/1,
	print_removed_unresolved_cstrs_cycle/1, 
	
	print_ce_bounds/1,
	print_loop_bounds/1,
	print_phase_bounds/1,
	print_chain_bounds/1,
	print_external_patterns_bounds/1,
	
%	print_phase_cost/4,
%	print_loops_costs/3,
	print_chains_closed_bounds/2,
	print_single_closed_result/1,
	print_competition_result/1,
	print_log/0,
	print_piecewise_bounds/2,
	print_cost_structure/1,
	print_aux_exp/1,
	print_itvars_renaming/1,
	print_stats/0
	]).

:- use_module('../db',[
	ground_equation_header/1
	]).
:- use_module('../pre_processing/SCCs',[scc_get_cover_points/2]).
:- use_module('../refinement/invariants',[back_invs_get/3]).
:- use_module('../refinement/loops',[
	loop_head/2,
	loop_calls/2,
	loop_get_CEs/2,
	loop_get_rfs/2,
	loop_get_cost/2,	
	
	loops_get_head/2,
	loops_get_ids/2,
	loops_get_list/2,
	loops_get_list_with_id/2
]).

:- use_module('../refinement/chains',[
	phase_get_pattern/2,
	phase_get_cost/2,
	phase_is_iterative/1,
	phase_get_rfs/2,
	phase_get_termination/2,
	chain_get_pattern/2,
	chain_get_property/3,
	chain_get_cost/2,
	chain_get_closed_upper_bound/2,
	chain_get_closed_lower_bound/2
	]).
:- use_module('../bound_computation/phase_solver/phase_solver',[type_of_loop/2]).

:- use_module('../utils/crs',[
	ce_head/2,
	ce_rec_calls/2,
	ce_get_cost/2,
	ce_get_refined/2,
	cr_nameArity/2,
	cr_get_ceList_with_id/2
	]).
			
:- use_module('../utils/cost_expressions',[
	get_asymptotic_class_name/2,
	cexpr_simplify/3
	]).
:- use_module('../utils/cofloco_utils',[
	constraint_to_coeffs_rep/2,
	write_sum/2,
	tuple/3,
	ground_copy/2
	]).

:- use_module('../utils/cost_structures',[
	cstr_get_itvars/2,
	cstr_get_unbounded_itvars/2,
	itvar_recover_long_name/2,
	astrexp_to_cexpr/2
	]).
:- use_module('../utils/structured_cost_expression',[
	strexp_simplify_max_min/2,
	strexp_to_cost_expression/2
	]).

:- use_module('../IO/params',[
	parameter_dictionary/3,
	get_param/2,
	param_description/2
	]).

:- use_module(stdlib(linear_expression),[write_le/2]).
:- use_module(stdlib(profiling),[profiling_get_info/3]).
:- use_module(stdlib(counters),[counter_get_value/2]).
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list),[contains_sl/2]).
:- use_module(stdlib(list_map),[
	map_values_lm/3,
	values_lm/2
	]).
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(lambda)).
:-use_module(library(varnumbers)).

:-dynamic log_entry/3.

init_output:-
	set_prolog_flag(print_write_options,[quoted(false),numbervars(true)]),
	retractall(log_entry(_,_,_)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% predicates to print or log information depending on wether with are in the competition or not

print_or_log_list([]).
print_or_log_list([Elem|List]):-
	print_or_log('~p~n',[Elem]),
	print_or_log_list(List).

print_or_log(String,Args):-
	get_param(competition,[]),!,
	assertz(log_entry([],String,Args)).
	
print_or_log(String,Args):-
	format(String,Args).
	
print_or_log_nl:-
	get_param(competition,[]),!,
	assertz(log_entry([],'~n',[])).
	
print_or_log_nl:-nl.
	
print_log:-
	log_entry(Options,String,Args),
	(Options=[]->
		format(String,Args)
		;
		ansi_format_aux(Options,String,Args)
	),fail.
	
print_log.


ansi_print_or_log(Options,String,Args):-
	get_param(competition,[]),!,
	assertz(log_entry(Options,String,Args)).
	
ansi_print_or_log(Options,String,Args):-
	ansi_format_aux(Options,String,Args).
	
ansi_format_aux(Options,Format,Args):-current_prolog_flag(dialect,swi),!,ansi_format(Options,Format,Args).
ansi_format_aux(_,Format,Args):-current_prolog_flag(dialect,yap),format(Format,Args).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

print_header(Text,Arguments,1):-!,
	print_or_log_nl,
	ansi_print_or_log([bold],Text,Arguments),
	print_or_log('=====================================~n',[]).
print_header(Text,Arguments,2):-!,
	print_or_log_nl,
	ansi_print_or_log([bold],Text,Arguments),
	print_or_log('-------------------------------------~n',[]).
print_header(Text,Arguments,3):-!,
	print_or_log_nl,
	ansi_print_or_log([bold],'###~p',[' ']),
	ansi_print_or_log([bold],Text,Arguments).
print_header(Text,Arguments,4):-!,
	print_or_log_nl,
	ansi_print_or_log([bold],'####~p',[' ']),
	ansi_print_or_log([bold],Text,Arguments).	
print_header(Text,Arguments,5):-!,
	print_or_log_nl,
	ansi_print_or_log([bold],'#####~p',[' ']),
	ansi_print_or_log([bold],Text,Arguments).	
print_header(Text,Arguments,6):-!,
	print_or_log_nl,
	ansi_print_or_log([bold],'######~p',[' ']),
	ansi_print_or_log([bold],Text,Arguments).		
	
print_warning(_Text,_Args):-
	get_param(no_warnings,[]),!.
print_warning(Text,Args):-
	print_or_log(Text,Args).	

% debugging predicate to find interesting examples
interesting_example_warning(no_candidate,([]+_C,loop_vars(Head,[_|_]),Loop,[])):-
    get_param(debug,[]),!,
	ground_copy(Head,Headp),
	print_warning_in_error_stream('No candidate for multiple recursion ~p in ~p~n',[Headp,Loop]).
	
interesting_example_warning(failed_maximization,([],Lin_exp,Loop,Head,Calls)):-
	get_param(debug,[]),!,
	copy_term((Lin_exp,Head,Calls),	 (Lin_exp_p,Head_p,Calls_p)),
	write_le(Lin_exp_p,Exp_p),
	ground_header(Head_p),
	ground_rec_calls(Calls_p,1),
	print_warning_in_error_stream('Failed max/minimization of ~p in ~p: ~p -> ~p~n',[Exp_p,Loop,Head_p,Calls_p]).

interesting_example_warning(_,_).	
	
print_warning_in_error_stream(Text,Args):-	
	format(user_error,Text,Args).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
	
print_sccs(SCC_list):-
	get_param(v,[X]),X > 1,!,
	print_header('Computed strongly connected components ~n',[],4),
	reverse(SCC_list,SCC_list_rev),
	foldl(print_scc,SCC_list_rev,1,_).
print_sccs.

print_scc(scc(Type,Nodes,_Subgraph,_Entries,Info),SCC_N,SCC_N1):-
	SCC_N1 is SCC_N+1,
	(Info\=[] ->Info_print=Info;Info_print=''),
	print_or_log('~p. ~p ~p : ~p~n',[SCC_N,Type,Info_print,Nodes]).


%print_new_scc(Entry,SCC_N):-
%	get_param(v,[X]),X > 1,!,
%	print_or_log('* The entry ~p is not a cutpoint so it becomes a new SCC ~p~n',[Entry,SCC_N]).
%print_new_scc(_,_).
	
print_merging_cover_points(SCC_N,Cover_points,Merged):-
	get_param(v,[X]),X > 1,!,
	print_or_log('~p. SCC does not have a single cut point : ~p  ~n Merged into ~p~n',[SCC_N,Cover_points,Merged]).
print_merging_cover_points(_,_,_).	
	
print_partially_evaluated_sccs(SCC_list):-
	get_param(v,[X]),X > 1,!,
	print_header('Obtained direct recursion through partial evaluation ~n',[],4),
	reverse(SCC_list,SCC_list_rev),
	foldl(print_partially_evaluated,SCC_list_rev,1,_).
print_partially_evaluated_sccs.

print_partially_evaluated(SCC,SCC_N,SCC_N1):-
	scc_get_cover_points(SCC,[Cover_point]),!,
	SCC_N1 is SCC_N+1,
	print_or_log('~p. SCC is partially evaluated into ~p~n',[SCC_N,Cover_point]).	
print_partially_evaluated(_SCC,SCC_N,SCC_N1):-
	SCC_N1 is SCC_N+1,
	print_or_log('~p. SCC is completely evaluated into other SCCs~n',[SCC_N]).		
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%! print_equations_refinement(+Head:term,+RefCnt:int) is det
% print the calls from the SCC Head in the refinement phase RefCnt
% if the verbosity is high enough
print_equations_refinement(CR):-
	get_param(v,[X]),X > 1,!,
	cr_nameArity(CR,Name/Arity),
	print_header('Specialization of cost equations ~p ~n',[Name/Arity],3),
	print_equations_refinement_1(CR),
	(X>2-> 
		print_header('Refined cost equations ~p ~n',[Name/Arity],4),
		print_CR(CR)
	;
		true
	).
print_equations_refinement(_).
	
print_equations_refinement_1(CR):-
	cr_get_ceList_with_id(CR,Eqs),
	map_values_lm(ce_get_refined,Eqs,Pairs_refined),
	maplist(\Pair^Pair2^(Pair=(A,B),Pair2=B-A),Pairs_refined,Inverse_pairs),
	group_pairs_by_key(Inverse_pairs,Grouped_pairs),
	maplist(print_refined_pair,Grouped_pairs),
	print_or_log_nl.
	
print_refined_pair(Eq_id-Refined_list):-
	print_or_log('* CE ~p is refined into CE ~p ~n',[Eq_id,Refined_list]).

%print_or_log('* CE ~p is discarded (unfeasible) ~n',[Eq_id])


print_CR(CR):-
	cr_get_ceList_with_id(CR,Eqs),
	copy_term(Eqs,Eqs_copy),
	maplist(pretty_print_CE,Eqs_copy).

pretty_print_CE((Id,eq_ref(Head,Cost,_,_,Calls,Cs,_))):-
	foldl(unify_equalities,Cs,[],Cs2),
	maplist(pretty_print_constr,Cs2,Cs3),
	ground_header(Head),
	Head=..[_|Var_names],
	max_var_number(Var_names,0,Max),InitN is Max+1,
	numbervars((Cost,Calls,Cs3),InitN,_),
	print_or_log('* CE ~p: ~p =~| ',[Id,Head]),
	print_cost_structure(Cost),
	pretty_print_refinedCalls(Calls,'+'),
	print_or_log_nl,
	print_or_log('     ~p ~n',[Cs3]).


pretty_print_refinedCalls([],_).
pretty_print_refinedCalls([Pattern:Call|Calls],Sep):-!,
	print_or_log('~a ~p',[Sep,Call:Pattern]),
	pretty_print_refinedCalls(Calls,Sep).
pretty_print_refinedCalls([RecCall|Calls],Sep):-
	print_or_log('~a ~p',[Sep,RecCall]),
	pretty_print_refinedCalls(Calls,Sep).	
		
unify_equalities(C,Cs,Cs):-
	constraint_to_coeffs_rep(C, coeff_rep([-1*A,1*A],=,0)),!.
unify_equalities(C,Cs,[C|Cs]).	

equality(Constr):-
    constraint_to_coeffs_rep(Constr, coeff_rep([-1*A,1*A],=,0)).	
%! print_loops_refinement(+Head:term,+RefCnt:int) is det
% print the correspondence between loops and cost equations from the SCC Head in the refinement phase RefCnt
% if the verbosity is high enough
print_loops(Loops):-
	get_param(v,[X]),X > 1,!,
	loops_get_head(Loops,Head),
	functor(Head,Name,Arity),
	print_header('Cost equations --> "Loop" of ~p ~n',[Name/Arity],3),
	loops_get_list_with_id(Loops,Pairs),
	maplist(print_loop_refinement,Pairs),
	(X>2-> 
		print_header('Loops of ~p ~n',[Name/Arity],4),
		maplist(print_loop,Pairs)
	;
		true
	).
print_loops_refinement(_).
	
print_loop_refinement((Id,Loop)):-
	loop_get_CEs(Loop,Eqs),
	print_or_log('* CEs ~p --> Loop ~p ~n',[Eqs,Id]).


print_loop((Id,Loop)):-
	copy_term(Loop,loop(Head,Calls,Cs,_)),
	print_or_log('* Loop ~p: ',[Id]),
	foldl(unify_equalities,Cs,[],Cs2),
	maplist(pretty_print_constr,Cs2,Cs3),
	ground_header(Head),
	ground_rec_calls(Calls,1),
	numbervars(Cs3,0,_),
	print_or_log('~p',[Head]),
	(Calls\=[]->
		print_or_log('->',[]),
		pretty_print_refinedCalls(Calls,' '),print_or_log_nl,
		print_or_log('                  ~p ~n',[Cs3])
		;
		print_or_log(' ~p ~n',[Cs3])
	).


%! print_external_pattern_refinement(+Head:term,+RefCnt:int) is det
% print the correspondence between external patterns and chains from the SCC Head in the refinement phase RefCnt
% if the verbosity is high enough
print_external_patterns(External_patterns):-
	get_param(v,[X]),X > 2,!,
	copy_term(External_patterns,external_patterns(Head,Ex_patt_map)),
	ground_header(Head),
	functor(Head,Name,Arity),
	print_header('Merging Chains  ~p into  External patterns of execution ~n',[Name/Arity],3),
	maplist(print_external_pattern,Ex_patt_map),
	print_or_log_nl.

print_external_patterns(_).
	
print_external_pattern((Pattern,external_pattern(Properties))):-
	print_or_log('* ~p : ~p ~n',[Pattern,Properties]).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_ranking_functions(Loops,Chains):-
	get_param(v,[X]),X > 1,!,
	loops_get_head(Loops,Head),
	copy_term(Head,Head_print),
	ground_header(Head_print),
	print_header('Ranking functions of CR ~p ~n',[Head_print],3),
	print_complete_ranking_functions(Chains),
	print_header('Partial ranking functions of CR ~p ~n',[Head_print],4),
	print_partial_ranking_functions(Loops),print_or_log_nl.
print_ranking_functions(_,_).

print_complete_ranking_functions(chains(Phases,_)):-
	include(phase_is_iterative,Phases,Iterative_phases),
	maplist(phase_get_rfs,Iterative_phases,Rfs),
	maplist(phase_get_pattern,Iterative_phases,Patterns),
	maplist(print_ranking_function(phase),Patterns,Rfs).

print_partial_ranking_functions(Loops):-
	loops_get_list(Loops,Loops_list),
	maplist(loop_get_rfs,Loops_list,Rfs),
	maplist(loop_head,Loops_list,Heads),
	copy_term((Heads,Rfs),(Heads_print,Rfs_print)),
	maplist(ground_header,Heads_print),
	loops_get_ids(Loops,Loops_ids),
	maplist(print_ranking_function(loop),Loops_ids,Rfs_print).
	
print_ranking_function(phase,Pattern,Rf_term):-
	copy_term(Rf_term,ranking_functions(Head,Rf)),
	ground_header(Head),
	print_or_log('* RF of phase ~p: ~p~n',[Pattern,Rf]).
	
print_ranking_function(loop,Loop,ranking_functions([])):-!,		
	print_or_log('* RF of loop ~p: ~p~n',[Loop,[1]]).	
	
print_ranking_function(loop,Loop,ranking_functions([(_,Rf)])):-!,
	print_or_log('* RF of loop ~p: ~p~n',[Loop,Rf]).	
	
print_ranking_function(loop,Loop,ranking_functions(Rfs)):-	
	maplist(print_ranking_function(sub_loop,Loop),Rfs).
	
print_ranking_function(sub_loop,Loop,(Sub_loop,Rf)):-
	print_or_log('* RF of loop ~p.~p: ~p~n',[Loop,Sub_loop,Rf]).		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


print_termination_arguments(chains(Phases,_)):-
	print_header('Termination arguments ~n',[],3),
	maplist(phase_get_termination,Phases,Termination),
	maplist(phase_get_pattern,Phases,Patterns),
	maplist(print_termination,Patterns,Termination).


print_termination(Pattern,terminating(trivial)):-!,
%	copy_term(Rf_term,ranking_functions(Head,Rf)),
	%ground_header(Head),
	print_or_log('* Phase ~p is trivially terminating~n',[Pattern]).
print_termination(Pattern,Term_arg):-
	copy_term(Term_arg,Term_arg2),
	(Term_arg2=terminating(Head,Rf)->
		ground_header(Head),
		print_or_log('* Phase ~p terminates with ranking function ~p~n',[Pattern,Rf])
		;
		Term_arg2=non_terminating(Head,Cycle),
		ground_header(Head),
		print_or_log('* Phase ~p might not terminate. Found the following cycle ~p~n',[Pattern,Cycle])
	).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! print_chains_entry(+Entry:term,+RefCnt:int) is det
% print the inferred chains in SCC Entry in the refinement phase RefCnt
print_chains(chains(Phases,Chains)):-
	get_param(v,[X]),X > 2,!,
	print_header('Phases: ~n',[],3),
	maplist(print_phase,Phases),
	print_header('Chains: ~n',[],3),
	maplist(print_chain,Chains).
print_chains(_).

print_phase(Phase):-
	phase_get_pattern(Phase,Phase_pattern),
	print_or_log(' ~p~n',[Phase_pattern]).
	

print_chain(Chain):-
	chain_get_pattern(Chain,Chain_pattern),
	(chain_get_property(Chain,termination,non_terminating)->
	   ansi_print_or_log([fg(red)],'~p...~n',[Chain_pattern])
	 ;
	   ansi_print_or_log([],'~p~n',[Chain_pattern])
	).

print_chains_graph(un_graph(_,_,Matrix)):-
	Matrix=..[_|Lines],
	maplist(writeln,Lines).

	
print_changes_map(Reason,Map):-
	get_param(v,[X]),X > 2,
	Map\=[],!,
	print_header('Chains discarded or modified because of ~p ~n',[Reason],3),
	maplist(print_change,Map).

print_changes_map(_,_).

print_change((Original,New)):-
	(New=none->
		print_or_log('Discarded chain ~p~n',[Original])
	;
		print_or_log('Chain ~p transformed into ~p~n',[Original,New])
	).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_phase_solving_state(state(StateMap)):-
	values_lm(StateMap,Values),
	maplist(print_state_elem,Values).

print_state_elem(pending_set(_,Set)):-!,
	(Set=[]->
		print_header('Empy Pending set: Done ~n',[],5)
	;
		print_header('Pending set~n',[],5),
		maplist(print_pending_constr,Set)
	).
	
print_state_elem(_Elem).
	
print_pending_constr(pending(Type,Loop,_Depth,Loop_vars,Constr)):-
	copy_term((Loop_vars,Constr),(loop_vars(Head_gr,Calls_gr),Constr_gr)),
	ground_header(Head_gr),
	ground_rec_calls(Calls_gr,1),
	write_top_exp(Constr_gr,Constr_print),
	print_or_log('* ~p in loop ~p: ~p~n',[Type,Loop,Constr_print]).
	


print_selected_pending_constraint(Loop_vars,sum(Loop),Constr):-
	get_param(debug,[]),!,
	copy_term((Loop_vars,Constr),(loop_vars(Head_gr,Calls_gr),Constr_gr)),
	ground_header(Head_gr),
	ground_rec_calls(Calls_gr,1),
	write_top_exp(Constr_gr,Constr_print),
	type_of_loop(Loop,Loop_type),
	print_header('Computing sum for ~p  in ~p ~p ~n',[Constr_print,Loop_type,Loop],6).

print_selected_pending_constraint(Head,Type,Constr):-
	get_param(debug,[]),!,
	copy_term((Head,Constr),(Head_gr,Constr_gr)),
	ground_header(Head_gr),
	write_top_exp(Constr_gr,Constr_print),
	print_header('Computing ~p for ~p  ~n',[Type,Constr_print],6).
	
print_selected_pending_constraint(_,_,_).


print_phase_computation_changes(Changes):-
	maplist(print_phase_computation_change,Changes).
print_phase_computation_change(new_fconstrs(Loop_vars,Fconstrs)):-!,
	(Fconstrs=[]->
		true
	;
	copy_term((Loop_vars,Fconstrs),(loop_vars(Head_gr,Calls_gr),Fconstrs_gr)),
	ground_header(Head_gr),
	ground_rec_calls(Calls_gr,1),
	maplist(write_top_exp,Fconstrs_gr,Fconstrs_print),
	print_or_log(' * Adding final constraints: ~p ~n',[Fconstrs_print])
	).
	
print_phase_computation_change(new_iconstrs(Iconstrs)):-!,
	copy_term(Iconstrs,Iconstrs_p),
	(Iconstrs_p=[]->
		true
	;
		maplist(write_aux_exp,Iconstrs_p,Iconstrs_print),
		print_or_log(' * Adding non-final constraints: ~p ~n',[Iconstrs_print])
	).
	

print_product_strategy_message(Head,Type,Fconstrs):-
	get_param(debug,[]),!,
	copy_term((Head,Fconstrs),(Head_gr,Fconstrs_gr)),
	ground_header(Head_gr),
	maplist(write_top_exp,Fconstrs_gr,Fconstrs_print),
	(Type=level->
		print_or_log('     - Adding to Plevel-sum: ~p ~n',[Fconstrs_print])
		;
		print_or_log('     - Adding to Pmax/min: ~p ~n',[Fconstrs_print])
	).
	
print_product_strategy_message(_,_,_).


% debugging predicates 
print_candidate_in_phase(Head,Type,Exp):-
	get_param(debug,[]),!,
	copy_term((Head,Exp),(Head_gr,Exp_gr)),
	ground_header(Head_gr),
	write_le(Exp_gr,Exp_print),
	print_or_log('     - ~p Candidate: ~p ~n',[Type,Exp_print]).

print_candidate_in_phase(_Head,_Type,_Exp).

write_lin_exp_in_phase(Loop_vars,Exp,Exp_print):-
	copy_term((Loop_vars,Exp),(loop_vars(Head_gr,Calls_gr),Exp_gr)),
	ground_header(Head_gr),
	ground_rec_calls(Calls_gr,1),
	write_le(Exp_gr,Exp_print).


print_ce_bounds(CR):-
	cr_get_ceList_with_id(CR,List),
	maplist(print_ce_bound,List).
	
print_ce_bound((Id,CE)):-
	ce_head(CE,Head),
	ce_rec_calls(CE,Calls),
	ce_get_cost(CE,Cost),
	print_cost_structure_w_name('CE',Id,Head,Cost,Calls).



print_loop_bounds(Loops):-
	loops_get_list_with_id(Loops,Loop_list),
	maplist(print_loop_bound,Loop_list).

print_loop_bound((Id,Loop)):-
	loop_head(Loop,Head),
	loop_calls(Loop,Calls),
	loop_get_cost(Loop,Cost),
	print_cost_structure_w_name('Loop',Id,Head,Cost,Calls).
	
print_phase_bounds(chains(Phases,_)):-
	maplist(print_phase_bound,Phases).

print_phase_bound(Phase):-
	phase_get_pattern(Phase,Phase_patt),
	phase_get_cost(Phase,cost(Head,Calls,Cost)),
	print_cost_structure_w_name('Phase',Phase_patt,Head,Cost,Calls).

print_chain_bounds(chains(_,Chains)):-
	maplist(print_chain_bound,Chains).

print_chain_bound(Chain):-
	chain_get_pattern(Chain,Chain_patt),
	chain_get_cost(Chain,cost(Head,Cost)),
	print_cost_structure_w_name('Chain',Chain_patt,Head,Cost).
			
%TODO
print_external_patterns_bounds(_).
			
print_cost_structure_w_name(Type,Id,Head,Cost):-
	print_cost_structure_w_name(Type,Id,Head,Cost,[]).		
print_cost_structure_w_name(Type,Id,Head,Cost,Calls):-
	copy_term((Head,Calls,Cost),(Head_gr,Calls_gr,Cost_gr)),
	ground_header(Head_gr),
	ground_rec_calls(Calls_gr,1),
	print_header('Cost of ~p ~p ~n',[Type,Id],3),
	print_cost_structure(Cost_gr).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_changed_to_chain_method_warning(Lost):-
	get_param(debug,[]),!,
	print_warning('Some Itvars are unbounded ~p ~nChanging solving method to compute the cost of the chain directly ~n',[Lost]).
	
print_changed_to_chain_method_warning(_).	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_cycle_in_cstr_warning:-
	(get_param(debug,[])->
		print_warning('Found a cycle in the non-final constraints~n',[])
	; 
		true
	).
print_removed_possibly_redundant_cstrs(Removed_iconstrs):-
	get_param(debug,[]),!,
	copy_term(Removed_iconstrs,Removed_iconstrs_copy),
	maplist(write_aux_exp,Removed_iconstrs_copy,Removed_iconstrs_print),
	print_or_log(' Removed possibly redundant constraints to solve a cycle in the cost structure ~n',[]),
	print_or_log_list(Removed_iconstrs_print).
	
print_removed_possibly_redundant_cstrs(_).	

print_removed_unresolved_cstrs_cycle(Pred_graph):-
	get_param(debug,[]),!,
	maplist(get_iconstr_from_graph,Pred_graph,Iconstrs),
	copy_term(Iconstrs,Iconstrs_copy),
	maplist(write_aux_exp,Iconstrs_copy,Iconstrs_print),
	print_or_log('Could not solve cycle in cost structure.~n Discarded constraints:  ~n',[]),
	print_or_log_list(Iconstrs_print).
	
print_removed_unresolved_cstrs_cycle(_).

get_iconstr_from_graph((_Id:Iconstr,_Preds),Iconstr).
	
	
print_removed_redundant_constr_message(Constr,Removed_set):-
	get_param(debug,[]),Removed_set\=[],!,
	copy_term((Constr,Removed_set),(Constr_copy,Removed_set_copy)),
	write_aux_exp(Constr_copy,Constr_print),
	maplist(write_aux_exp,Removed_set_copy,Removed_print),
	print_or_log(' * Removed the redundant constraints ~p (They are implied by ~p)~n',[Removed_print,Constr_print]).
print_removed_redundant_constr_message(_,_).

print_joined_itvar_sets_message(Sets):-
	get_param(debug,[]),!,
	maplist(print_joined_itvar_set,Sets).
print_joined_itvar_sets_message(_).

print_joined_itvar_set([First|Rest]):-
	print_or_log(' * Joined equivalent variables ~p into ~p~n',[[First|Rest],First]).


gen_mult_bases((A,B),A*B).

print_cost_structure(cost(Top_exps,LTop_exps,Aux_exps,Bases,Base)):-
	cstr_get_unbounded_itvars(cost(Top_exps,LTop_exps,Aux_exps,Bases,Base),Unbounded),
	partition(is_ub_aux_exp,Aux_exps,Ub_Aux_exps,Lb_Aux_exps),
	print_base(Bases,Base,Unbounded),
	((Top_exps=[],LTop_exps=[],Aux_exps=[])->
		true
	;
	print_or_log('~n  Such that:~12|',[]),
	maplist(print_top_exp,Top_exps),
	maplist(print_aux_exp,Ub_Aux_exps),
	maplist(print_top_exp,LTop_exps),
	maplist(print_aux_exp,Lb_Aux_exps)
	),
	((get_param(debug,[]),Unbounded\=[])->
		ansi_print_or_log([fg(red)],'~nUnbounded itvars~n',[]),
		maplist(itvar_recover_long_name,Unbounded,Long_names),
		maplist(print_unbounded_itvar,Unbounded,Long_names)
	;
		true	
	),!.


print_unbounded_itvar(Short,Long):-
	ansi_print_or_log([fg(red)],'~p :  ~p~n',[Short,Long]).
	
print_base([],C,_):-
	print_or_log('~p',[C]).
print_base([(Itvar,Coeff)|Bases],C,Unbounded):-
	(contains_sl(Unbounded,Itvar)->
		ansi_print_or_log([fg(red)],'~p',[Coeff*Itvar])
		;
		ansi_print_or_log([],'~p',[Coeff*Itvar])
	),
	print_or_log('+',[]),
	print_base(Bases,C,Unbounded).
		
is_ub_aux_exp(bound(ub,_,_)).

write_top_exp(bound(Op,Exp,Bounded),Constr):-
	print_op(Op,Op_p),
	write_sum(Bounded,Sum),
	write_le(Exp,Exp_print),
	Constr=..[Op_p,Sum,Exp_print].

write_aux_exp(bound(Op,Exp,Bounded),Constr):-
	print_op(Op,Op_p),
	astrexp_to_cexpr(Exp,Exp2),
	write_sum(Bounded,Sum),
	Constr=..[Op_p,Sum,Exp2].
	
print_top_exp(bound(Op,Exp,Bounded)):-
	print_op(Op,Op_p),
	write_sum(Bounded,Sum),
	write_le(Exp,Exp_print),
	print_or_log('~p ~p ~p~n',[Sum,Op_p,Exp_print]).

print_aux_exp(bound(Op,Exp_0,Bounded)):-
	print_op(Op,Op_p),
	copy_term(Exp_0,Exp),
	astrexp_to_cexpr(Exp,Exp2),
	write_sum(Bounded,Sum),
	print_or_log('~p ~p ~p~n',[Sum,Op_p,Exp2]).	
	
print_op(ub,'=<').
print_op(lb,'>=').


print_itvars_renaming(Cost):-
	get_param(debug,[]),!,
	cstr_get_itvars(Cost,Itvar_set),
	(Itvar_set\=[]->
		maplist(get_itvar_renaming,Itvar_set,Renaming),
		print_or_log(' * Renamed intermediate variables: ~n~p~n',[Renaming])
	;
		true
	).
print_itvars_renaming(_Cost).
	
get_itvar_renaming(New, Old >> New ):-
		itvar_recover_long_name(New,Old).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_chains_closed_bounds(chains(_,Chains),Back_invs):-
	print_header('Closed bounds: ~n',[],3),
	maplist(print_chain_closed_bound(Back_invs),Chains).

print_chain_closed_bound(Back_invs,Chain):-
	chain_get_pattern(Chain,Chain_patt),
	back_invs_get(Back_invs,Chain_patt,inv(Head,_,Summary)),	
	maplist(pretty_print_constr,Summary,Summary_pretty),
	(get_param(compute_ubs,[])->
		chain_get_closed_upper_bound(Chain,closed_bound(Head,UbExp)),
 	    closed_bound_print(UbExp,Summary,Ub_simple),
 	    get_asymptotic_class_name(Ub_simple,Asym_class)
 	    ;
 	    true
 	 ),
 	(get_param(compute_lbs,[])->
 		chain_get_closed_lower_bound(Chain,closed_bound(Head,LbExp)),
 		closed_bound_print(LbExp,Summary,Lb_simple),
		get_asymptotic_class_name(Lb_simple,Asym_class1)
		;
		true
	),
	copy_term((Head,Summary_pretty,Ub_simple,Lb_simple),(Head_p,Summary_p,Ub_p,Lb_p)),
	ground_header(Head_p),
	print_or_log('* Chain ~p ',[Chain_patt]),
	print_or_log(' with precondition: ~p ~n',[Summary_p]),
	(get_param(compute_ubs,[])->
	print_or_log('    - Upper bound: ~p ~n',[Ub_p]),
	print_or_log('    - Complexity: ~p ~n',[Asym_class]);true),
	(get_param(compute_lbs,[])->
	print_or_log('    - Lower bound: ~p ~n',[Lb_p]),
	print_or_log('    - Complexity: ~p~n ',[Asym_class1]);true).
	
	
closed_bound_print(Cost_max_min,Summary,UB1):-
	strexp_simplify_max_min(Cost_max_min,Cost_max_min_simple),
	strexp_to_cost_expression(Cost_max_min_simple,UB),
	cexpr_simplify(UB,Summary,UB1),!.
	
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_single_closed_result(+Entry:term,+Expr:cost_expression) is det
% print the given upper bound Expr and its asymptotic bound
print_single_closed_result(single_bound(Head,Expr)):-
	copy_term((Head,Expr),(Head_p,Expr_p)),
	get_asymptotic_class_name(Expr,Asym_class),
	ground_header(Head_p),
	print_header('Maximum cost of ~p: ',[Head_p],3),
	print_or_log('~p ~n',[Expr_p]),
	print_or_log('Asymptotic class: ~p ~n',[Asym_class]).

%! print_conditional_upper_bounds(+Head:term) is det
% print the conditional upper bounds
print_piecewise_bounds(Op,Piecewise_bounds):-
	copy_term(Piecewise_bounds,piecewise_bound(Head,Segments)),
	ground_header(Head),
	print_header('Piecewise ~p bound of ~p: ~n',[Op,Head],3),
	maplist(print_segment(Op),Segments),
	print_maximum_bound(Op,Segments).


print_segment(Op,((UB,LB),[Cond1|Conditions])):-
	(Op=upper->
		Bound=UB
		;
		Bound=LB
	),
	maplist(maplist(pretty_print_constr),[Cond1|Conditions],[Cond1_pretty|Conditions_pretty]),
	print_or_log('* ~p ~n if ~p~n',[Bound,Cond1_pretty]),
	maplist(print_partition_condition,Conditions_pretty).


print_partition_condition(Cond):-
	print_or_log(' or ~p~n',[Cond]).
	
print_maximum_bound(Op,Segments):-
	maplist(\Segment^UB^LB^(Segment=((UB,LB),_)),Segments,UBs,LBs),
	(Op=upper->
		Costs=UBs
		;
		Costs=LBs
	),
	get_asymptotic_class_name(max(Costs),Asym_class),
	print_or_log('Possible ~p bounds : ~p~n',[Op,Costs]),
	print_or_log('Maximum ~p bound complexity: ~p~n',[Op,Asym_class]).

	
ground_header(Head):-
   ground_equation_header(Head),!.
 ground_header(Head):- 
    numbervars(Head,0,_).

ground_rec_calls([],_).
ground_rec_calls([Call|Calls],N):-
	ground_header_prime(Call,N),
	N1 is N+1,
	ground_rec_calls(Calls,N1).
	
ground_header_prime(Head,N):-
	copy_term(Head,Head2),
	ground_header(Head2),
	Head2=..[F|Names],
	maplist(prime_name(N),Names,Namesp),
	Head=..[F|Maybe_vars],
	maplist(unify_if_possible,Maybe_vars,Namesp).

unify_if_possible(X,X):-!.
unify_if_possible(_,_):-!.	

prime_name(1,Name,Namep):-!,
	with_output_to(atom(Namep),format('~p\'',[Name])).
prime_name(N,Name,Namep):-N>1,!,
	with_output_to(atom(Namep),format('~p\'~p',[Name,N])).


	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
print_competition_result(single_bound(Expr)):-
	get_param(competition,[]),!,
	get_asymptotic_class_name(Expr,Asym_class),
	(Asym_class=infinity->
		format('MAYBE~n',[])
			;
		get_complexity_competition_name(Asym_class,Asym_class_comp),
		format('WORST_CASE(?,O(~p))  ~n',[Asym_class_comp])
	).
print_competition_result(piecewise_bound(_Head,Segments)):-
	get_param(competition,[]),!,
	maplist(\Segment^UB^(Segment=((UB,_),_)),Segments,UBs),
	get_asymptotic_class_name(max(UBs),Asym_class),
	(Asym_class=infinity->
		format('MAYBE~n',[])
			;
		get_complexity_competition_name(Asym_class,Asym_class_comp),
		format('WORST_CASE(?,O(~p))  ~n',[Asym_class_comp])
	).

print_competition_result(_).

get_complexity_competition_name(n,n^1):-!.
get_complexity_competition_name(constant,1):-!.
get_complexity_competition_name(Name,Name).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_help is det
% print information about the input parameters
print_help:-
	print_help_header,
	print_parameters_list.
%	format('~nExamples of use:~n~n',[]),
%	print_examples.

print_help_header:-
	format('~tCoFloCo~nUsage: cofloco [Options]~n where:~n',[]).

print_parameters_list:-
    param_description(Param,Description),
    findall(Name,parameter_dictionary(Name,Param,_),Names),
    format('~p  ~p ~n',[Names,Description]),
    fail.
print_parameters_list.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_stats is det
% print time statistics of the different phases of the analysis
print_stats:-
	(get_param(stats,[])->
	print_header('Time statistics:~p~n',[' '],2),
	profiling_get_info(pe,T_pe,_),
	profiling_get_info(inv,T_inv,_),
	profiling_get_info(inv_back,T_inv_back,_),
	profiling_get_info(inv_transitive,T_inv_transitive,_),
	profiling_get_info(unfold,T_unfold,_),
	profiling_get_info(ubs,T_ubs,_),

	profiling_get_info(loop_phases,T_loop_phases,_),
	profiling_get_info(chain_solver,T_chain_solver,_),
	profiling_get_info(equation_cost,T_equation_cost,_),
	
	profiling_get_info(solver,T_solver,_),
	profiling_get_info(termination,T_termination,_),
	
	%counter_get_value(compressed_phases1,N_compressed_phases1),
	%counter_get_value(compressed_invs,N_compressed_invs),
	%counter_get_value(compressed_chains,N_compressed_chains),
	print_or_log("* Partial evaluation computed in ~0f ms.~n",[T_pe]),
	print_or_log("* Invariants computed in ~0f ms.~n",[T_inv]),
	print_or_log("   - Backward Invariants ~0f ms.~n",[T_inv_back]),
	print_or_log("   - Transitive Invariants ~0f ms.~n",[T_inv_transitive]),
	print_or_log("* Refinement performed in ~0f ms.~n",[T_unfold]),
	print_or_log("* Termination proved in ~0f ms.~n",[T_termination]),
	print_or_log("* Upper bounds computed in ~0f ms.~n",[T_ubs]),
	print_or_log("   - Equation cost structures ~0f ms.~n",[T_equation_cost]),
	print_or_log("   - Phase cost structures ~0f ms.~n",[T_loop_phases]),
	print_or_log("   - Chain cost structures ~0f ms.~n",[T_chain_solver]),
	print_or_log("   - Solving cost expressions ~0f ms.~n",[T_solver]),
	%	print_or_log("~nCompressed phase information: ~p ~n",[N_compressed_phases1]),
	%	print_or_log("Compressed Chains: ~p ~n",[N_compressed_chains]),
	%	print_or_log("Compressed invariants: ~p ~n",[N_compressed_invs]).
	profiling_get_info(analysis,T_analysis,_),
	print_or_log("* Total analysis performed in ~0f ms.~n~n",[T_analysis])
	;
		((get_param(v,[N]),N>0) ->
	   		profiling_get_info(analysis,T_analysis,_),
			print_or_log("* Total analysis performed in ~0f ms.~n~n",[T_analysis])
		;
		true)
	).
	


print_stats.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! pretty_print_constr(+Constr:linear_constraint,-Simple_constr:linear_constraint) is det
% format a linear constraint so it is easily readable
pretty_print_constr(Constr,Simple_constr):-
	constraint_to_coeffs_rep(Constr, coeff_rep(Coeffs,Rel,B)),
	partition(is_negative_coeff,Coeffs,Neg,Pos),
	maplist(make_positive,Neg,Neg1),
	maplist(simplify_multipliers,Pos,Pos1),
	maplist(simplify_multipliers,Neg1,Neg2),
	(B=0->
	  Pos2=Pos1,
	  Neg3=Neg2
	;
	(B<0->
	 B1 is 0-B,
	 append(Pos1,[B1],Pos2),
	 Neg3=Neg2
	;
	 append(Neg2,[B],Neg3),
	 Pos2=Pos1
	)
	),
	write_sum(Pos2,Left),
	write_sum(Neg3,Right),
	Simple_constr=..[Rel,Left,Right].

is_negative_coeff(X*_Var):-
	number(X),X<0.
make_positive(X*Var,X1*Var):-
	X1 is 0-X.
simplify_multipliers(1*Var,Var):-!.
simplify_multipliers(X,X).