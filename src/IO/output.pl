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
          print_chain_simple/1,
		  print_chains_entry/2,
		  print_sccs/0,
		  print_merging_cover_points/3,
		  print_new_scc/2,
		  print_partially_evaluated_sccs/0,
		  print_equations_refinement/2,
		  print_loops_refinement/2,
		  print_external_pattern_refinement/2,
		  print_ranking_functions/1,
		  print_phase_termination_argument/4,
		  print_pending_set/2,
		  print_selected_pending_constraint/3,
		  print_new_phase_constraints/3,
		  print_product_strategy_message/3,
		  print_candidate_in_phase/3,
		  write_lin_exp_in_phase/3,
		  print_removed_redundant_constr_message/2,
		  print_joined_itvar_sets_message/1,
		  print_cycle_in_cstr_warning/0,
		  print_changed_to_chain_method_warning/1,
		  print_removed_possibly_redundant_cstrs/1,
		  print_removed_unresolved_cstrs_cycle/1, 
		  print_results/2,
		  print_phase_cost/4,
		  print_loops_costs/3,
		  print_single_closed_result/2,
		  print_competition_result/1,
		  print_log/0,
		  print_conditional_upper_bounds/1,
		  print_conditional_lower_bounds/1,
		  print_closed_results/2,
		  print_cost_structure/1,
		  print_aux_exp/1,
		  print_itvars_renaming/1,
		  print_stats/0]).

:- use_module('../db',[ground_equation_header/1,
						eq_refined/2,
						eq_ph/8,
						loop_ph/6,
						external_call_pattern/5,
						upper_bound/4,
						closed_upper_bound_print/3,
						closed_lower_bound_print/3,
						conditional_upper_bound/3,
						conditional_lower_bound/3,
						non_terminating_chain/3]).
:- use_module('../pre_processing/SCCs',[crs_scc/6,crs_residual_scc/2]).
:- use_module('../refinement/invariants',[backward_invariant/4]).
:- use_module('../refinement/chains',[chain/3]).
:- use_module('../ranking_functions',[
	ranking_function/4,
	partial_ranking_function/7]).
:- use_module('../bound_computation/phase_solver/phase_solver',[type_of_loop/2]).
:- use_module('../utils/cost_expressions',[get_asymptotic_class_name/2]).
:- use_module('../utils/cofloco_utils',[
			constraint_to_coeffs_rep/2,
			write_sum/2,
			tuple/3,
			ground_copy/2]).

:- use_module('../utils/cost_structures',[
	cstr_get_itvars/2,
	cstr_get_unbounded_itvars/2,
	itvar_recover_long_name/2,
	astrexp_to_cexpr/2]).


:- use_module('../IO/params',[parameter_dictionary/3,get_param/2,
		      param_description/2]).

:- use_module(stdlib(linear_expression),[write_le/2]).
:- use_module(stdlib(profiling),[profiling_get_info/3]).
:- use_module(stdlib(counters),[counter_get_value/2]).
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list),[contains_sl/2]).
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
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
	
ansi_format_aux(Options,Format,Args):-current_prolog_flag(dialect,swi),ansi_format(Options,Format,Args).
ansi_format_aux(_,Format,Args):-current_prolog_flag(dialect,yap),format(Format,Args).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

print_header(Text,Arguments,1):-
	print_or_log_nl,
	ansi_print_or_log([bold],Text,Arguments),
	print_or_log('=====================================~n',[]).
print_header(Text,Arguments,2):-
	print_or_log_nl,
	ansi_print_or_log([bold],Text,Arguments),
	print_or_log('-------------------------------------~n',[]).
print_header(Text,Arguments,3):-
	print_or_log_nl,
	ansi_print_or_log([bold],'###~p',[' ']),
	ansi_print_or_log([bold],Text,Arguments).
print_header(Text,Arguments,4):-
	print_or_log_nl,
	ansi_print_or_log([bold],'####~p',[' ']),
	ansi_print_or_log([bold],Text,Arguments).	
print_header(Text,Arguments,5):-
	print_or_log_nl,
	ansi_print_or_log([bold],'#####~p',[' ']),
	ansi_print_or_log([bold],Text,Arguments).	
print_header(Text,Arguments,6):-
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
	
print_sccs:-
	get_param(v,[X]),X > 1,!,
	print_header('Computed strongly connected components ~n',[],4),
	findall(scc(SCC_N,Type,Nodes,Entries,Info),
		(crs_scc(SCC_N,Type,Nodes,_SCC_Graph,Entries,Info),
		Nodes\=['$cofloco_aux_entry$'/0])
		,Sccs),
	maplist(print_scc,Sccs).
print_sccs.

print_scc(scc(SCC_N,Type,Nodes,_Entries,Info)):-
	(Info\=[] ->Info_print=Info;Info_print=''),
	print_or_log('~p. ~p ~p : ~p~n',[SCC_N,Type,Info_print,Nodes]).


print_new_scc(Entry,SCC_N):-
	get_param(v,[X]),X > 1,!,
	print_or_log('* The entry ~p is not a cutpoint so it becomes a new SCC ~p~n',[Entry,SCC_N]).

print_new_scc(_,_).
	
print_merging_cover_points(SCC_N,Cover_points,Merged):-
	get_param(v,[X]),X > 1,!,
	print_or_log('~p. SCC does not have a single cut point : ~p  ~n Merged into ~p~n',[SCC_N,Cover_points,Merged]).
print_merging_cover_points(_,_,_).	
	
print_partially_evaluated_sccs:-
	get_param(v,[X]),X > 1,!,
	print_header('Obtained direct recursion through partial evaluation ~n',[],4),
	findall(SCC_N,
		(crs_scc(SCC_N,_,Nodes,_,_,_),
		Nodes\=['$cofloco_aux_entry$'/0]
		)
		,Sccs),
	maplist(print_partially_evaluated,Sccs).
print_partially_evaluated_sccs.

print_partially_evaluated(SCC_N):-
	crs_residual_scc(SCC_N,Cover_point),!,
	print_or_log('~p. SCC is partially evaluated into ~p~n',[SCC_N,Cover_point]).	
print_partially_evaluated(SCC_N):-
	print_or_log('~p. SCC is completely evaluated into other SCCs~n',[SCC_N]).		
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%! print_equations_refinement(+Head:term,+RefCnt:int) is det
% print the calls from the SCC Head in the refinement phase RefCnt
% if the verbosity is high enough
print_equations_refinement(Head,RefCnt):-
	get_param(v,[X]),X > 1,!,
	functor(Head,Name,Arity),
	print_header('Specialization of cost equations ~p ~n',[Name/Arity],3),
	print_equations_refinement_1(Head,RefCnt),
	(X>2-> 
		RefCnt2 is RefCnt+1,
		print_header('Refined cost equations ~p ~n',[Name/Arity],4),
		print_refined_equations(Head,RefCnt2)
	;
		true
	).
print_equations_refinement(_,_).
	
print_equations_refinement_1(Head,RefCnt):-
	eq_ph(Head,(Eq_id,RefCnt),_,_,_,_,_,_),
	findall(Refined,
	        eq_refined(Eq_id,Refined),
	        Refined_list),
	(Refined_list\=[]-> 
		print_or_log('* CE ~p is refined into CE ~p ~n',[Eq_id,Refined_list])
		;
		print_or_log('* CE ~p is discarded (unfeasible) ~n',[Eq_id])
	),
	fail.
print_equations_refinement_1(_,_):-print_or_log_nl.

print_refined_equations(Head,RefCnt):-
	findall(Id,
	 eq_ph(Head,(Id,RefCnt),_,_,_,_,_,_),
	 Eqs),
	 maplist(pretty_print_CE,Eqs).

pretty_print_CE(Id):-
	eq_ph(Head,(Id,_),Cost,_NR_Calls,_Rec_Calls,Calls,Cs,_Non_Term),
	foldl(unify_equalities,Cs,[],Cs2),
	maplist(pretty_print_constr,Cs2,Cs3),
	ground_header(Head),
	Head=..[_|Var_names],
	max_var_number(Var_names,0,Max),InitN is Max+1,
	numbervars((Cost,Calls,Cs3),InitN,_),
	print_or_log('* CE ~p: ~p =~| ',[Id,Head]),
	print_cost_structure(Cost),
	pretty_print_refinedCalls(Calls,'+'),print_or_log_nl,
	print_or_log('     ~p ~n',[Cs3]).


pretty_print_refinedCalls([],_).
pretty_print_refinedCalls([(Call,external_pattern(Pattern))|Calls],Sep):-!,
	print_or_log('~a ~p',[Sep,Call:Pattern]),
	pretty_print_refinedCalls(Calls,Sep).
pretty_print_refinedCalls([(Call,chain(Chain))|Calls],Sep):-!,
	print_or_log('~a ~p',[Sep,Call:Chain]),
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
print_loops_refinement(Head,RefCnt):-
	get_param(v,[X]),X > 1,!,
	functor(Head,Name,Arity),
	print_header('Cost equations --> "Loop" of ~p ~n',[Name/Arity],3),
	print_loops_refinement_1(Head,RefCnt),
	(X>2-> 
		print_header('Loops of ~p ~n',[Name/Arity],4),
		print_refined_loops(Head,RefCnt)
	;
		true
	).
print_loops_refinement(_,_).
	
print_loops_refinement_1(Head,RefCnt):-
	loop_ph(Head,(Id,RefCnt),_,_,Eqs,_),
	print_or_log('* CEs ~p --> Loop ~p ~n',[Eqs,Id]),
	fail.
print_loops_refinement_1(_,_).	

print_refined_loops(Head,RefCnt):-
	loop_ph(Head,(Id,RefCnt),Calls,Cs,_Eqs,_),
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
	),	
	fail.	
print_refined_loops(_,_).

%! print_external_pattern_refinement(+Head:term,+RefCnt:int) is det
% print the correspondence between external patterns and chains from the SCC Head in the refinement phase RefCnt
% if the verbosity is high enough
print_external_pattern_refinement(Head,RefCnt):-
	get_param(v,[X]),X > 2,!,
	functor(Head,Name,Arity),
	print_header('Merging Chains  ~p into  External patterns of execution ~n',[Name/Arity],3),
	print_external_pattern_refinement_1(Head,RefCnt).
print_external_pattern_refinement(_,_).
	
print_external_pattern_refinement_1(Head,RefCnt):-
	external_call_pattern(Head,(Id,RefCnt),_,Components,_),
	maplist(reverse,Components,Components_rev),
	print_or_log('* ~p --> ~p ~n',[Components_rev,Id]),
	fail.
print_external_pattern_refinement_1(_,_):-print_or_log_nl.
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_ranking_functions(Head):-
	copy_term(Head,Head_print),
	get_param(v,[X]),X > 1,!,
	ground_header(Head_print),
	print_header('Ranking functions of CR ~p ~n',[Head_print],3),
	print_complete_ranking_functions(Head_print),
	print_header('Partial ranking functions of CR ~p ~n',[Head_print],4),
	print_partial_ranking_functions(Head_print),print_or_log_nl.
print_ranking_functions(_Head).

print_complete_ranking_functions(Head):-
	findall((Phase,Rf),
		(ranking_function(Head,Var,Phase,Rf),var(Var)),Unconditional_rfs),
	findall(((Phase,Prefix),Rf),
		(ranking_function(Head,Prefix,Phase,Rf),nonvar(Prefix)),Conditional_rfs),	
	from_pair_list_mm(Unconditional_rfs,Unconditional_rfs_mm),
	from_pair_list_mm(Conditional_rfs,Conditional_rfs_mm),

	maplist(print_rf,Unconditional_rfs_mm),
	maplist(print_conditional_rf,Conditional_rfs_mm).

print_rf((Phase,Rfs)):-
	maplist(write_le,Rfs,Rfs_print),
	print_or_log('* RF of phase ~p: ~p~n',[Phase,Rfs_print]).
print_conditional_rf(((Phase,Prefix),Rfs)):-
	maplist(write_le,Rfs,Rfs_print),
	print_or_log('* RF of phase ~p preceeded by ~p : ~p~n',[Phase,Prefix,Rfs_print]).	

print_partial_ranking_functions(Head):-
	findall((Phase,(Loop,(Rf,Deps))),
		(
		partial_ranking_function(Head,Var,Phase,Loop,Rf,Deps,_),
		var(Var)
		),Unconditional_rfs),
	findall(((Phase,Prefix),(Loop,(Rf,Deps))),
		(
		partial_ranking_function(Head,Prefix,Phase,Loop,Rf,Deps,_),
		nonvar(Prefix)
		),Conditional_rfs),	
	from_pair_list_mm(Unconditional_rfs,Unconditional_rfs_mm),
	from_pair_list_mm(Conditional_rfs,Conditional_rfs_mm),
	ground_header(Head),
	maplist(print_partial_rfs_for_phase,Unconditional_rfs_mm),
	maplist(print_conditional_partial_rfs_for_phase,Conditional_rfs_mm).	

print_partial_rfs_for_phase((Phase,Loop_rf_pairs)):-
	print_or_log('* Partial RF of phase ~p:~n',[Phase]),
	from_pair_list_mm(Loop_rf_pairs,Loop_rf_mm),
	maplist(print_partial_rfs_for_loop,Loop_rf_mm).
	

print_conditional_partial_rfs_for_phase(((Phase,Prefix),Loop_rf_pairs)):-
	print_or_log('  - RF of phase ~p preceeded by ~p :~n',[Phase,Prefix]),
	from_pair_list_mm(Loop_rf_pairs,Loop_rf_mm),
	maplist(print_partial_rfs_for_loop,Loop_rf_mm).
		
print_partial_rfs_for_loop((Loop,Rfs)):-
	print_or_log('  - RF of loop ~p:~n',[Loop]),
	maplist(print_partial_rf,Rfs).
	
print_partial_rf((Rf,[])):-!,
	write_le(Rf,Rf_print),
	print_or_log('    ~p~n',[Rf_print]).
print_partial_rf((Rf,Deps)):-
	Deps\=[],
	write_le(Rf,Rf_print),
	print_or_log('    ~p depends on loops ~p ~n',[Rf_print,Deps]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_phase_termination_argument(+Head:term,+Phase:phase,+Term_argument:termination_argument,+YesNo:flag) is det
% print the termination argument of Phase if Phase is an iterative phase and the verbosity
% is high enough
print_phase_termination_argument(Head,Phase,Term_argument,no):-
	get_param(v,[X]),X > 2,
	Phase=[_|_],
	copy_term((Head,Term_argument),(Head2,Term_argument2)),
	ground_header(Head2),
    print_or_log('~p: Phase ~p might not terminate:: ~p~n',[Head2,Phase,Term_argument2]).
print_phase_termination_argument(Head,Phase,Term_argument,yes):-
	get_param(v,[X]),X > 2,
	Phase=[_|_],
	copy_term((Head,Term_argument),(Head2,Term_argument2)),
	ground_header(Head2),
    print_or_log('~p: Phase ~p termination argument: ~p~n',[Head2,Phase,Term_argument2]).

print_phase_termination_argument(_Head,_Phase,_Term_argument,_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! print_chains_entry(+Entry:term,+RefCnt:int) is det
% print the inferred chains in SCC Entry in the refinement phase RefCnt
print_chains_entry(Entry,RefCnt):-
	get_param(v,[X]),X > 2,!,
	ground_header(Entry),
	print_header('Resulting Chains:~p ~n',[Entry],3),
	print_chains_entry_1(RefCnt,Entry).
print_chains_entry(_,_).

print_chains_entry_1(RefCnt,Entry):-
	chain(Entry,RefCnt,Pattern),
	print_or_log('* ',[]),
	print_chain_simple(Pattern),print_or_log_nl,
	fail.
print_chains_entry_1(_,_):-print_or_log_nl.


print_chain_simple(Pattern):-
	(non_terminating_chain(_,_,Pattern)->
	   ansi_print_or_log([fg(red)],'~p...',[Pattern])
	 ;
	   ansi_print_or_log([],'~p',[Pattern])
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


print_pending_set(Head,Pending):-
	get_param(debug,[]),!,
	copy_term((Head,Pending),(Head_gr,pending(Head_gr,Maxs_mins,Level_sums,Sums))),
    (pending(Head_gr,Maxs_mins,Level_sums,Sums)\=pending(_,[],[],[])->
		ground_header(Head_gr),
		print_header('Pending set ~p~n',[Head_gr],5),
		(Maxs_mins\=[]->
			maplist(tuple,_,Maxs_mins_cs,Maxs_mins),
			maplist(write_top_exp,Maxs_mins_cs,Max_mins_p),
			print_or_log('* Pmax/min: ~p~n',[Max_mins_p])
			;true),
		(Level_sums\=[]->	
			maplist(tuple,_,Level_sums_cs,Level_sums),
			maplist(write_top_exp,Level_sums_cs,Level_sums_p),
			print_or_log('* Plevel-sum: ~p~n',[Level_sums_p])
			;true
		),
		(Sums\=[]->
		maplist(print_pending_sum,Sums);
		true)
	;
		print_header('Empy Pending set: Done ~n',[],5)
	).
	
print_pending_set(_,_).	


print_pending_sum((Loop,loop_vars(Head,Calls),Sums)):-
	ground_header(Head),
	ground_rec_calls(Calls,1),
	maplist(tuple,_,Sums_cs,Sums),
	maplist(write_top_exp,Sums_cs,Sums_p),
	type_of_loop(Loop,Loop_type),
	print_or_log('* Psum in ~p ~p: ~p~n',[Loop_type,Loop,Sums_p]).

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

print_new_phase_constraints(loop_vars(Head,Calls),Fconstrs,Iconstrs):-
	get_param(debug,[]),!,
	copy_term((loop_vars(Head,Calls),Fconstrs,Iconstrs),(loop_vars(Head_gr,Calls_gr),Fconstrs_gr,Iconstrs_gr)),
	ground_header(Head_gr),
	ground_rec_calls(Calls_gr,1),
	maplist(write_top_exp,Fconstrs_gr,Fconstrs_print),
	maplist(write_aux_exp,Iconstrs_gr,Iconstrs_print),
	append(Iconstrs_print,Fconstrs_print,All_constrs),
	print_or_log(' * Adding constraints: ~p ~n',[All_constrs]).
print_new_phase_constraints(Head,Fconstrs,Iconstrs):-
	get_param(debug,[]),!,
	copy_term((Head,Fconstrs,Iconstrs),(Head_gr,Fconstrs_gr,Iconstrs_gr)),
	ground_header(Head_gr),
	maplist(write_top_exp,Fconstrs_gr,Fconstrs_print),
	maplist(write_aux_exp,Iconstrs_gr,Iconstrs_print),
	append(Iconstrs_print,Fconstrs_print,All_constrs),
	print_or_log(' * Adding constraints:~p ~n',[All_constrs]).	
	
print_new_phase_constraints(_,_,_).

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


print_loops_costs(Phase_feasible,Phase_vars,Costs):-
	get_param(v,[X]),X > 2,!,
	print_header('Cost of loops ~p ~n',[Phase_feasible],4),
	maplist(print_loop_cost,Phase_feasible,Phase_vars,Costs).
print_loops_costs(_,_,_).

print_loop_cost(Loop,loop_vars(Head,Calls),Cost):-
	get_param(v,[X]),X > 2,
	copy_term((Head,Calls,Cost),(Headp,Callsp,Costp)),
	ground_header(Headp),
	(
		Callsp==[]
		;
		ground_rec_calls(Callsp,1)
	),
	print_or_log('~n * loop ~p:~p -> ~p ~n',[Loop,Headp,Callsp]),
	print_cost_structure(Costp).


print_phase_cost(Phase,Head,Calls,Cost):-
	get_param(v,[X]),X > 2,
	copy_term((Head,Calls,Cost),(Headp,Callsp,Costp)),
	ground_header(Headp),
	(
		Callsp==[]
		;
		ground_rec_calls(Callsp,1)
	),
	print_header('Cost of phase ~p:~p -> ~p ~n',[Phase,Headp,Callsp],4),
	print_cost_structure(Costp).

print_phase_cost(_,_,_,_).


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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! print_results(+Entry:term,+RefCnt:int) is det
% print the chains, invariants and uppuer bounds of SCC Entry in the refinement phase RefCnt
print_results(Entry,RefCnt):-
	ground_header(Entry),
	print_header('Cost of chains of ~p:~n',[Entry],4),
	print_results_1(Entry,RefCnt).
print_results_1(Entry,RefCnt):-
	backward_invariant(Entry,(Chain,RefCnt),_,EPat),
	maplist(pretty_print_constr,EPat,EPat_pretty),
 	upper_bound(Entry,Chain,_,CExp),
 	print_or_log('* Chain ',[]),
	print_chain_simple(Chain),
	print_or_log(': ',[]),
	print_cost_structure(CExp),
	%print_cost_structure(CExp),
	print_or_log('~n  with precondition: ~p ~n~n',[EPat_pretty]),
 	fail.
print_results_1(_Entry,_).

	

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

%! print_closed_results(+Entry:term,+RefCnt:int) is det
% print the chains, invariants and closed upper bounds of SCC Entry in the refinement phase RefCnt	
print_closed_results(Entry,RefCnt):-
	copy_term(Entry,Entry_ground),
	ground_header(Entry_ground),
	print_header('Closed-form bounds of ~p: ~n',[Entry_ground],2),
	print_closed_results_1(Entry,RefCnt).

print_closed_results_1(Entry,RefCnt):-
	backward_invariant(Entry,(Chain,RefCnt),_,EPat),
	maplist(pretty_print_constr,EPat,EPat_pretty),
	(get_param(compute_ubs,[])->
 	    closed_upper_bound_print(Entry,Chain,CExp),
 	    get_asymptotic_class_name(CExp,Asym_class)
 	    ;
 	    true
 	 ),
 	(get_param(compute_lbs,[])->
 		closed_lower_bound_print(Entry,Chain,CExp_lb),
		get_asymptotic_class_name(CExp_lb,Asym_class1)
		;
		true
	),
	ground_header(Entry),
	print_or_log('* Chain ',[]),
	print_chain_simple(Chain),
	print_or_log(' with precondition: ~p ~n',[EPat_pretty]),
	(get_param(compute_ubs,[])->
	print_or_log('    - Upper bound: ~p ~n',[CExp]),
	print_or_log('    - Complexity: ~p ~n',[Asym_class]);true),
	(get_param(compute_lbs,[])->
	print_or_log('    - Lower bound: ~p ~n',[CExp_lb]),
	print_or_log('    - Complexity: ~p~n ',[Asym_class1]);true),
 	fail.
print_closed_results_1(_Entry,_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_single_closed_result(+Entry:term,+Expr:cost_expression) is det
% print the given upper bound Expr and its asymptotic bound
print_single_closed_result(Entry,Expr):-
	copy_term((Entry,Expr),(Entry2,Expr2)),
	get_asymptotic_class_name(Expr,Asym_class),
	ground_header(Entry2),
	print_header('Maximum cost of ~p: ',[Entry2],3),
	print_or_log('~p ~n',[Expr2]),
	print_or_log('Asymptotic class: ~p ~n',[Asym_class]).

%! print_conditional_upper_bounds(+Head:term) is det
% print the conditional upper bounds
print_conditional_upper_bounds(Head):-
	copy_term(Head,Head2),
	ground_header(Head2),
	print_header('Partitioned upper bound of ~p: ~n',[Head2],3),
	print_conditional_upper_bound(Head),
	print_maximum_upper_bound(Head).

print_conditional_upper_bound(Head):-
	conditional_upper_bound(Head,Cost,[Cond1|Conditions]),
	maplist(maplist(pretty_print_constr),[Cond1|Conditions],[Cond1_pretty|Conditions_pretty]),
	ground_header(Head),
	print_or_log('* ~p ~n if ~p~n',[Cost,Cond1_pretty]),
	maplist(print_partition_condition,Conditions_pretty),
	fail.
print_conditional_upper_bound(_).	

%! print_conditional_lower_bounds(+Head:term) is det
% print the conditional lower bounds
print_conditional_lower_bounds(Head):-
	copy_term(Head,Head2),
	ground_header(Head2),
	print_header('Partitioned lower bound of ~p: ~n',[Head2],3),
	print_conditional_lower_bound(Head),
	print_maximum_lower_bound(Head).

print_conditional_lower_bound(Head):-
	conditional_lower_bound(Head,Cost,[Cond1|Conditions]),
	maplist(maplist(pretty_print_constr),[Cond1|Conditions],[Cond1_pretty|Conditions_pretty]),
	ground_header(Head),
	print_or_log('* ~p ~n if ~p~n',[Cost,Cond1_pretty]),
	maplist(print_partition_condition,Conditions_pretty),
	fail.
print_conditional_lower_bound(_).


print_maximum_upper_bound(Head):-
	copy_term(Head,Head2),
	bagof(Cost,
		Conds^conditional_upper_bound(Head2,Cost,Conds),
		Costs),
	get_asymptotic_class_name(max(Costs),Asym_class),
	ground_header(Head2),
	print_or_log('Possible upper bounds : ~p~n',[Costs]),
	print_or_log('Maximum upper bound complexity: ~p~n',[Asym_class]).

print_maximum_lower_bound(Head):-
	copy_term(Head,Head2),
	bagof(Cost,
		Conds^conditional_lower_bound(Head2,Cost,Conds),
		Costs),
	get_asymptotic_class_name(max(Costs),Asym_class),
	ground_header(Head2),
	print_or_log('Possible lower bounds : ~p~n',[Costs]),
	print_or_log('Maximum lower bound complexity: ~p~n',[Asym_class]).

print_partition_condition(Cond):-
	print_or_log(' or ~p~n',[Cond]).
	
	
	
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
print_competition_result(Expr):-
	get_param(competition,[]),!,
	get_asymptotic_class_name(Expr,Asym_class),
	(Asym_class=infinity->
		format('MAYBE~n',[])
			;
		get_complexity_competition_name(Asym_class,Asym_class_comp),
		format('WORST_CASE(?,O(~p))  ~n',[Asym_class_comp])
	).
print_competition_result(_Expr).


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