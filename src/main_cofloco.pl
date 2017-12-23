/* 
Part of CoFloCo

@author Antonio Flores Montoya

@copyright Copyright (C) 2014-2017 Antonio Flores Montoya

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

:- module(main_cofloco,[cofloco_shell_main/0,cofloco_bin_main/0,cofloco_query/2,cofloco_query/1]).

/** <module> main_cofloco

The analysis has three main phases:
  * preprocessing: 
    * read the cost equations from an input file
    * detect the SCC (strongly connected components)
    * partially evaluate each SCC to obtain direct recursion
  * refinement: refine the abstract representation. 
    the refinement goes form the outmost SCC to the innermost SCC and back to the outmost SCC.  
    for each SCC:
     * infer the possible execution patterns (chains)
     * infer invariants and discard infeasible patterns
     * infer ranking functions and prove termination    
  * upper bound computation: the upper bound computation computes upper 
    bounds for all the chains of each SCC starting from the innermost
    up to the outmost SCC.  
    For the outmost SCC it also computes the closed form of the upper bound.


The main "data types" used in CoFloCo are the following:
  * list_set(A): list(A) a sorted list (with the standard order of elements) and without duplicates
    as defined in the library set_list.
  
  * list_map(A,B): list((A,B)) a map where A is the key and B is the value.
    The pairs are sorted according to A.
    as defined in the library list_map.
    
  * multimap(A,B): list((A,list_set(B))) a multimap where A is the key and B is a set of values.
    The pairs are sorted according to A.
    as defined in the library multimap.
    
  * term: functor(Var1,Var2,...VarN)
    Usually used to represent the head of a cost equation
    
  * equation_id: int
    Unique identifier for a cost equation   
    
  * phase: list_set(equation_id) | equation_id
    A phase can be of two kinds:
    * A simple phase X consist on a cost equation X executed once
    * An interative phase [X1,X2,...XN] consists on a set of cost equations X1,X2,...,XN that call each other a positive number of times.
      The regular expression that represents such a phase is (X1 \/ X2 \/...\/ XN)^+ where \/ is OR. 
          
  * chain: list(phase)
    A chain is a sequence of phases that are executed one after another.
    The sequence of phases are stored in inverse order. The head of the list is the base case
    and the last element is the one executed first.
      
  * rel_op: >= |  =< | =
   
  * normal_linear_expression: list((Coeff,Var))+ Coeff
    as defined in the module costa_stdlib/math/linear_expression
    Coeff is a rational.
    we abbreviate them as nlin_exp
    
  * linear_expression: N0+N1*X1+N1*X1+... +NN*XN where N0..NN are rationals and X1...XN variables
  
  * linear_constraint: linear_expression rel_op linear_expression
    If the linear constraint is normalized, it has the form:
    linear_expression rel_op number

  * polyhedron: list(linear_constraint)
    A polyhedron is expressed with the constraints representation
    
  * cost_structure: See 'utils/cost_structures.pl'


@author Antonio Flores Montoya

*/

:-include('search_paths.pl').


:- use_module(db,[init_db/0,init_timers/0]).
:- use_module('pre_processing/SCCs',[
	compute_sccs_and_btcs/3,
	scc_get_cover_points/2]).
:- use_module('pre_processing/partial_evaluation',[partial_evaluation/4]).

:- use_module('refinement/invariants',[
	compute_backward_invariants/3,
	compute_forward_invariants/4,
	compute_phases_transitive_closures/3,
	fwd_invs_get_loop_invariants/2,
	fwd_invs_get_infeasible_prefixes/2,
	fwd_invs_update_with_discarded_loops/3,
	loop_invs_to_CE_invs/3,
	back_invs_get_infeasible/2,
	back_invs_update_with_changed_chains/3,
	back_invs_get_loop_invariants/2
	]).
:- use_module('refinement/unfolding',[
	cr_specialize/3,
	cr_compute_external_execution_patterns/4]). 
:- use_module('refinement/chains',[
	compute_chains/2,
	chains_discard_terminating_non_terminating/3,
	chains_discard_infeasible_prefixes/4,
	chains_update_with_discarded_loops/4,
	chains_annotate_termination/3,
	chains_discard_infeasible/4,
	chains_discard_infeasible_combinations/5
	]).
:- use_module('refinement/loops',[
	compute_loops/3,
	compute_phase_loops/3,
	loops_strengthen_with_loop_invs/5
	]).


:- use_module(ranking_functions,[
	find_loops_ranking_functions/3,
	prove_phases_termination/4
	]).


:- use_module('bound_computation/bounds_main',[
	cr_compute_bounds/4,
	compute_closed_bound/1,
	compute_single_closed_bound/3
	]).
:- use_module('bound_computation/conditional_bounds',[compute_conditional_bounds/1]).			  

:- use_module('IO/output',[
	init_output/0,
	print_header/3,
	print_or_log/2,
	print_results/2,
	print_sccs/1,
	print_partially_evaluated_sccs/1,
	print_equations_refinement/1,
	print_loops/1,
	print_external_patterns/1,
	print_ranking_functions/2,
	print_termination_arguments/1,
	print_changes_map/2,
	
	print_help/0,
	print_closed_results/2,
	print_chains/1,
	print_single_closed_result/2,
	print_competition_result/1,
	print_conditional_upper_bounds/1,
	print_conditional_lower_bounds/1,
	print_stats/0,
	print_log/0,
	print_help/0
	]).
:-use_module('IO/input',[
	read_cost_equations/2,
	store_cost_equations/2]).
:-use_module('IO/params',[
	set_default_params/0,
	set_competition_params/0,
	parse_params/1,
	get_param/2
	]).
:-use_module('utils/cost_structures',[init_cost_structures/0]).

:-use_module('utils/crs',[
	cr_set_external_patterns/3,
	cr_get_external_patterns/2,
	cr_get_loops/2,
	cr_set_loops/3,
	cr_set_chains/3,
	cr_get_forward_invariant/2,
	cr_strengthen_with_CE_invs/4,
	cr_IOvars/2,
	
	crs_get_cr/3,
	crs_IOvars/3,		
	crs_update_cr_forward_invariant/4,
	crs_update_forward_invariants_with_calls_from_cr/3,
	crs_update_cr/4,
	cr_strengthen_with_ce_invs/5]).

:-use_module('utils/cofloco_utils',[tuple/3]).

:- use_module(stdlib(set_list),[contains_sl/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_set_domain/1]).
:- use_module(stdlib(profiling),[
	profiling_start_timer/1,
	profiling_get_info/3,
	profiling_stop_timer/2,
	profiling_stop_timer_acum/2]).
	
:- use_module(stdlib(counters),[
	counter_get_value/2,
	counter_initialize/2]).
	
:-use_module(stdlib(polyhedra_ppl),[ppl_my_initialize/0]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(lambda)).

%! cofloco_shell_main is det
% main predicate to be called form the console.  
% it performs the complete analysis
cofloco_shell_main:-
        current_prolog_flag(argv, Args),
	   (Args=[_|_]->
	    catch(cofloco_query(Args),E,(print_message(error, E),halt))
	   ;
	    print_help
	   ),
	   halt.
cofloco_bin_main:-
        current_prolog_flag(argv, [_|Args]),
	   (Args=[_|_]->
	    catch(cofloco_query(Args),E,(print_message(error, E),halt))
	   ;
	    print_help
	   ),
	   halt.
%! save_executable is det
% build an executable file of cofloco
%save_executable:-
%	ppl_my_initialize,
%	make,
%	check,
%	prolog_history(disable),
%	qsave_program('cofloco',[stand_alone(true),goal(main_cofloco:cofloco_shellco_main),foreign(save)]),
%	writeln('Binary package generated').

%! cofloco_query(+Eqs:list(cost_equation),+Params:list(atom)) is det
% perform the main analysis on the equations Eqs with the parameters Params
cofloco_query(Eqs,Params):-
	cofloco_query_part1(Params),
	store_cost_equations(Eqs,CRSE),
	cofloco_query_part2(CRSE).

	
%! cofloco_query(+Params:list(atom)) is det
% Obtains the input file, read the cost equations, preprocess the cost equations,
% perform the main analysis and print results
cofloco_query(Params):-
	cofloco_query_part1(Params),
	(get_param(input,[File])->
		(read_cost_equations(File,CRSE)->
			true
			;
			throw(error('Failed to parse input file'))
		),	
		cofloco_query_part2(CRSE)
	;
		(get_param(help,[])->
		   print_help
		;
		   throw(error('No input file given'))
		)
	).

cofloco_query_part1(Params):-
	set_default_params,
	init_database,
	parse_params(Params),
	conditional_call(get_param(competition,[]),set_competition_params),
	init_timers,
	profiling_start_timer(analysis).

cofloco_query_part2(CRSE):-
	get_param(incremental,[]),!,
	conditional_call((get_param(v,[N]),N>0),print_header('Preprocessing Cost Relations~n',[],1)),
	preprocess_cost_equations(CRSE,SCCs,Ignored_crs,CRSE2),
	conditional_call((get_param(v,[N]),N>0),print_header('Incremental solution of Cost Relations~n',[],1)),
	incremental_refinement_bounds(CRSE2,SCCs,Ignored_crs),
	profiling_stop_timer(analysis,_T_analysis),
	print_stats,
	print_log.

cofloco_query_part2(CRSE):-
	conditional_call((get_param(v,[N]),N>0),print_header('Preprocessing Cost Relations~n',[],1)),
	preprocess_cost_equations(CRSE,SCCs,Ignored_crs,CRSE2),
	conditional_call((get_param(v,[N]),N>0),print_header('Control-Flow Refinement of Cost Relations~n',[],1)),
	refinement(CRSE2,SCCs,Ignored_crs,CRSE3),
	(get_param(only_termination,[])->
			true
			;
			conditional_call((get_param(v,[N]),N>0),print_header('Computing Bounds~n',[],1)),
			bounds(CRSE3,SCCs,Ignored_crs),
			profiling_stop_timer(analysis,_T_analysis),
			print_stats
	),
	print_log.
%! init_database is det
% erase all the information from previous analyses	
init_database:-
	init_output,
	init_cost_structures.
	
%! preprocess_cost_equations is det
% Computes the SCC (strongly connected components)
% Performs partial evaluation to obtain direct recursion
preprocess_cost_equations(CRSE,SCCs,Ignored_CRS,CRSE3):-
	profiling_start_timer(comp_sccs),
	compute_sccs_and_btcs(CRSE,SCCs,CRSE2),
	print_sccs(SCCs),
	profiling_stop_timer(comp_sccs,_),
	profiling_start_timer(pe),
	partial_evaluation(CRSE2,SCCs,Ignored_CRS,CRSE3),
	print_partially_evaluated_sccs(SCCs),
	profiling_stop_timer(pe,_).

%! refinement is det
% perform the top_down analysis followed
% by the bottom_up analysis
refinement(CRSE,SCCs,Ignored_crs,CRSE2):-
	CRSE=crse(Entries,CRS),
	foldl(\Entry^CRS1_l^CRS2_l^
	 		(
	 		Entry=entry(Head,Cs),
	 		crs_update_cr_forward_invariant(CRS1_l,Head,Cs,CRS2_l)
	 		),Entries,CRS,CRS2),
	reverse(SCCs,SCCs_rev),
	top_down_refinement(SCCs_rev,CRS2,Ignored_crs,CRS3),
	bottom_up_refinement(SCCs,CRS3,Ignored_crs,CRS4),
	CRSE2=crse(Entries,CRS4).

%! top_down_refinement(+SCC_N:int) is det
% Start from the outmost SCC and goes down until the innermost
% For each SCC, it calls top_down_refinement_scc/1

top_down_refinement([],CRS,_Ignored_crs,CRS).
top_down_refinement([SCC|SCCs],CRS,Ignored_crs,CRS_out):-
	scc_get_cover_points(SCC,[F/A]),\+contains_sl(Ignored_crs,F/A),!,
	crs_get_cr(CRS,F,CR),
	top_down_refinement_scc(CR,CR2),
	crs_update_forward_invariants_with_calls_from_cr(CRS,CR2,CRS2),
	crs_update_cr(CRS2,F,CR2,CRS3),
	top_down_refinement(SCCs,CRS3,Ignored_crs,CRS_out).
top_down_refinement([_SCC|SCCs],CRS,Ignored_crs,CRS_out):-
	top_down_refinement(SCCs,CRS,Ignored_crs,CRS_out).


%! bottom_up_refinement(+SCC_N:int,+Max_SCC_N:int) is det
% Start from the innermost SCC and goes up until the outmost SCC
% For each SCC, it calls bottom_up_refinement_scc/1
bottom_up_refinement([],CRS,_Ignored_crs,CRS).
bottom_up_refinement([SCC|SCCs],CRS,Ignored_crs,CRS_out):-
	scc_get_cover_points(SCC,[F/A]),\+contains_sl(Ignored_crs,F/A),!,
	crs_get_cr(CRS,F,CR),
	bottom_up_refinement_scc(CR,CRS,CR2),
	crs_update_cr(CRS,F,CR2,CRS2),
	bottom_up_refinement(SCCs,CRS2,Ignored_crs,CRS_out).
bottom_up_refinement([_SCC|SCCs],CRS,Ignored_crs,CRS_out):-
	bottom_up_refinement(SCCs,CRS,Ignored_crs,CRS_out).


%! top_down_refinement_scc(+Head:term) is det
% Computes chains for a SCC defined by Head
% Computes forward invariants for the generated chains and add the invariants
% to the cost equations
top_down_refinement_scc(CR,CR3):-
	profiling_start_timer(unfold),
	(get_param(compress_chains,[N_compress])->true;N_compress=0),
	compute_loops(CR,N_compress,Loops),
	compute_chains(Loops,Chains),
	compute_phase_loops(Loops,Chains,Chains_annotated),
	profiling_stop_timer_acum(unfold,_),
	cr_get_forward_invariant(CR,Initial_fwd_inv),
	compute_forward_invariants(Initial_fwd_inv,Loops,Chains_annotated,Fwd_invs),
	fwd_invs_get_loop_invariants(Fwd_invs,Loop_invs),
	loop_invs_to_CE_invs(Loop_invs,Loops,CE_invs),

	%fwd_invs_get_infeasible_prefixes(Fwd_invs,Infeasible_prefixes),
	%chains_discard_infeasible_prefixes(Chains_annotated,Infeasible_prefixes,Chains2),
	cr_strengthen_with_ce_invs(CR,head,CE_invs,CR3,_Discarded).

%! bottom_up_refinement_scc(+Head:term) is det
%  *  Unfold the SCC defined by Head according to its calls to other SCC 
%  *  that have been already refined. 
%  *  Compute Chains 
%  *  Find ranking functions and prove termination of the chains
%  *  Remove impossible chains
%  *  Compute forward and backwards invariants
bottom_up_refinement_scc(CR,CRS,CR7) :-
	cr_IOvars(CR,IOvars),
	profiling_start_timer(unfold),
	cr_specialize(CR,CRS,CR2),
	print_equations_refinement(CR2), 
	(get_param(compress_chains,[N_compress])->true;N_compress=0),
	compute_loops(CR2,N_compress,Loops),
	
	print_loops(Loops),
	
	compute_chains(Loops,Chains),
	chains_annotate_termination(Chains,Loops,Chain4print),
	print_chains(Chain4print),
	compute_phase_loops(Loops,Chains,Chains_annotated),
	
	profiling_stop_timer_acum(unfold,_),
	
	profiling_start_timer(inv),
	
	cr_get_forward_invariant(CR,Initial_fwd_inv),
	compute_forward_invariants(Initial_fwd_inv,Loops,Chains_annotated,Fwd_invs),
	fwd_invs_get_infeasible_prefixes(Fwd_invs,Infeasible_prefixes),
	chains_discard_infeasible_prefixes(Chains_annotated,Infeasible_prefixes,Chains2,Changes_fwd_invs),
	print_changes_map('calling contexts',Changes_fwd_invs),
	
	fwd_invs_get_loop_invariants(Fwd_invs,Loop_invs),
	loops_strengthen_with_loop_invs(Loops,head,Loop_invs,Loops2,Discarded_loops),
	%the discarded loops won't generate CE invs and therefore we discard the corresponding CEs
	loop_invs_to_CE_invs(Loop_invs,Loops2,CE_invs),
	%FIXME: we assume no additional CEs are discarded
	% I am not 100% sure of this assumption
	cr_strengthen_with_ce_invs(CR2,head,CE_invs,CR3,_Discarded_CEs),

	chains_update_with_discarded_loops(Chains2,Discarded_loops,Chains3,Changes_fwd_invs_loops),
	print_changes_map('discarded loop because of calling context strengthening',Changes_fwd_invs_loops),
	fwd_invs_update_with_discarded_loops(Fwd_invs,Discarded_loops,Fwd_invs2),
	
	
	profiling_stop_timer_acum(inv,_),
	profiling_start_timer(termination),
	
	find_loops_ranking_functions(IOvars,Loops2,Loops3),
	prove_phases_termination(Chains3,IOvars,Loops3,Chains4),

	print_ranking_functions(Loops3,Chains4),
	print_termination_arguments(Chains4),
	
	chains_discard_terminating_non_terminating(Chains4,Chains5,Changes_map_termination),
	print_changes_map('termination proving',Changes_map_termination),
	
	profiling_stop_timer_acum(termination,_),
	profiling_start_timer(inv),	

	profiling_start_timer(inv_back),
	compute_backward_invariants(Loops3,Chains5,Backward_invs),
	back_invs_get_infeasible(Backward_invs,Infeasible_chains),
	chains_discard_infeasible(Chains5,Infeasible_chains,Chains6,Changes_map),
	print_changes_map('infeasible summaries',Changes_map),
	back_invs_update_with_changed_chains(Backward_invs,Changes_map,Backward_invs2),
	chains_discard_infeasible_combinations(Chains6,Backward_invs2,Fwd_invs2,Chains7,Changes_map2),
	print_changes_map('infeasible calling context-summary combination',Changes_map2),
	back_invs_update_with_changed_chains(Backward_invs2,Changes_map2,Backward_invs3),
	
	profiling_stop_timer_acum(inv_back,_),
	
	
	
	back_invs_get_loop_invariants(Backward_invs3,Loop_call_invs),
	loops_strengthen_with_loop_invs(Loops3,call,Loop_call_invs,Loops4,Discarded_loops2),
	loop_invs_to_CE_invs(Loop_call_invs,Loops4,CE_call_invs),
	cr_strengthen_with_ce_invs(CR3,call,CE_call_invs,CR4,_Discarded_CEs2),
	
	chains_update_with_discarded_loops(Chains7,Discarded_loops2,Chains8,Changes_map4),
	print_changes_map('infeasible loops because of summary strengthening',Changes_map4),
	back_invs_update_with_changed_chains(Backward_invs3,Changes_map4,Backward_invs4),
	
	
	cr_set_loops(CR4,Loops4,CR5),
	chains_annotate_termination(Chains8,Loops4,Chains9),
	compute_phases_transitive_closures(Chains9,Loops4,Chains10),
	print_chains(Chains10),
	cr_set_chains(CR5,Chains10,CR6),
	(get_param(compress_chains,[Compress_param])->
		true
		;
		Compress_param=0
	),
	cr_compute_external_execution_patterns(Chains10,Backward_invs4,Compress_param,External_patterns),
	cr_set_external_patterns(CR6,External_patterns,CR7),
	print_external_patterns(External_patterns).
	
	%profiling_start_timer(inv_transitive),
	%compute_loops_transitive_closures(Head,RefCnt),
	%profiling_stop_timer_acum(inv_transitive,_),

	
%! upper_bounds is det
% compute upper bounds for all SCC and a closed upper bounds for the entry SCC
bounds(CRSE,SCCs,Ignored_crs):-
    profiling_start_timer(ubs),
    bottom_up_bounds(SCCs,CRSE,Ignored_crs,CRSE2), 
    CRSE=crse(Entries,_CRS),
    maplist(\Entry^(Entry=entry(Head,_Cs),compute_closed_bound_scc(Head,CRSE2)),Entries),
    profiling_stop_timer_acum(ubs,_).
   
%! bottom_up_upper_bounds(+SCC_N:int,+Max_SCC_N:int) is det
% Start from the innermost SCC and goes up until the outmost SCC
% For each SCC, it computes the upper bound


	
bottom_up_bounds([],CRSE,_Ignored_crs,CRSE).

bottom_up_bounds([SCC|SCCs],CRSE,Ignored_crs,CRSE_final):-
	scc_get_cover_points(SCC,[F/A]),\+contains_sl(Ignored_crs,F/A),!,
	functor(Head,F,A),
	(SCCs=[]-> Last=true;Last=false),
	CRSE=crse(Entries,CRS),
	cr_compute_bounds(F,CRS,Last,CRS2),
	CRSE2=crse(Entries,CRS2),
	copy_term(Head,Head_aux),
	conditional_call((get_param(v,[N]),N>1),
		  print_results(Head_aux,CRS2)
		 ),
	bottom_up_bounds(SCCs,CRSE2,Ignored_crs,CRSE_final).

bottom_up_bounds([_SCC|SCCs],CRSE,Ignored_crs):-
	bottom_up_bounds(SCCs,CRSE,Ignored_crs).



compute_closed_bound_scc(Head) :-	
	copy_term(Head,Head_aux),
	profiling_start_timer(solver),
	compute_closed_bound(Head),
	profiling_stop_timer_acum(solver,_),
	conditional_call((get_param(v,[N]),N>0),	
		 print_closed_results(Head,2)
		),	
	((get_param(conditional_ubs,[]); get_param(conditional_lbs,[]))->
	   compute_conditional_bounds(Head_aux),
	   ((get_param(compute_ubs,[]),get_param(conditional_ubs,[]))->print_conditional_upper_bounds(Head_aux);true),
	   ((get_param(compute_lbs,[]),get_param(conditional_lbs,[]))->print_conditional_lower_bounds(Head_aux);true)
	   ;
	   (get_param(compute_ubs,[])->
	     compute_single_closed_bound(Head_aux,2,Exp),
	     print_single_closed_result(Head_aux,Exp),
	     print_competition_result(Exp)
	     ; true)
	).
	
% compute the refinement and upper bound one cost relation (SCC) at a time
incremental_refinement_bounds(CRSE,SCCs,Ignored_crs):-
	CRSE=crse(Entries,_CRS),
	maplist(\Entry^(Entry=entry(Head,Cs),add_scc_forward_invariant(Head,0,Cs)),Entries),
	reverse(SCCs,SCCs_rev),
	top_down_refinement(SCCs_rev,CRSE,Ignored_crs,CRSE2),	
	bottom_up_refinement_bounds(SCCs,CRSE2,Ignored_crs).
	
	
bottom_up_refinement_bounds([],_CRSE,_Ignored_crs).

bottom_up_refinement_bounds([SCC|SCCs],CRSE,Ignored_crs):-
	scc_get_cover_points(SCC,[F/A]),\+contains_sl(Ignored_crs,F/A),!,
	functor(Head,F,A),
	bottom_up_refinement_scc(Head),
	(SCCs=[]-> Last=true;Last=false),
	CRSE=crs(_Entries,CRS),
	crs_IOvars(CRS,F,IOvars),
	compute_bound_for_scc(Head,IOvars,2,Last),
	copy_term(Head,Head_aux),
	conditional_call((get_param(v,[N]),N>1),
		  print_results(Head_aux,2)
		 ),
	CRSE=crse(Entries,_CRS),
	(member(entry(Head,_),Entries) ->
		compute_closed_bound_scc(Head)
		;
		true
	),  
	bottom_up_refinement_bounds(SCCs,CRSE,Ignored_crs).

bottom_up_refinement_bounds([_SCC|SCCs],CRSE,Ignored_crs):-
	bottom_up_refinement_bounds(SCCs,CRSE,Ignored_crs).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%auxiliary predicates

	

conditional_call(Condition,Call):-
	(call(Condition)->
	   call(Call)
	   ;
	   true).

