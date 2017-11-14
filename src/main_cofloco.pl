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
     * infer invariants and discard unfeasible patterns
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


:- module(main_cofloco,[cofloco_shell_main/0,cofloco_bin_main/0,cofloco_query/2,cofloco_query/1]).
:-include('search_paths.pl').


:- use_module(db,[init_db/0,init_timers/0]).
:- use_module('pre_processing/SCCs',[compute_sccs_and_btcs/3,scc_get_cover_points/2]).
:- use_module('pre_processing/partial_evaluation',[partial_evaluation/4]).

:- use_module('refinement/invariants',[compute_invariants_for_scc/2,
			  compute_forward_invariants/2,
			  clean_invariants/0,
			  add_scc_forward_invariant/3,
			  backward_invariant/4
			  ]).
:- use_module('refinement/unfolding',[unfold_calls/2,
			 reinforce_equations_with_forward_invs/2,
			 remove_terminating_non_terminating_chains/2,
			 compress_chains_execution_patterns/2]). 
:- use_module('refinement/chains',[compute_chains/2,chain/3,init_chains/0]).
:- use_module('refinement/loops',[compute_loops/2,compute_phase_loops/2]).


:- use_module(ranking_functions,[init_ranking_functions/0,find_ranking_functions/3]).
:- use_module(termination_checker,[init_termination/0,prove_termination/2]).

:- use_module('bound_computation/bounds_main',[compute_bound_for_scc/3,
				  compute_closed_bound/1,
				  compute_single_closed_bound/3]).
:- use_module('bound_computation/conditional_bounds',[
				  compute_conditional_bounds/1]).			  
:- use_module('bound_computation/phase_solver/phase_solver',[init_phase_solver/0]).
:- use_module('bound_computation/cost_equation_solver',[init_cost_equation_solver/0]).    
:- use_module('bound_computation/chain_solver',[init_chain_solver/0]).    

:- use_module('IO/output',[
			  init_output/0,
			  print_header/3,
			  print_or_log/2,
			  print_results/2,
			  print_sccs/1,
			  print_partially_evaluated_sccs/1,
	          print_equations_refinement/2,
	          print_loops_refinement/2,
	          print_external_pattern_refinement/2,
	          print_ranking_functions/1,
		      print_help/0,
		      print_closed_results/2,
		      print_chains_entry/2,
		      print_single_closed_result/2,
		      print_competition_result/1,
		      print_conditional_upper_bounds/1,
		      print_conditional_lower_bounds/1,
		      print_stats/0,
		      print_log/0,
		      print_help/0]).
:- use_module('IO/input',[read_cost_equations/2,store_cost_equations/2]).
:-use_module('IO/params',[set_default_params/0,set_competition_params/0,parse_params/1,get_param/2]).
:-use_module('utils/cost_structures',[init_cost_structures/0]).

:-use_module('utils/crs',[crs_IOvars/3]).

:-use_module('utils/cofloco_utils',[tuple/3]).

:- use_module(stdlib(set_list),[contains_sl/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_set_domain/1]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_get_info/3,
				 profiling_stop_timer/2,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_get_value/2,counter_initialize/2]).
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
	parse_params(Params),
	conditional_call(get_param(competition,[]),set_competition_params),
	init_timers,
	init_database,
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
	trace,
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
	init_db,
	init_ranking_functions,
	init_termination,
	init_chains,
	clean_invariants,
	init_phase_solver,
	init_cost_equation_solver,
	init_chain_solver,
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
	foldl(\Entry^CRS_l^CRS2_l^
	 		(
	 		Entry=entry(Head,Cs),
	 		crs_add_cr_forward_invariant(CRS_l,Head,Cs,CRS2_l)
	 		),Entries,CRS,CRS2),
	reverse(SCCs,SCCs_rev),
	top_down_refinement(SCCs_rev,CRS2,Ignored_crs,CRS3),
	bottom_up_refinement(SCCs,CRS3,Ignored_crs,CRS4),
	CRSE2=crse(Entries,CRS4),
	warn_if_no_chains(2).


%! top_down_refinement(+SCC_N:int) is det
% Start from the outmost SCC and goes down until the innermost
% For each SCC, it calls top_down_refinement_scc/1

top_down_refinement([],CRS,_Ignored_crs,CRS).
top_down_refinement([SCC|SCCs],CRS,Ignored_crs,CRS_out):-
	scc_get_cover_points(SCC,[F/A]),\+contains_sl(Ignored_crs,F/A),!,
	crs_get_cr(CRS,F,CR),
	top_down_refinement_scc(CR,CR2),
	crs_update_cr(CRS,F,CR2,CRS2),
	top_down_refinement(SCCs,CRS2,Ignored_crs,CRS_out).
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
top_down_refinement_scc(CR,CR6):-
	profiling_start_timer(unfold),
	compute_loops(CR,CR2),
	compute_chains(CR2,CR3),!,
	compute_phase_loops(CR3,CR4),
	profiling_stop_timer_acum(unfold,_),
	compute_forward_invariants(CR4,CR5),
	reinforce_equations_with_forward_invs(CR5,CR6).

%! bottom_up_refinement_scc(+Head:term) is det
%  *  Unfold the SCC defined by Head according to its calls to other SCC 
%  *  that have been already refined. 
%  *  Compute Chains 
%  *  Find ranking functions and prove termination of the chains
%  *  Remove impossible chains
%  *  Compute forward and backwards invariants
bottom_up_refinement_scc(CR,CRS,CR6) :-
	copy_term(Head,Head_aux),
	functor(Head,Name,_),
	cr_IOvars(CR,Name,IOvars),
	
	profiling_start_timer(unfold),
	unfold_calls(CR,CRS,CR2,Ref_info),
	print_equations_refinement(CR2,Ref_info), 
	compute_loops(CR2,CR3),
	print_loops_refinement(CR3),
	
	compute_chains(CR3,CR4),
	compute_phase_loops(CR4,CR5),
	profiling_stop_timer_acum(unfold,_),

	profiling_start_timer(inv),
	compute_forward_invariants(CR5,CR6),	
	profiling_stop_timer_acum(inv,_),
	
	profiling_start_timer(termination),
	find_ranking_functions(Head,IOvars,2),
	print_ranking_functions(Head),
	
	prove_termination(Head,2),
	profiling_stop_timer_acum(termination,_),
	
	remove_terminating_non_terminating_chains(Head,2),
	
	profiling_start_timer(inv),
	%compute_forward_invariants(Head,2),	
	compute_invariants_for_scc(Head,2),
	profiling_stop_timer_acum(inv,_),
	print_chains_entry(Head_aux,2),
%TODO: experiment with chain compression	
	conditional_call((get_param(compress_chains,[N]),N > 0),
	    (
		  compress_chains_execution_patterns(Head,2),
		  print_external_pattern_refinement(Head,2)
		  )
		 ).
	
%! upper_bounds is det
% compute upper bounds for all SCC and a closed upper bounds for the entry SCC
bounds(CRSE,SCCs,Ignored_crs):-
    profiling_start_timer(ubs),
    bottom_up_bounds(SCCs,CRSE,Ignored_crs), 
    CRSE=crse(Entries,_CRS),
    maplist(\Entry^(Entry=entry(Head,_Cs),compute_closed_bound_scc(Head)),Entries),
    profiling_stop_timer_acum(ubs,_).
   
%! bottom_up_upper_bounds(+SCC_N:int,+Max_SCC_N:int) is det
% Start from the innermost SCC and goes up until the outmost SCC
% For each SCC, it computes the upper bound
bottom_up_bounds([],_CRSE,_Ignored_crs).

bottom_up_bounds([SCC|SCCs],CRSE,Ignored_crs):-
	scc_get_cover_points(SCC,[F/A]),\+contains_sl(Ignored_crs,F/A),!,
	functor(Head,F,A),
	(SCCs=[]-> Last=true;Last=false),
	CRSE=crs(_Entries,CRS),
	crs_IOvars(CRS,F,IOvars),
	compute_bound_for_scc(Head,IOvars,2,Last),
	copy_term(Head,Head_aux),
	conditional_call((get_param(v,[N]),N>1),
		  print_results(Head_aux,2)
		 ),
	bottom_up_bounds(SCCs,CRSE,Ignored_crs).

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

warn_if_no_chains(RefCnt):-
	chain(_,RefCnt,_),!.
warn_if_no_chains(_):-
	conditional_call((get_param(v,[N]),N>0),print_or_log('Warning: No feasible chains found~n',[])).
