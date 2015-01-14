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
   
  * linear_expression: N0+N1*X1+N1*X1+... +NN*XN where N0..NN are rationals and X1...XN variables
  
  * linear_constraint: linear_expression rel_op linear_expression
    If the linear constraint is normalized, it has the form:
    linear_expression rel_op number

  * polyhedron: list(linear_constraint)
    A polyhedron is expressed with the constraints representation
    
  * cost_expression:
        * nat(linear_expression)
          Often the nat wrapping is removed if it can be proved that linear_expression must be positive
        * cost_expression+cost_expression
        * cost_expression*cost_expression
        * max(list(cost_expression))
        * min(list(cost_expression))
        
  * norm: norm(list_set(var),cost_expression)
    A norm norm([It1,It2,...ItN],C) represent a constraint It1+It2+...ItN=< C that binds the values
    of the iteration variables It1,It2...ItN.
    
  * loop_cost: loop(var,cost_expression,list(loop_cost),list(norm))
    a loop cost loop(It_var,C,Loops,Norms) is a loop that has the iteration variable It_var
    a cost per iteration of C plus the cost of the loops that has inside Loops.
    Norms bind the iteration variable of the loops in Loops.
    
  * cost_structure: cost(cost_expression,list(loop_cost),list(norm))
    a cost structure cost(Base,Loops,Norms) has a basic cost Base
    plus the cost of the loops that are inside Loops.
    Norms bind the iteration variables of the loops in Loops.




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


:- module(main_cofloco,[cofloco_shell_main/0,cofloco_query/2]).

:-include('search_paths.pl').

:- use_module(db,[eq_ph/7,entry_eq/2,init_db/0,init_timers/0]).
:- use_module('pre_processing/SCCs',[compute_sccs_and_btcs/0,
				ignored_scc/1,
				crs_residual_scc/2,
				crs_max_scc_id/1,  
				crs_node_scc/3,    
		       crs_scc/5]).
:- use_module('pre_processing/partial_evaluation',[partial_evaluation/0]).

:- use_module('refinement/invariants',[compute_invariants_for_scc/2,
			  compute_forward_invariants/2,
			  clean_invariants/0,
			  add_scc_forward_invariant/3,
			  backward_invariant/4
			  ]).
:- use_module('refinement/unfolding',[unfold_calls/2,
			 reinforce_equations_with_forward_invs/2,
			 remove_terminating_non_terminating_chains/2]). 
:- use_module('refinement/chains',[compute_chains/2,chain/3,init_chains/0]).
:- use_module('refinement/loops',[compute_loops/2,compute_phase_loops/2]).


:- use_module(ranking_functions,[init_ranking_functions/0,find_ranking_functions/2]).
:- use_module(termination_checker,[init_termination/0,prove_termination/2]).

:- use_module('upper_bounds/upper_bounds',[compute_upper_bound_for_scc/2,
				  compute_closed_bound/1,
				  compute_single_closed_bound/2]).
:- use_module('upper_bounds/phase_solver',[init_phase_solver/0]).
:- use_module('upper_bounds/cost_equation_solver',[init_cost_equation_solver/0]).    

:- use_module('IO/output',[print_results/2,
	          print_equations_refinement/2,
		      print_help/0,
		      print_closed_results/2,
		      print_chains/1,
		      print_chains_entry/2,
		      print_single_closed_result/2,
		      print_stats/0,
		      print_help/0]).
:- use_module('IO/input',[read_cost_equations/1,store_cost_equations/1]).
:-use_module('IO/params',[set_default_params/0,parse_params/1,get_param/2]).


:- use_module(stdlib(numeric_abstract_domains),[nad_set_domain/1]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_get_info/3,
				 profiling_stop_timer/2,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_get_value/2,counter_initialize/2]).
:-use_module(stdlib(polyhedra_ppl),[ppl_my_initialize/0]).


%! cofloco_shell_main is det
% main predicate to be called form the console.  
% it performs the complete analysis
cofloco_shell_main:-
        current_prolog_flag(argv, Args),
           set_default_params,
	   (Args=[_|_]->
	    catch(parse_params(Args),E,(print_message(error, E), halt)),
	    catch(main,E,(print_message(error, E),halt))
	   ;
	    print_help
	   ),
	   halt.

%! save_executable is det
% build an executable file of cofloco
save_executable:-
	ppl_my_initialize,
	make,
	check,
	prolog_history(disable),
	qsave_program('cofloco',[stand_alone(true),goal(main:cofloco_shell_main),foreign(save)]),
	writeln('Binary package generated').


%! cofloco_query(+Eqs:list(cost_equation),+Params:list(atom)) is det
% perform the main analysis on the equations Eqs with the parameters Params
cofloco_query(Eqs,Params):-
	parse_params(Params),
    ppl_my_initialize,
	init_timers,
	init_database,
	store_cost_equations(Eqs),
	preprocess_cost_equations,
	refinement,
	upper_bounds.


	
%! main is det
% Obtains the input file, read the cost equations, preprocess the cost equations,
% perform the main analysis and print results
main:-
    ppl_my_initialize,
	init_timers,
	init_database,
	profiling_start_timer(analysis),
	get_param(input,[File]),!,
	read_cost_equations(File),
	preprocess_cost_equations,
	refinement,
	(get_param(only_termination,[])->
		true
		;
		upper_bounds
	),
	
	profiling_stop_timer(analysis,T_analysis),
	ansi_format([underline,bold],'Time statistics:~p~n',[' ']),
	conditional_call(get_param(stats,[]),print_stats),		
	format("Total analysis performed in ~0f ms.~n~n",[T_analysis]).

main:-
	print_help.

%! init_database is det
% erase all the information from previous analyses	
init_database:-
	init_db,
	init_ranking_functions,
	init_termination,
	init_chains,
	clean_invariants,
	init_phase_solver,
	init_cost_equation_solver.	
	
%! preprocess_cost_equations is det
% Computes the SCC (strongly connected components)
% Performs partial evaluation to obtain direct recursion
preprocess_cost_equations:-
	profiling_start_timer(comp_sccs),
	compute_sccs_and_btcs,
	profiling_stop_timer(comp_sccs,_),
	profiling_start_timer(pe),
	partial_evaluation,
	profiling_stop_timer(pe,_).

%! refinement is det
% perform the top_down analysis followed
% by the bottom_up analysis
refinement:-
	entry_eq(Head,Cs),
    add_scc_forward_invariant(Head,0,Cs),
    functor(Head,F,A),
    crs_node_scc(F,A,SCC_N),
	top_down_refinement(SCC_N),	
	bottom_up_refinement(0,SCC_N),
	warn_if_no_chains(2).



%! top_down_refinement(+SCC_N:int) is det
% Start from the outmost SCC and goes down until the innermost
% For each SCC, it calls top_down_refinement_scc/1
top_down_refinement(SCC_N) :-
	SCC_N >= 0,
	crs_residual_scc(SCC_N,F/A),\+ignored_scc(F/A),!,
	functor(Head,F,A),
	top_down_refinement_scc(Head),
	Next_SCC_N is SCC_N-1,
	top_down_refinement(Next_SCC_N).
top_down_refinement(SCC_N):-
	SCC_N >= 0,
	crs_residual_scc(SCC_N,F/A),ignored_scc(F/A),
	Next_SCC_N is SCC_N-1,
	top_down_refinement(Next_SCC_N).
top_down_refinement(-1).

%! bottom_up_refinement(+SCC_N:int,+Max_SCC_N:int) is det
% Start from the innermost SCC and goes up until the outmost SCC
% For each SCC, it calls bottom_up_refinement_scc/1
bottom_up_refinement(SCC_N, Max_SCC_N) :-
	SCC_N =< Max_SCC_N,
	crs_residual_scc(SCC_N,F/A),\+ignored_scc(F/A),!,
	functor(Head,F,A),
	bottom_up_refinement_scc(Head),
	Next_SCC_N is SCC_N+1,
	bottom_up_refinement(Next_SCC_N, Max_SCC_N).
bottom_up_refinement(SCC_N, Max_SCC_N) :-
	SCC_N =< Max_SCC_N,
	crs_residual_scc(SCC_N,F/A),ignored_scc(F/A),
	Next_SCC_N is SCC_N+1,
	bottom_up_refinement(Next_SCC_N, Max_SCC_N).
bottom_up_refinement(SCC_N, SCC_N_max):-SCC_N > SCC_N_max.

%! top_down_refinement_scc(+Head:term) is det
% Computes chains for a SCC defined by Head
% Computes forward invariants for the generated chains and add the invariants
% to the cost equations
top_down_refinement_scc(Head):-
	profiling_start_timer(unfold),
	compute_loops(Head,0),
	compute_chains(Head,0),!,
	compute_phase_loops(Head,0),
	profiling_stop_timer_acum(unfold,_),
	compute_forward_invariants(Head,0),
	reinforce_equations_with_forward_invs(Head,0).

%! bottom_up_refinement_scc(+Head:term) is det
%  *  Unfold the SCC defined by Head according to its calls to other SCC 
%  *  that have been already refined. 
%  *  Compute Chains 
%  *  Find ranking functions and prove termination of the chains
%  *  Remove impossible chains
%  *  Compute forward and backwards invariants
bottom_up_refinement_scc(Head) :-
	copy_term(Head,Head_aux),

	profiling_start_timer(unfold),
	unfold_calls(Head,1),
	print_equations_refinement(Head_aux,1),
		  
	compute_loops(Head,2),
	compute_chains(Head,2),
	compute_phase_loops(Head,2),
	profiling_stop_timer_acum(unfold,_),

	
	profiling_start_timer(termination),
	find_ranking_functions(Head,2),
	prove_termination(Head,2),
	profiling_stop_timer_acum(termination,_),
	
	remove_terminating_non_terminating_chains(Head,2),
	
	profiling_start_timer(inv),
	compute_forward_invariants(Head,2),	
	compute_invariants_for_scc(Head,2),
	profiling_stop_timer_acum(inv,_),
	
	print_chains_entry(Head_aux,2).
	

%! upper_bounds is det
% compute upper bounds for all SCC and a closed upper bounds for the entry SCC
upper_bounds:-
    entry_eq(Head,_),   
    functor(Head,F,A),
    crs_node_scc(F,A,SCC_N),
    profiling_start_timer(ubs),
    bottom_up_upper_bounds(0,SCC_N),
    compute_closed_bound_scc(Head),
    profiling_stop_timer_acum(ubs,_).
    
%! bottom_up_upper_bounds(+SCC_N:int,+Max_SCC_N:int) is det
% Start from the innermost SCC and goes up until the outmost SCC
% For each SCC, it computes the upper bound
bottom_up_upper_bounds(SCC_N, Max_SCC_N) :-
	SCC_N =< Max_SCC_N,
	crs_residual_scc(SCC_N,F/A),\+ignored_scc(F/A),!,
	functor(Head,F,A),
	Next_SCC_N is SCC_N+1,

	compute_upper_bound_for_scc(Head,2),
	copy_term(Head,Head_aux),
	conditional_call((get_param(v,[N]),N>1),
		  print_results(Head_aux,2)
		 ),
	bottom_up_upper_bounds(Next_SCC_N, Max_SCC_N).
bottom_up_upper_bounds(SCC_N, Max_SCC_N) :-
	SCC_N =< Max_SCC_N,
	crs_residual_scc(SCC_N,F/A),ignored_scc(F/A),
	Next_SCC_N is SCC_N+1,
	bottom_up_upper_bounds(Next_SCC_N, Max_SCC_N).
bottom_up_upper_bounds(SCC_N, SCC_N_max):-SCC_N > SCC_N_max.   


compute_closed_bound_scc(Head) :-	
	copy_term(Head,Head_aux),
	profiling_start_timer(solver),
	compute_closed_bound(Head),
	compute_single_closed_bound(Head_aux,Exp),
	profiling_stop_timer_acum(solver,_),
	conditional_call((get_param(v,[N]),N>0),	
		 print_closed_results(Head,2)
		),
	print_single_closed_result(Head_aux,Exp).
	

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
	format('Warning: No feasible chains found~n',[]).