/** <module> bounds_main

This is the main module that performs bound computation.
It basically calls the chain_solver.pl for each chain in a given SCC


Afterwards, it compresses the upper bounds within each 
external call pattern (if these exists) to obtain external bounds
that can be passed on to the callers.

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

:- module(bounds_main,[
	cr_compute_bounds/4,
	compute_closed_bounds/2]).

:- use_module(cost_equation_solver,[
	compute_ce_bounds/3,
	compute_loop_bounds/3
	]).
:- use_module('phase_solver/phase_solver',[compute_phase_bounds/3]).
:- use_module(chain_solver,[compute_chain_bounds/5]).
:- use_module(cost_structure_solver,[cstr_maxminimization/6]).
:- use_module(conditional_bounds,[compute_conditional_bounds/3]).

:- use_module('../utils/crs',[
	crs_get_cr/3,
	cr_head/2,
	cr_get_loops/2,
	cr_get_chains/2,
	cr_get_external_patterns/2,
	cr_get_back_invs/2,
	cr_set_loops/3,
	cr_set_chains/3,
	cr_set_external_patterns/3,
	cr_IOvars/2,
	cr_set_piecewise_bounds/3,
	cr_get_piecewise_bounds/2,
	crs_update_cr/4
	]).

:-use_module('../refinement/chains',[
	chain_get_pattern/2,
	chains_get_chain/3,
	chain_get_cost/2,
	chain_set_closed_upper_bound/3,
	chain_set_closed_lower_bound/3
	]).
:-use_module('../refinement/invariants',[
	back_invs_get/3
	]).	
	
:-use_module('../refinement/unfolding',[
	external_pattern_set_cost/3,
	external_pattern_cost/2,
	external_patterns_head/2,
	external_patterns_get_external_pattern/3,
	external_patterns_apply_to_each/3
	]).

:- use_module('../utils/cofloco_utils',[
	bagof_no_fail/3,
	zip_with_op/3
	]).
	
:- use_module('../utils/cost_expressions',[cexpr_simplify/3]).

:- use_module('../utils/structured_cost_expression',[
	strexp_simplify_max_min/2,
	strexp_to_cost_expression/2
	]).
	
:- use_module('../utils/cost_structures',[
	cstr_or_compress/2,
	cstr_extend_variables_names/3
	]).

:- use_module('../IO/params',[get_param/2]).

:- use_module('../IO/output',[
	print_ce_bounds/1,
	print_loop_bounds/1,
	print_phase_bounds/1,
	print_chain_bounds/1,
	print_external_patterns_bounds/1,
	print_chains_closed_bounds/2,
	print_single_closed_result/1,
	print_piecewise_bounds/2,
	print_competition_result/1
	]).


:- use_module(stdlib(numeric_abstract_domains),[
	nad_list_lub/2,
	nad_glb/3
	]).
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list),[from_list_sl/2]).
:- use_module(stdlib(profiling),[
	profiling_start_timer/1,
	profiling_stop_timer_acum/2
	]).
	
:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(lambda)).

%! compute_bound_for_scc(+Head:term,+RefCnt:int,Last:bool) is det
% compute a bound for each chain
% then, compress the bounds for the chains that have been grouped into
% external call patterns only if we are not at the last scc
cr_compute_bounds(F,CRS,Last,CRS2):-
	crs_get_cr(CRS,F,CR),
	cr_get_loops(CR,Loops),
	cr_get_chains(CR,Chains),
	cr_get_external_patterns(CR,External_patterns),
	cr_get_back_invs(CR,Back_invs),
	profiling_start_timer(equation_cost),
	compute_ce_bounds(CR,CRS,CR2),
	print_ce_bounds(CR2),
	compute_loop_bounds(Loops,CR2,Loops2),
	print_loop_bounds(Loops2),
	profiling_stop_timer_acum(equation_cost,_),
	compute_phase_bounds(Chains,Loops2,Chains2),
	print_phase_bounds(Chains2),
	
	cr_IOvars(CR,IOvars),
	compute_chain_bounds(Chains2,Back_invs,Loops2,IOvars,Chains3),
	print_chain_bounds(Chains3),
	(Last=false->
		compute_external_patterns_bounds(External_patterns,Chains3,External_patterns2),
		print_external_patterns_bounds(External_patterns2)
	;
		true
	),	
	cr_set_loops(CR2,Loops2,CR3),
	cr_set_chains(CR3,Chains3,CR4),
	cr_set_external_patterns(CR4,External_patterns2,CR5),
	crs_update_cr(CRS,F,CR5,CRS2).
	

%! compress_upper_bounds_for_external_calls(+Head:term,+RefCnt:int) is det
% For each external call pattern, it computes an upper bound and store it
% as a external_upper_bound/3.
% If there are no expternal call patterns, it does nothing.
%
% Each call pattern contains a set of chains. The upper bound (cost structure)
% is obtained by compressing the upper bound of these chains into one.
compute_external_patterns_bounds(External_patterns,Chains3,External_patterns2):-
	external_patterns_head(External_patterns,Head),
	external_patterns_apply_to_each(bounds_main:compute_external_pattern_cost(Head,Chains3),External_patterns,External_patterns2).

compute_external_pattern_cost(Head,Chains,(Chains_pattern,External_pattern),(Chains_pattern,External_pattern2)):-
	maplist(get_chain_cost(Head,Chains),Chains_pattern,Costs),
	cstr_or_compress(Costs,Final_cost_structure),
	external_pattern_set_cost(External_pattern,Final_cost_structure,External_pattern2).

	
get_chain_cost(Head,Chains,Chain_pattern,Cost3):-
	chains_get_chain(Chains,Chain_pattern,Chain),
	chain_get_cost(Chain,cost(Head1,Cost1)),
	copy_term(cost(Head1,Cost1),cost(Head,Cost2)),
	cstr_extend_variables_names(Cost2,ch(Chain_pattern),Cost3).
	
compute_closed_bounds(CRSE,CRSE2):-
	CRSE=crse(Entries,CRS),
	foldl(compute_cr_closed_bound,Entries,CRS,CRS2),
	CRSE2=crse(Entries,CRS2).

    
compute_cr_closed_bound(entry(Head,_Cs) ,CRS,CRS2):-
	functor(Head,F,_),
	crs_get_cr(CRS,F,CR),
	cr_IOvars(CR,IOvars),
	cr_get_chains(CR,Chains),
	cr_head(CR,Head),
	cr_get_back_invs(CR,Back_invs),
	profiling_start_timer(solver),
	compute_chains_closed_bounds(Chains,Chains2,Back_invs,IOvars,Closed_bounds),
	profiling_stop_timer_acum(solver,_),
	cr_set_chains(CR,Chains2,CR2),
	
	((get_param(conditional_ubs,[]); get_param(conditional_lbs,[]))->
	   compute_conditional_bounds(Head,Closed_bounds,Piecewise_bounds),
	   cr_set_piecewise_bounds(CR2,Piecewise_bounds,CR3)
	   ;
	   (get_param(compute_ubs,[])->
	     	compute_single_closed_bound(Head,Closed_bounds,Exp),
	     	Piecewise_bounds=Exp,
	     	cr_set_piecewise_bounds(CR2,Piecewise_bounds,CR3)
	     ; 
	     	CR3=CR2
	     )
	),
	print_closed_results(CR3),
	crs_update_cr(CRS,F,CR3,CRS2).
	

compute_chains_closed_bounds(chains(Phases,Chains),chains(Phases,Chains2),Back_invs,IOvars,Closed_bounds):-
	maplist(compute_chain_closed_bound(Back_invs,IOvars),Chains,Chains2,Closed_bounds).
	
		
compute_chain_closed_bound(Back_invs,IOvars,Chain,Chain3,Closed_bound):-
	chain_get_cost(Chain,cost(Head,Cost)),
	chain_get_pattern(Chain,Chain_patt),
	back_invs_get(Back_invs,Chain_patt,inv(Head,_,Inv)),
	(get_param(compute_ubs,[])->
	  cstr_maxminimization(Cost,max,Head,Inv,IOvars,UB),  
	  chain_set_closed_upper_bound(Chain,closed_bound(Head,UB),Chain2)
	; 
	  Chain2=Chain,
	  UB=max([inf])
	),
    (get_param(compute_lbs,[])->
	  cstr_maxminimization(Cost,min,Head,Inv,IOvars,LB),
	  chain_set_closed_lower_bound(Chain2,closed_bound(Head,LB),Chain3)
	  ;
	  Chain3=Chain2,
	  LB=min([add([])])
	 ),
	Closed_bound=execution_pattern(Head,(UB,LB),Inv).


	
print_closed_results(CR):-
	cr_get_chains(CR,Chains),
	cr_get_back_invs(CR,Back_invs),
	print_chains_closed_bounds(Chains,Back_invs),
	cr_get_piecewise_bounds(CR,Piecewise_bounds),
    ((get_param(compute_ubs,[]),get_param(conditional_ubs,[]))->
    	print_piecewise_bounds(upper,Piecewise_bounds),
    	print_competition_result(Piecewise_bounds)
    	;
    	Exp=Piecewise_bounds,
		print_single_closed_result(Exp),
		print_competition_result(Exp)
    	),
	((get_param(compute_lbs,[]),get_param(conditional_lbs,[]))->
		print_piecewise_bounds(lower,Piecewise_bounds)
		;
		true
		).
	
	
%! compute_single_closed_bound(+Head:term,+RefCnt:int,-SimpleExp:cost_expression) is det
% compute a closed bound that is the maximum of all the closed bounds of all the chains in a SCC Head
compute_single_closed_bound(Head,External_patterns,single_bound(Head,UB1)):-
	maplist(Head+\Ex_pat^UB^Inv^(
		Ex_pat=execution_pattern(Head,(UB,_),Inv)
		),External_patterns,CExps,Invs),
	maplist(zip_with_op(_),Lists,CExps),
	nad_list_lub(Invs,General_invariant),
	ut_flat_list(Lists,List),
	from_list_sl(List,Set_costs),
	strexp_simplify_max_min(max(Set_costs),Cost_max_min_simple),
	strexp_to_cost_expression(Cost_max_min_simple,UB),
	cexpr_simplify(UB,General_invariant,UB1).
	

