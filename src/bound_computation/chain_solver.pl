/** <module> chain_solver

This module computes the cost of a chain in terms of the variables 
at the beginning of the chain.
It calls the phase_solver.pl to obtain the costs of the phases and 
combine them trying to compress constraints. 

The different elements of the cost structures from the phases
 are expressed in terms of intermediate variables
so they have to be maximized in terms of the initial variables of the chain.
For the constraints, this is done at the same time of the compression.

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

:- module(chain_solver,[compute_chain_cost/3]).

:- use_module(phase_solver,[compute_phases_cost/5]).
:- use_module(constraints_maximization,[max_min_fconstrs_in_chain/6]).

:-use_module('../db',[phase_loop/5,loop_ph/6]).
:-use_module('../refinement/invariants',[
				  backward_invariant/4,
			      phase_transitive_closure/5,
			      forward_invariant/4]).
:- use_module('../utils/polyhedra_optimizations',[nad_project_group/3]).			      
:- use_module('../utils/cost_expressions',[cexpr_simplify_ctx_free/2]).
:- use_module('../utils/cost_structures',[
		 cstr_extend_variables_names/3,
		 cstr_join_equal_fconstr/2]).
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(numeric_abstract_domains),[nad_list_glb/2]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).
	
:-use_module(library(apply_macros)).
:-use_module(library(lists)).


%! compute_chain_cost(+Head:term,+Chain:chain,-Cost:cstr) is det
% compute the cost structure of a chain.
%   * Compute the cost of each phase
%   * compress the costs of different phases
compute_chain_cost(Head,Chain,Cost_total1):-
	profiling_start_timer(loop_phases),
	compute_phases_cost(Chain,Chain,Head,Call,Costs),
	profiling_stop_timer_acum(loop_phases,_),
	profiling_start_timer(chain_solver),
	compress_chain_costs(Chain,Costs,Head,Call,Cost_total),
	cstr_extend_variables_names(Cost_total,ch(Chain),Cost_total1),	
	profiling_stop_timer_acum(chain_solver,_),
	!.




%! compress_chain_costs(+Chain:chain,+Costs:list(cstr),+Head_total:term,+Call:term,-Cost_total:cstr) is det
%  We have a cost structure for each phase and we want to combine them into a single cost structure
% in terms of the input variables
%
% we combine the cost structures incrementally from the last phase (base case) to the first (entry point).
compress_chain_costs([Lg|More],[Cost_base|Costs],Head_total,Call_total,Cost_total):-
	copy_term((Head_total,Cost_base),(Head,Cost_base1)),
	get_all_base_case_information(Head,[Lg|More],Phi),
	compress_chain_costs_1(More,Costs,Cost_base1,Phi,Head_total,Call_total,Head,Cost_total).

compress_chain_costs_1([],[],Cost_total,_,Head,_,Head,Cost_total).
compress_chain_costs_1([Lg|More],[Cost|Cost_list],Cost_prev,Cs_prev,Head_total,Call_total,Call,Cost_total):-
	copy_term((Head_total,Call_total,Cost),(Head,Call,Cost1)),
	cstr_join_equal_fconstr(Cost1,Cost1_simple),
	%get information of the phase and later phases
	get_all_phase_information(Head,Call,[Lg|More],Cs_list),
	nad_list_glb([Cs_prev|Cs_list],Cs_total),
	% combine the upper bound and lower bound final constraints separately
	Cost_prev=cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands_prev,BConstant_prev),
	Cost1_simple=cost(Ub_fconstrs1,Lb_fconstrs1,Iconstrs1,Bsummands1,BConstant1),
	append(Ub_fconstrs,Ub_fconstrs1,Ub_fconstrs_total),
	append(Lb_fconstrs,Lb_fconstrs1,Lb_fconstrs_total),
	max_min_fconstrs_in_chain(Ub_fconstrs_total,[Lg|More],Cs_total,Head,Ub_fconstrs_new,Ub_iconstrs_extra),
	max_min_fconstrs_in_chain(Lb_fconstrs_total,[Lg|More],Cs_total,Head,Lb_fconstrs_new,Lb_iconstrs_extra),
	% put together the original non-final constraints (Aux_exps) and the newly created
	ut_flat_list([Ub_iconstrs_extra,Lb_iconstrs_extra,Iconstrs,Iconstrs1],Aux_exps_new),
	%the cost is the sum of the individual costs
	append(Bsummands_prev,Bsummands1,Bsummands_total),
	cexpr_simplify_ctx_free(BConstant_prev+BConstant1,BConstant2),
	Cost_next=cost(Ub_fconstrs_new,Lb_fconstrs_new,Aux_exps_new,Bsummands_total,BConstant2),
	% simplify resulting cost structure
	cstr_join_equal_fconstr(Cost_next,Cost_next_simple),
	Head=..[_|EVars],
	%prepare  information for next iteration
	nad_project_group(EVars,Cs_total,Cs_next),
	compress_chain_costs_1(More,Cost_list,Cost_next_simple,Cs_next,Head_total,Call_total,Head,Cost_total).


%! get_all_base_case_information(+Head:term,+Part_chain:chain,-Phi:polyhedron) is det
%  obtain the base case definition and the forward invariant
%  and put them together
get_all_base_case_information(Head,[Lg|More],Phi):-
	loop_ph(Head,(Lg,_),none,Cs_base,_,_),
	forward_invariant(Head,([Lg|More],_),_,Local_inv),
	ut_flat_list([Local_inv,Cs_base],Phi). %cheap glb

%! get_all_phase_information(+Head:term,Call:term,+Part_chain:chain,-Phi_list:list(polyhedron)) is det
% Obtain:
%  * The transitive closure of the phase or the phase definition (depending on whether
%    it is iterative or not. 
%  * The forward invariant
%  * The phase information at the beginning of the phase
%  * The phase information at the end of the next phase
% and put it all together in a list
get_all_phase_information(Head,Call,[Lg|More],Phi_list):-
	forward_invariant(Head,([Lg|More],_),_,Local_inv),
	
	(
	phase_transitive_closure(Lg,_,Head,Call,Cs_transitive)
	 ;
	loop_ph(Head,(Lg,_),Call,Cs_transitive,_,_)
	),
	(phase_loop(Lg,_,Head,_,Cs_extra) ; Cs_extra=[]),!,
	get_next_phase_predicate(More,Head,Cs_carried),
	Phi_list=[Local_inv,Cs_transitive,Cs_extra,Cs_carried].


get_next_phase_predicate([],_,[]).
get_next_phase_predicate([Lg_next|_],Head,Cs_carried):-
	number(Lg_next),!,
	loop_ph(_,(Lg_next,_),Head,Cs_carried,_,_).
get_next_phase_predicate([Lg_next|_],Head,Cs_carried):-
	phase_loop(Lg_next,_,_,Head,Cs_carried).


