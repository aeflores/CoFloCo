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

:- use_module(phase_solver,[compute_phase_cost/5]).
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
:- use_module('../utils/cost_structures',[new_itvar/1]).	

%! compute_chain_cost(+Head:term,+Chain:chain,-Cost:cstr) is det
% compute the cost structure of a chain.
%   * Compute the cost of each phase
%   * compress the costs of different phases
compute_chain_cost(Head,Chain,Cost_total1):-
	compress_chain_costs(Chain,[],Head,Head,Cost_total,_),
	cstr_extend_variables_names(Cost_total,ch(Chain),Cost_total1),
	!.


compress_chain_costs([Base_case],Chain_rev,Head_total,Head,Cost_base,Cs_base):-
	copy_term(Head_total,Head),
	get_all_base_case_information(Head,[Base_case|Chain_rev],Cs_base),
	profiling_start_timer(loop_phases),
	(number(Base_case)->
		compute_phase_cost(Head,[],Base_case,[Base_case|Chain_rev],Cost_base_aux),
		cstr_join_equal_fconstr(Cost_base_aux,Cost_base)
		;
		copy_term(Head_total,Call),
		compute_phase_cost(Head,[Call],Base_case,[Base_case|Chain_rev],Cost_base_aux),
		Cost_base_aux=cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands,BConstant),
		max_min_fconstrs_in_chain(Ub_fconstrs,[Base_case],Cs_base,Head,Ub_fconstrs_new,Ub_iconstrs_extra),
		max_min_fconstrs_in_chain(Lb_fconstrs,[Base_case],Cs_base,Head,Lb_fconstrs_new,Lb_iconstrs_extra),
	    % put together the original non-final constraints (Aux_exps) and the newly created
	    ut_flat_list([Ub_iconstrs_extra,Lb_iconstrs_extra,Iconstrs],Aux_exps_new),
	    Cost_base_aux2=cost(Ub_fconstrs_new,Lb_fconstrs_new,Aux_exps_new,Bsummands,BConstant),
	    cstr_join_equal_fconstr(Cost_base_aux2,Cost_base)
	),
	profiling_stop_timer_acum(loop_phases,_).

%multiple recursion case
% we don't compute anything yet
compress_chain_costs([multiple(_Phase,_Tails)],_Chain_rev,_Head_total,_Head,Cost_next_simple,Cs_next):-
	%maplist(compress_chain_costs_aux([Phase|Chain_rev],Head_total,Call),Tails,Costs_prev,Cs_prevs),
	new_itvar(It_var),
	Cost_next_simple=cost([],[],[],[(It_var,1)],0),
	Cs_next=[].
	
compress_chain_costs([Phase|Chain],Chain_rev,Head_total,Head,Cost_next_simple,Cs_next):-
	copy_term(Head_total,Head),
	compress_chain_costs(Chain,[Phase|Chain_rev],Head_total,Call,Cost_prev,Cs_prev),
	profiling_start_timer(loop_phases),
	compute_phase_cost(Head,[Call],Phase,[Phase|Chain_rev],Cost),
	profiling_stop_timer_acum(loop_phases,_),
	
	profiling_start_timer(chain_solver),
	cstr_join_equal_fconstr(Cost,Cost_simple),
	%get information of the phase and later phases
	get_all_phase_information(Head,Call,[Phase|Chain_rev],Cs_list),
	nad_list_glb([Cs_prev|Cs_list],Cs_total),
	% combine the upper bound and lower bound final constraints separately
	Cost_prev=cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands_prev,BConstant_prev),
	Cost_simple=cost(Ub_fconstrs1,Lb_fconstrs1,Iconstrs1,Bsummands1,BConstant1),
	append(Ub_fconstrs,Ub_fconstrs1,Ub_fconstrs_total),
	append(Lb_fconstrs,Lb_fconstrs1,Lb_fconstrs_total),
	max_min_fconstrs_in_chain(Ub_fconstrs_total,[Phase|Chain],Cs_total,Head,Ub_fconstrs_new,Ub_iconstrs_extra),
	max_min_fconstrs_in_chain(Lb_fconstrs_total,[Phase|Chain],Cs_total,Head,Lb_fconstrs_new,Lb_iconstrs_extra),
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
	profiling_stop_timer_acum(chain_solver,_).
	


%! get_all_base_case_information(+Head:term,+Part_chain:chain,-Phi:polyhedron) is det
%  obtain the base case definition and the forward invariant
%  and put them together
get_all_base_case_information(Head,[Lg|More],Phi):-
	loop_ph(Head,(Lg,_),[],Cs_base,_,_),!,
	forward_invariant(Head,([Lg|More],_),_,Local_inv),
	ut_flat_list([Local_inv,Cs_base],Phi). %cheap glb
% for non-terminating chains
get_all_base_case_information(Head,[Lg|More],Local_inv):-
	forward_invariant(Head,([Lg|More],_),_,Local_inv).%cheap glb

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
	loop_ph(Head,(Lg,_),[Call],Cs_transitive,_,_)
	),
	(phase_loop(Lg,_,Head,_,Cs_extra) ; Cs_extra=[]),!,
	get_next_phase_predicate(More,Head,Cs_carried),
	Phi_list=[Local_inv,Cs_transitive,Cs_extra,Cs_carried].


get_next_phase_predicate([],_,[]).
get_next_phase_predicate([Lg_next|_],Head,Cs_carried):-
	number(Lg_next),!,
	loop_ph(_,(Lg_next,_),[Head],Cs_carried,_,_).
get_next_phase_predicate([Lg_next|_],Head,Cs_carried):-
	phase_loop(Lg_next,_,_,[Head],Cs_carried).


