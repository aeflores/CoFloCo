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
:- use_module(constraints_maximization,[
		max_min_top_exprs_in_chain/6]).

:-use_module('../db',[phase_loop/5,loop_ph/6]).
:-use_module('../refinement/invariants',[
				  backward_invariant/4,
			      phase_transitive_closure/5,
			      forward_invariant/4]).
:- use_module('../utils/polyhedra_optimizations',[nad_project_group/3]).			      
:- use_module('../utils/cost_expressions',[cexpr_simplify_ctx_free/2]).
:- use_module('../utils/cost_structures',[
		 cstr_extend_variables_names/3,
		 cstr_join_equal_top_expressions/2]).
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(numeric_abstract_domains),[nad_list_glb/2]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).
	
:-use_module(library(apply_macros)).
:-use_module(library(lists)).


%! compute_chain_cost(+Head:term,+Chain:chain,-Cost:cost_structure) is det
% compute the cost structure of a chain.
%   * Compute the cost of each phase
%   * compress the norms of different phases
compute_chain_cost(Head,Chain,Cost_total1):-
	profiling_start_timer(loop_phases),
	compute_phases_cost(Chain,Chain,Head,Call,Costs),
	profiling_stop_timer_acum(loop_phases,_),
	profiling_start_timer(chain_solver),
	compress_chain_costs(Chain,Costs,Head,Call,Cost_total),
	cstr_extend_variables_names(Cost_total,ch(Chain),Cost_total1),	
	profiling_stop_timer_acum(chain_solver,_),
	!.




%! compress_chain_constraints(+Chain:chain,+Norms_list:list(list(norm)),+Head_total:term,+Call:term,-Norms_out:list(norm)) is det
%  We have a set of norms for each phase and we want to express all of them in terms
% of the entry variables. At the same time, we try to compress them to gain precision.
%
% we start from the base case to the outmost phase.
% At each step we try to compress the norms from the previous phases 
% witht the ones of the current phase and express them in terms of the initial variables
% of the phase.

compress_chain_costs([Lg|More],[Cost_base|Costs],Head_total,Call_total,Cost_total):-
	copy_term((Head_total,Cost_base),(Head,Cost_base1)),
	get_all_base_case_information(Head,[Lg|More],Phi),
	compress_chain_costs_1(More,Costs,Cost_base1,Phi,Head_total,Call_total,Head,Cost_total).

compress_chain_costs_1([],[],Cost_total,_,Head,_,Head,Cost_total).
compress_chain_costs_1([Lg|More],[Cost|Cost_list],Cost_prev,Cs_prev,Head_total,Call_total,Call,Cost_total):-
	copy_term((Head_total,Call_total,Cost),(Head,Call,Cost1)),
	cstr_join_equal_top_expressions(Cost1,Cost1_simple),
	get_all_phase_information(Head,Call,[Lg|More],Cs_list),
	nad_list_glb([Cs_prev|Cs_list],Cs_total),
	Cost_prev=cost(Ub_tops,Lb_tops,Auxs,Bases_prev,Base_prev),
	Cost1_simple=cost(Ub_tops1,Lb_tops1,Auxs1,Bases1,Base1),
	append(Ub_tops,Ub_tops1,Ub_tops_total),
	append(Lb_tops,Lb_tops1,Lb_tops_total),
	max_min_top_exprs_in_chain(Ub_tops_total,[Lg|More],Cs_total,Head,Ub_tops_new,Ub_Aux_exps_extra),
	max_min_top_exprs_in_chain(Lb_tops_total,[Lg|More],Cs_total,Head,Lb_tops_new,Lb_Aux_exps_extra),
	ut_flat_list([Ub_Aux_exps_extra,Lb_Aux_exps_extra,Auxs,Auxs1],Aux_exps_new),
	append(Bases_prev,Bases1,Bases_total),
	cexpr_simplify_ctx_free(Base_prev+Base1,Base2),
	Cost_next=cost(Ub_tops_new,Lb_tops_new,Aux_exps_new,Bases_total,Base2),
	cstr_join_equal_top_expressions(Cost_next,Cost_next_simple),
	Head=..[_|EVars],
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


