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

:- use_module(cost_equation_solver,[get_loop_cost/5]).
:- use_module('phase_solver/phase_solver',[compute_phase_cost/5,compute_multiple_rec_phase_cost/6]).
:- use_module(constraints_maximization,[max_min_fconstrs_in_chain/6]).

:-use_module('../db',[phase_loop/5,loop_ph/6]).
:-use_module('../refinement/invariants',[
				  backward_invariant/4,
				  partial_backward_invariant/5,
			      phase_transitive_closure/5,
			      forward_invariant/4]).
:- use_module('../utils/polyhedra_optimizations',[nad_project_group/3]).			      
:- use_module('../utils/cost_expressions',[cexpr_simplify_ctx_free/2]).
:- use_module('../utils/cost_structures',[
		 cstr_extend_variables_names/3,
		 cstr_join_equal_fconstr/2,
		 cstr_or_compress/2,
		 cstr_join/3,
		 new_itvar/1]).
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(numeric_abstract_domains),[
				nad_list_glb/2,
				nad_list_lub/2]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).
	
:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module('../utils/cost_structures',[new_itvar/1]).	
:-use_module('../IO/params',[get_param/2]).
%! compute_chain_cost(+Head:term,+Chain:chain,-Cost:cstr) is det
% compute the cost structure of a chain.
%   * Compute the cost of each phase
%   * compress the costs of different phases
compute_chain_cost(Head,Chain,Cost_total1):-
	compress_chain_costs(Chain,[],Head,Head,Cost_total,_),
	cstr_extend_variables_names(Cost_total,ch(Chain),Cost_total1),
	!.

compress_chain_costs([],_Chain_rev,_Head_total,_Head,Cost_base,[]):-
	Cost_base=cost([],[],[],[],0).
compress_chain_costs([Base_case],Chain_rev,Head_total,Head,Cost_base,Cs_base):-
	number(Base_case),!,
	copy_term(Head_total,Head),
	forward_invariant(Head,([Base_case|Chain_rev],_),Forward_hash,Forward_inv),
	profiling_start_timer(equation_cost),
	get_loop_cost(Head,[],(Forward_hash,Forward_inv),Base_case,Cost),
	profiling_stop_timer_acum(equation_cost,_),
	cstr_join_equal_fconstr(Cost,Cost_base),
	loop_ph(Head,(Base_case,_),[],Cs,_,_),
	ut_flat_list([Forward_inv,Cs],Cs_base).


compress_chain_costs([multiple(Phase,Tails)],Chain_rev,Head_total,Head,Cost_next_simple,Cs_next):-
	number(Phase),!,
 	copy_term(Head_total,Head),
 	maplist(compress_chain_costs_aux([Phase|Chain_rev],Head_total,Call),Tails,Costs_prev,Css_prev),
	nad_list_lub(Css_prev,Cs_prev),
	cstr_or_compress(Costs_prev,Cost_prev),
	
	forward_invariant(Head,([Phase|Chain_rev],_),Forward_hash,Forward_inv),
	get_loop_cost(Head,Calls,(Forward_hash,Forward_inv),Phase,Cost_simple),
 	
 	loop_ph(Head,(Phase,_),Calls,Cs,_,_),
 	maplist(copy_call_costs_and_inv(Call,Cost_prev,Cs_prev),Calls,Costs_prevs,Cs_prevs),
 	nad_list_glb([Cs|Cs_prevs],Cs_total),

	foldl(cstr_join,Costs_prevs,Cost_simple,cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands,BConstant)),
    max_min_fconstrs_in_chain(Ub_fconstrs,[multiple(Phase,Tails)],Cs_total,Head,Ub_fconstrs_new,Ub_iconstrs_extra),
    max_min_fconstrs_in_chain(Lb_fconstrs,[multiple(Phase,Tails)],Cs_total,Head,Lb_fconstrs_new,Lb_iconstrs_extra),
    % put together the original non-final constraints (Aux_exps) and the newly created
    ut_flat_list([Ub_iconstrs_extra,Lb_iconstrs_extra,Iconstrs],Aux_exps_new),
    %the cost is the sum of the individual costs
    Cost_next=cost(Ub_fconstrs_new,Lb_fconstrs_new,Aux_exps_new,Bsummands,BConstant),
 	cstr_join_equal_fconstr(Cost_next,Cost_next_simple),
 	Head=..[_|EVars],
 	%prepare  information for next iteration
	nad_project_group(EVars,Cs_total,Cs_next).	


%multiple recursion case
compress_chain_costs([multiple(Phase,Tails)],Chain_rev,Head_total,Head,Cost_simple,Cs_next):-
	copy_term(Head_total,Head),
	maplist(compress_chain_costs_aux([Phase|Chain_rev],Head_total,Call),Tails,Costs_prev,_Css_prev),
	%nad_list_lub(Css_prev,_Cs_prev),
	cstr_or_compress(Costs_prev,Cost_prev),
	
	(get_param(debug,[])->format('computing cost of phase ~p with multiple recursion with suffix ~p and prefix ~p ~n',[Phase,Tails,Chain_rev]);true),
	profiling_start_timer(loop_phases),
	copy_term((Call,Cost_prev),(Head,Cost_prev2)),
	
	forward_invariant(Head,([Phase|Chain_rev],_),Hash_local_inv,Local_inv),	
	partial_backward_invariant([multiple(Phase,Tails)],Head,(Hash_local_inv,Local_inv),Entry_pattern,Back_inv_star),
	
	compute_multiple_rec_phase_cost(Head,Phase,[Phase|Chain_rev],Cost_prev2,Back_inv_star,Cost),
	profiling_stop_timer_acum(loop_phases,_),
	cstr_join_equal_fconstr(Cost,Cost_simple),	
	nad_list_glb([Local_inv,Entry_pattern],Cs_next).	


 compress_chain_costs([Phase|Chain],Chain_rev,Head_total,Head,Cost_next_simple,Cs_next):-
	number(Phase),
 	copy_term(Head_total,Head),
 	compress_chain_costs(Chain,[Phase|Chain_rev],Head_total,Call,Cost_prev,Cs_prev),	
	forward_invariant(Head,([Phase|Chain_rev],_),Forward_hash,Forward_inv),
	get_loop_cost(Head,[Call],(Forward_hash,Forward_inv),Phase,Cost_simple),
 	
	%FIXME: this should be substituted by the backward invariant!!
 	get_all_phase_information(Head,Call,[Phase|Chain_rev],Cs_list),
 	nad_list_glb([Cs_prev|Cs_list],Cs_total),

	%FIXME: this has to be simplified
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
 	cstr_join_equal_fconstr(Cost_next,Cost_next_simple),
 	Head=..[_|EVars],
 	%prepare  information for next iteration
	nad_project_group(EVars,Cs_total,Cs_next).	
	
compress_chain_costs([Phase|Chain],Chain_rev,Head_total,Head,Cost_next_simple,Cs_next):-
	copy_term(Head_total,Head),
	compress_chain_costs(Chain,[Phase|Chain_rev],Head_total,Call,Cost_prev,Cs_prev),
	profiling_start_timer(loop_phases),
	(get_param(debug,[])->format('computing cost of phase ~p with suffix ~p and prefix ~p ~n',[Phase,Chain,Chain_rev]);true),
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
	
compress_chain_costs_aux(Chain_rev,Head_total,Head,Chain,Cost,Cs):-
	compress_chain_costs(Chain,Chain_rev,Head_total,Head,Cost,Cs).

copy_call_costs_and_inv(Call,Cost_prev,Cs_prev,Call2,Cost_prev2,Cs_prev2):-
	copy_term((Call,Cost_prev,Cs_prev),(Call2,Cost_prev2,Cs_prev2)).
	
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
	phase_loop(Lg_next,_,_,Head,Cs_carried).


