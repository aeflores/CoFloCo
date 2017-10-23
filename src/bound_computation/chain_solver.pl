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

:- module(chain_solver,[compute_chain_cost/3,init_chain_solver/0]).

:- use_module(cost_equation_solver,[get_loop_cost/5]).
:- use_module('phase_solver/phase_solver',[compute_phase_cost/6,compute_multiple_rec_phase_cost/6]).
:- use_module(constraints_maximization,[max_min_fconstrs_in_chain/6]).

:-use_module('../db',[phase_loop/5,loop_ph/6]).
:-use_module('../refinement/invariants',[
				  backward_invariant/4,
				  partial_backward_invariant/5,
			      phase_transitive_closure/5,
			      forward_invariant/4,
			      get_forward_invariant/4]).
:- use_module('../utils/polyhedra_optimizations',[nad_project_group/3]).			      
:- use_module('../utils/cost_expressions',[cexpr_simplify_ctx_free/2]).
:- use_module('../utils/cost_structures',[
		 cstr_extend_variables_names/3,
		 cstr_simplify/2,
		 cstr_or_compress/2,
		 cstr_join/3,
		 new_itvar/1,
		 bconstr_accum_bounded_set/3]).

:-use_module('../IO/params',[get_param/2]).
:-use_module('../IO/output',[print_phase_cost/4,
	print_changed_to_chain_method_warning/1,
	print_header/3]).
	
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(numeric_abstract_domains),[
				nad_list_glb/2,
				nad_list_lub/2]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).



:- use_module(stdlib(set_list),[
		difference_sl/3]).
		
:-use_module(library(apply_macros)).
:-use_module(library(lists)).


% chain_cost(Head:term,Chain:chain,(Forward_hash:int,Forward_inv:polyhedron),Cost:cstr,Cs:polyhedron)
:-dynamic chain_cost/5.

%! init_chain_solver is det
init_chain_solver:-
	retractall(chain_cost(_,_,_,_,_)).



%! compute_chain_cost(+Head:term,+Chain:chain,-Cost:cstr) is det
% compute the cost structure of a chain.
%   * Compute the cost of each phase
%   * compress the costs of different phases
compute_chain_cost(Head,Chain,Cost_total):-
	compress_chain_costs(Chain,[],Head,Head,Cost_total,_),
	!.




compress_chain_costs([],_Chain_rev,_Head_total,_Head,Cost_base,[]):-
	Cost_base=cost([],[],[],[],0).

%cacheing	
compress_chain_costs([Phase|Chain],Chain_rev,Head_total,Head,Cost,Cs):-
	copy_term(Head_total,Head),
	get_forward_invariant(Head,([Phase|Chain_rev],_),Forward_hash,Forward_inv),
	chain_cost(Head,[Phase|Chain],(Forward_hash,Forward_inv2),Cost,Cs),
	Forward_inv==Forward_inv2,!.
%cacheing multiple chains
compress_chain_costs([multiple(Phase,Tails)],Chain_rev,Head_total,Head,Cost,Cs):-
	copy_term(Head_total,Head),
	get_forward_invariant(Head,([Phase|Chain_rev],_),Forward_hash,Forward_inv),
	chain_cost(Head,[multiple(Phase,Tails)],(Forward_hash,Forward_inv2),Cost,Cs),
	Forward_inv==Forward_inv2,!.

	
compress_chain_costs([Base_case],Chain_rev,Head_total,Head,Cost,Cs_base):-
	number(Base_case),!,
	copy_term(Head_total,Head),
	get_forward_invariant(Head,([Base_case|Chain_rev],_),Forward_hash,Forward_inv),
	profiling_start_timer(equation_cost),
	get_loop_cost(Head,[],(Forward_hash,Forward_inv),Base_case,Cost),
	profiling_stop_timer_acum(equation_cost,_),
	loop_ph(Head,(Base_case,_),[],Cs,_,_),
	ut_flat_list([Forward_inv,Cs],Cs_base),
	assert(chain_cost(Head,[Base_case],(Forward_hash,Forward_inv),Cost,Cs_base)).


compress_chain_costs([multiple(Phase,Tails)],Chain_rev,Head_total,Head,Cost_next_simple,Cs_next):-
	number(Phase),!,
 	copy_term(Head_total,Head),
 	maplist(compress_chain_costs_aux([Phase|Chain_rev],Head_total,Call),Tails,Costs_prev,Css_prev),
	nad_list_lub(Css_prev,Cs_prev),
	cstr_or_compress(Costs_prev,Cost_prev),
	
	get_forward_invariant(Head,([Phase|Chain_rev],_),Forward_hash,Forward_inv),
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
    
    (get_param(debug,[])->print_header('Simplifying cost structure of chain ~p ~n',[[multiple(Phase,Tails)]],4);true),
    
 	cstr_simplify(Cost_next,Cost_next_simple),
 	Head=..[_|EVars],
 	%prepare  information for next iteration
	nad_project_group(EVars,Cs_total,Cs_next),
	assert(chain_cost(Head,[multiple(Phase,Tails)],(Forward_hash,Forward_inv),Cost_next_simple,Cs_next)).


%multiple recursion case
compress_chain_costs([multiple(Phase,Tails)],Chain_rev,Head_total,Head,Cost,Cs_next):-
	copy_term(Head_total,Head),
	maplist(compress_chain_costs_aux([Phase|Chain_rev],Head_total,Call),Tails,Costs_prev,_Css_prev),
	%nad_list_lub(Css_prev,_Cs_prev),
	profiling_start_timer(loop_phases),
	copy_term((Call,Costs_prev),(Head,Costs_prev2)),
	get_forward_invariant(Head,([Phase|Chain_rev],_),Hash_local_inv,Local_inv),	
	partial_backward_invariant([multiple(Phase,Tails)],Head,(Hash_local_inv,Local_inv),Entry_pattern,_),
	compute_multiple_rec_phase_cost(Head,Phase,[Phase|Chain_rev],[multiple(Phase,Tails)],Costs_prev2,Cost),
	print_phase_cost(Phase,Head,[],Cost),

	profiling_stop_timer_acum(loop_phases,_),
	nad_list_glb([Local_inv,Entry_pattern],Cs_next),
	
	get_forward_invariant(Head,([Phase|Chain_rev],_),Forward_hash,Forward_inv),
	assert(chain_cost(Head,[multiple(Phase,Tails)],(Forward_hash,Forward_inv),Cost,Cs_next)).	


 compress_chain_costs([Phase|Chain],Chain_rev,Head_total,Head,Cost_next_simple,Cs_next):-
	number(Phase),
 	copy_term(Head_total,Head),
 	compress_chain_costs(Chain,[Phase|Chain_rev],Head_total,Call,Cost_prev,Cs_prev),	
	get_forward_invariant(Head,([Phase|Chain_rev],_),Forward_hash,Forward_inv),
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
    
    (get_param(debug,[])->print_header('Simplifying cost structure of chain ~p ~n',[[Phase|Chain]],4);true),
 	cstr_simplify(Cost_next,Cost_next_simple),
 	Head=..[_|EVars],
 	%prepare  information for next iteration
	nad_project_group(EVars,Cs_total,Cs_next),
	assert(chain_cost(Head,[Phase|Chain],(Forward_hash,Forward_inv),Cost_next_simple,Cs_next)).
	

% compute the phase cost independently
compress_chain_costs([Phase|Chain],Chain_rev,Head_total,Head,Cost_next_simple,Cs_next):-
	\+get_param(linear_phase_strategy,[chain]),
	copy_term(Head_total,Head),
	copy_term(Head_total,Call),
	compress_chain_costs(Chain,[Phase|Chain_rev],Head_total,Call,Cost_prev,Cs_prev),
	profiling_start_timer(loop_phases),
	compute_phase_cost(Head,[Call],Phase,[Phase|Chain_rev],[Phase|Chain],Cost),
	
	print_phase_cost(Phase,Head,[Call],Cost),
	profiling_stop_timer_acum(loop_phases,_),
	
	profiling_start_timer(chain_solver),
	%get information of the phase and later phases
	get_all_phase_information(Head,Call,[Phase|Chain_rev],Cs_list),
	nad_list_glb([Cs_prev|Cs_list],Cs_total),
	% combine the upper bound and lower bound final constraints separately
	Cost_prev=cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands_prev,BConstant_prev),
	Cost=cost(Ub_fconstrs1,Lb_fconstrs1,Iconstrs1,Bsummands1,BConstant1),
	append(Ub_fconstrs,Ub_fconstrs1,Ub_fconstrs_total),
	append(Lb_fconstrs,Lb_fconstrs1,Lb_fconstrs_total),
	max_min_fconstrs_in_chain(Ub_fconstrs_total,[Phase|Chain],Cs_total,Head,Ub_fconstrs_new,Ub_iconstrs_extra),
	(get_param(linear_phase_strategy,[mixed])->
		no_lost_constraints(Ub_fconstrs,Ub_fconstrs_new)
		;
		true
	),!,
	max_min_fconstrs_in_chain(Lb_fconstrs_total,[Phase|Chain],Cs_total,Head,Lb_fconstrs_new,Lb_iconstrs_extra),
	% put together the original non-final constraints (Aux_exps) and the newly created
	ut_flat_list([Ub_iconstrs_extra,Lb_iconstrs_extra,Iconstrs,Iconstrs1],Aux_exps_new),
	%the cost is the sum of the individual costs
	append(Bsummands_prev,Bsummands1,Bsummands_total),
	cexpr_simplify_ctx_free(BConstant_prev+BConstant1,BConstant2),
	Cost_next=cost(Ub_fconstrs_new,Lb_fconstrs_new,Aux_exps_new,Bsummands_total,BConstant2),
	% simplify resulting cost structure
	(get_param(debug,[])->print_header('Simplifying cost structure of chain ~p ~n',[[Phase|Chain]],4);true),
	cstr_simplify(Cost_next,Cost_next_simple),
	Head=..[_|EVars],
	%prepare  information for next iteration
	nad_project_group(EVars,Cs_total,Cs_next),
	
	get_forward_invariant(Head,([Phase|Chain_rev],_),Forward_hash,Forward_inv),
	assert(chain_cost(Head,[Phase|Chain],(Forward_hash,Forward_inv),Cost_next_simple,Cs_next)),
	profiling_stop_timer_acum(chain_solver,_).
	
	
% use multiple recursion method for linear chains	
compress_chain_costs([Phase|Chain],Chain_rev,Head_total,Head,Cost,Cs_next):-
	get_param(linear_phase_strategy,[Mode]),member(Mode,[chain,mixed]),!,
	copy_term(Head_total,Head),
	compress_chain_costs(Chain,[Phase|Chain_rev],Head_total,Call,Cost_prev,_Cs_prev),
	%nad_list_lub(Css_prev,_Cs_prev),
	profiling_start_timer(loop_phases),
	copy_term((Call,Cost_prev),(Head,Cost_prev2)),
	get_forward_invariant(Head,([Phase|Chain_rev],_),Hash_local_inv,Local_inv),	
	partial_backward_invariant([Phase|Chain],Head,(Hash_local_inv,Local_inv),Entry_pattern,_),
	
	compute_multiple_rec_phase_cost(Head,Phase,[Phase|Chain_rev],[Phase|Chain],[Cost_prev2],Cost),
	print_phase_cost(Phase,Head,[],Cost),

	profiling_stop_timer_acum(loop_phases,_),
	nad_list_glb([Local_inv,Entry_pattern],Cs_next),
	
	get_forward_invariant(Head,([Phase|Chain_rev],_),Forward_hash,Forward_inv),
	assert(chain_cost(Head,[Phase|Chain],(Forward_hash,Forward_inv),Cost,Cs_next)).
	
	
compress_chain_costs_aux(Chain_rev,Head_total,Head,Chain,Cost,Cs):-
	compress_chain_costs(Chain,Chain_rev,Head_total,Head,Cost,Cs).

copy_call_costs_and_inv(Call,Cost_prev,Cs_prev,Call2,Cost_prev2,Cs_prev2):-
	copy_term((Call,Cost_prev,Cs_prev),(Call2,Cost_prev2,Cs_prev2)).

no_lost_constraints(Ub_fconstrs,Ub_fconstrs_new):-
	foldl(bconstr_accum_bounded_set,Ub_fconstrs,[],Set_old),
	foldl(bconstr_accum_bounded_set,Ub_fconstrs_new,[],Set_new),
	difference_sl(Set_old,Set_new,Lost),
	(Lost=[]->
		true
		;
		 print_changed_to_chain_method_warning(Lost),
		 fail
	 ).
	
%! get_all_phase_information(+Head:term,Call:term,+Part_chain:chain,-Phi_list:list(polyhedron)) is det
% Obtain:
%  * The transitive closure of the phase or the phase definition (depending on whether
%    it is iterative or not. 
%  * The forward invariant
%  * The phase information at the beginning of the phase
%  * The phase information at the end of the next phase
% and put it all together in a list
get_all_phase_information(Head,Call,[Lg|More],Phi_list):-
	get_forward_invariant(Head,([Lg|More],_),_,Local_inv),
	(
	phase_transitive_closure(Lg,_,Head,Call,Cs_transitive)
	 ;
	loop_ph(Head,(Lg,_),[Call],Cs_transitive,_,_)
	),
	(phase_loop(Lg,_,Head,_,Cs_extra) ; Cs_extra=[]),!,
	Phi_list=[Local_inv,Cs_transitive,Cs_extra].





