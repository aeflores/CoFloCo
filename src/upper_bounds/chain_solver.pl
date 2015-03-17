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
    maximize_constraints_set/4,
	compress_sets_constraints/4]).

:-use_module('../db',[phase_loop/5,loop_ph/6]).
:-use_module('../refinement/invariants',[backward_invariant/4,
			      phase_transitive_closure/5,
			      forward_invariant/4]).
:- use_module('../utils/polyhedra_optimizations',[nad_project_group/3]).			      
:- use_module('../utils/cofloco_utils',[norm_contains_vars/2]).
:- use_module('../utils/cost_expressions',[cexpr_simplify_ctx_free/2,
					      cexpr_add_list/2]).

:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(numeric_abstract_domains),[
						nad_entails/3,
						nad_list_lub/2,
						nad_list_glb/2,
						nad_lub/6,
						nad_glb/3,
						nad_project/3,
						nad_consistent_constraints/1]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_get_info/3,
				 profiling_stop_timer/2,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_increase/3]).		



%! compute_chain_cost(+Head:term,+Chain:chain,-Cost:cost_structure) is det
% compute the cost structure of a chain.
%   * Compute the cost of each phase
%   * compress the norms of different phases
compute_chain_cost(Head,Chain,cost(Base,Loops,Norms_out)):-
	profiling_start_timer(loop_phases),
	compute_phases_cost(Chain,Chain,Head,Call,Cost_exprs),
	profiling_stop_timer_acum(loop_phases,_),
	compress_phases(Cost_exprs,cost(Base,Loops,Norms)),
	profiling_start_timer(chain_solver),
	compress_chain_constraints(Chain,Norms,Head,Call,Norms_out),
	profiling_stop_timer_acum(chain_solver,_),
	!.



% compress_phases(Costs:list(cost_structure),Cost_out:cost_structure) is det
% Put all the loops together and the norms in a list in inverse order.
% The base costs are all added and simplified
compress_phases(Costs,cost(Base,Loops_flat,Constrs1)):-
	foldl(accum_costs,Costs,cost([],[],[]),cost(Bases,Loops_rev,Constrs)),
	ut_flat_list(Loops_rev,Loops_flat),
	reverse(Constrs,Constrs1),
	cexpr_add_list(Bases,CExp),
	cexpr_simplify_ctx_free(CExp,Base).

accum_costs(cost(Base,Loops,C),cost(Bases,Loops_list,Cs),cost([Base|Bases],[Loops|Loops_list],[C|Cs])).



%! compress_chain_constraints(+Chain:chain,+Norms_list:list(list(norm)),+Head_total:term,+Call:term,-Norms_out:list(norm)) is det
%  We have a set of norms for each phase and we want to express all of them in terms
% of the entry variables. At the same time, we try to compress them to gain precision.
%
% we start from the base case to the outmost phase.
% At each step we try to compress the norms from the previous phases 
% witht the ones of the current phase and express them in terms of the initial variables
% of the phase.
compress_chain_constraints([Lg|More],[Norms|Norms_list],Head_total,Call,Norms_out):-!,
	copy_term(Head_total,Head),
	% put norms expressed in terms of Head
	maplist(substitute_norm_expression(Head_total,Head),Norms,Norms1),
	% get all invariants together
	get_all_base_case_information(Head,[Lg|More],Phi),
	compress_chain_constraints_1(More,Norms1,Norms_list,Head,Head_total,Call,Phi,Norms_out).

compress_chain_constraints_1([],Norms_out,[],Prev_entry,Head_total,_Call,_Cs_prev,Norms_out):-
	Head_total=Prev_entry.

compress_chain_constraints_1([Lg|More],Norms,[Norms1|Norms_list],Prev_entry,Head_total,Call,Cs_prev,Norms_out):-!,
	copy_term((Head_total,Call),(Head,Prev_entry)),
	% express the norms of the phase in terms of a new Head and the previous Head
	maplist(substitute_norm_expression((Head_total,Call),(Head,Prev_entry)),Norms1,Norms2),
	% get all the corresponding invariants
	get_all_phase_information(Head,Prev_entry,[Lg|More],Cs_list),
	nad_list_glb([Cs_prev|Cs_list],Cs_total),
	%ut_flat_list([Cs_prev|Cs_list],Cs_total), %cheap glb
	
	Head=..[_|EVars],
	Prev_entry=..[_|CVars],
	%compress the accumulated norms and the norms in the current phase
	compress_two_sets_constraints_with_filtering(Norms,Norms2,CVars,Cs_total,EVars,Compressed),
	nad_project_group(EVars,Cs_total,Cs_next),
	compress_chain_constraints_1(More,Compressed,Norms_list,Head,Head_total,Call,Cs_next,Norms_out).


%! compress_two_sets_constraints_with_filtering(+Set1:list_set(norm),+Set2:list_set(norm),+Common_vars:list(var),+Cs:polyhedron,+Vars:list(var),-Compressed:set_list(norm)) is det
% try to find expressions that compress pairs of norms from Set1 and Set2.
% express both the original norms and the compressed norms in term of Vars.
%
% Phi is the polyhedron that defines the relations between variables.
%
% Common_vars are the variables that might appear in constraints of both sets.
% avoid trying to compress norms that do not depend on the common variables.
compress_two_sets_constraints_with_filtering(Set1,Set2,Common_vars,Cs,Vars,Compressed):-
	from_list_sl(Common_vars,Common_vars_set),
	partition(norm_contains_vars(Common_vars_set),Set2,DepNorms,Non_depNorms),
	maximize_constraints_set(Non_depNorms,Vars,Cs,No_dep_maximized),
	compress_sets_constraints([Set1,DepNorms],Vars,Cs,Compressed_dep),
	union_sl(Compressed_dep,No_dep_maximized,Compressed).
	

substitute_norm_expression(Vars1,Vars2,norm(Its,E),norm(Its,E2)):-
	copy_term((Vars1,E),(Vars2,E2)).

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


