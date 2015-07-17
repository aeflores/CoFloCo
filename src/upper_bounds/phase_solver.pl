/** <module> phase_solver

This module computes the cost structure of a phase in terms of the variables 
at the beginning and the end of the phase.
The internal elements of the cost structure are directly expressed 
in terms of the initial values of the chain.

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

:- module(phase_solver,[compute_phases_cost/5,init_phase_solver/0]).

:- use_module(constraints_maximization,[
					maximize_top_expressions_in_phase/5]).
					
:- use_module(cost_equation_solver,[get_equation_cost/5]).
		
				      
:- use_module('../db',[
			   phase_loop/5,
		       loop_ph/6]).
:-use_module('../refinement/invariants',[
				  backward_invariant/4,
			      forward_invariant/4]).
:- use_module('../IO/params',[get_param/2]).
:- use_module('../utils/cost_structures',[extend_variables_names/3]).			
		      

:- use_module(stdlib(set_list)).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_increase/3]).

%! phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cost_structure)
% store the cost structure of a phase given a local invariant
% for cacheing purposes
:- dynamic  phase_cost/5.



%! init_phase_solver is det
% clear all the intermediate results
init_phase_solver:-
	retractall(phase_cost(_,_,_,_,_,_)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_phases_cost(+Phases:list(phase),+Chain:chain,+Head:term,+Call:term,-Costs:list(cost_structure)) is det
% compute cost structures for the phases Phases that belong to Chain.
% the internal parts of the cost structure are directly expressed in terms of the input variables of the chain
% the constraints of the cost structure are expressed in terms of the variables at the beginnig and end of the chain (Head and Call)
compute_phases_cost([],_,_,_,[]).
compute_phases_cost([Phase|More],Chain,Head,Call,[Cost|Costs]):-
	%get all kinds of invariants
	%backward_invariant(Head_total,(Chain,_),_,Head_patt),
	forward_invariant(Head,([Phase|More],_),Forward_inv_hash,Forward_inv),
	%obtain a cost structure in terms of the variables at the beginning and end of the phase
	compute_phase_cost(Phase,Head,Call,(Forward_inv_hash,Forward_inv),Cost),	
	compute_phases_cost(More,Chain,Head,Call,Costs).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! compute_phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cost_structure) is det
% Obtain the cost of a phase given a forward invariant.
% if the phase is non-iterative, the cost is the cost of the equation, otherwise:
% * get the cost of all the equations
% * put each cost into a new loop
% * try to take loops out by inductive compression
% * try to compress constraints from different loops
compute_phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost):-
	phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv2),Cost),
	Forward_inv2==Forward_inv,!,
	counter_increase(compressed_phases1,1,_).
% in a non-iterative phase, we just obtain the cost of the equation
compute_phase_cost(Non_it,Head,Call,(Forward_hash,Forward_inv),Cost):-
	number(Non_it),	
	profiling_start_timer(equation_cost),
	get_equation_cost(Head,Call1,(Forward_hash,Forward_inv),Non_it,Cost),
	(Call1\=none->Call1=Call;true),
	profiling_stop_timer_acum(equation_cost,_),
	assert(phase_cost(Non_it,Head,Call,(Forward_hash,Forward_inv),Cost)).

compute_phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost):-
    %get the cost of each iterative component of the phase	
	profiling_start_timer(equation_cost),
	maplist(get_equation_loop_cost(Head,Call,(Forward_hash,Forward_inv)),Phase,Costs),
	profiling_stop_timer_acum(equation_cost,_),
	maximize_top_expressions_in_phase(Costs,Head,Call,Phase,Cost),
	assert(phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost)).

get_equation_loop_cost(Head,Call,(Forward_hash,Forward_inv),Eq_id,cost(Top_exps1,Aux_exps1,Bases1,Base1)):-
	get_equation_cost(Head,Call,(Forward_hash,Forward_inv),Eq_id,Cost),
	extend_variables_names(Cost,it(Eq_id),cost(Top_exps1,Aux_exps1,Bases1,Base1)).
	
	