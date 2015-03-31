/** <module> cost_equation_solver

This module computes the cost structure of one application of a cost equation in terms of 
the input variables and the variables of the recursive call (if there is one)

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


:- module(cost_equation_solver,[get_equation_cost/5,init_cost_equation_solver]).

:- use_module(constraints_maximization,[
			compress_sets_constraints/4,
			maximize_loop/4]).

:- use_module('../db',[eq_ph/8,
			     loop_ph/6,
			     upper_bound/4,
			     external_upper_bound/3]).

:- use_module('../utils/cofloco_utils',[
			get_it_vars_in_loop/2,
			tuple/3]).
:- use_module('../utils/cost_structures',[
					      compress_cost_structures/4]).
:- use_module('../utils/cost_expressions',[
					      cexpr_add_list/2,
					      cexpr_maximize/4,
					      is_linear_exp/1
]).


:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(numeric_abstract_domains),[nad_glb/3,nad_entails/3,nad_consistent_constraints/1]).

%! equation_cost(Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Eq_id:equation_id,Cost:cost_structure)
% store the cost structure of a cost equation application given a local invariant
% for cacheing purposes
:- dynamic equation_cost/5.

%! init_cost_equation_solver
% clear all the stored intermediate results
init_cost_equation_solver:-
	retractall(equation_cost(_,_,_,_,_,_)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! get_equation_cost(+Head:term,+Call:term,+Forward_inv_hash:(int,polyhedron),+Eq_id:equation_id,-Cost:cost_structure) is det
%  Given a cost equation id (Eq_id) , it accesses the definition and computes the cost of an individual equation appication:
%  * each call in the equation is substituted by it cost expression.
%  * the base costs are added and then expressed in terms of the variables of Head
%  * the loops bodies are put together and expressed in terms of the variables of Head
%  * the constraints are compressed and expressed in terms of the variables of Head.
get_equation_cost(Head,Call,(Forward_inv_hash,Forward_inv),Loop_id,Cost):-
	equation_cost(Head,Call,(Forward_inv_hash,Forward_inv2),Loop_id,Cost),
	Forward_inv==Forward_inv2,!.

get_equation_cost(Head,Call,(Forward_inv_hash,Forward_inv),Loop_id,Final_cost):-
    loop_ph(Head,(Loop_id,_),Call,Inv,Eqs,_),
    maplist(get_equation_cost_1(Head,Call,Forward_inv),Eqs,Costs),
    nad_glb(Forward_inv,Inv,Inv1),
    compress_cost_structures(Costs,(Head,Call),Inv1,Final_cost),
    assert(equation_cost(Head,Call,(Forward_inv_hash,Forward_inv),Loop_id,Final_cost)).
    
    
 get_equation_cost_1(Head,Call,Forward_inv,Eq_id,Cost):-
     (Call==none->   
       eq_ph(Head,(Eq_id,_),C, Base_Calls,[],_,Phi,_)
       ;
       eq_ph(Head,(Eq_id,_),C, Base_Calls,[Call],_,Phi,_)
       ),
	nad_glb(Forward_inv,Phi,Phi1),
	maplist(substitute_call,Base_Calls,Base_costs,Loops,Constraints),
    term_variables((Head,Call),TVars),
	term_variables(Head,EVars),
	%base cost
	cexpr_add_list([C|Base_costs],CExp),
	cexpr_maximize(CExp,EVars,Phi1,Base_cost_out),
	%loops
	ut_flat_list(Loops,Loops_flat),
	maximize_loop(EVars,Phi1,loop(_,0,Loops_flat,[]),loop(_,0,Loops_out,[])),
	%loop constraints
	compress_sets_constraints(Constraints,TVars,Phi1,Constraints_out),
	Cost=cost(Base_cost_out,Loops_out,Constraints_out).


substitute_call((Call,chain(Chain)),Base_cost,Loops,Constraints) :-
    upper_bound(Call,Chain,_Hash,cost(Base_cost,Loops,Constraints)).
substitute_call((Call,external_pattern(Id)),Base_cost,Loops,Constraints) :-
	external_upper_bound(Call,Id,cost(Base_cost,Loops,Constraints)).








