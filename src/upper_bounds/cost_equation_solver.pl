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
			max_min_constrs_in_cost_equation/6]).

:- use_module('../db',[eq_ph/8,
			     loop_ph/6,
			     upper_bound/4,
			     external_upper_bound/3]).

:- use_module('../utils/cofloco_utils',[tuple/3]).
:- use_module('../utils/cost_structures',[cstr_extend_variables_names/3,
			cstr_empty/1,
			cstr_join_equal_top_expressions/2]).
:- use_module('../utils/cost_expressions',[cexpr_simplify_ctx_free/2]).


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
    loop_ph(Head,(Loop_id,_),Call,_Inv,Eqs,_),
    maplist(get_equation_cost_1(Head,Call,Forward_inv),Eqs,Costs),
    (Costs=[]->
    	cstr_empty(Final_cost)
    	;
    	Costs=[Final_cost]
    	),
  %  nad_glb(Forward_inv,Inv,Inv1),
  %  compress_cost_structures(Costs,(Head,Call),Inv1,Final_cost),
    assert(equation_cost(Head,Call,(Forward_inv_hash,Forward_inv),Loop_id,Final_cost)).
    
    
 get_equation_cost_1(Head,Call,Forward_inv,Eq_id,Cost):-
     (Call==none->   
       eq_ph(Head,(Eq_id,_),Basic_cost, Base_calls,[],_,Phi,_)
       ;
       eq_ph(Head,(Eq_id,_),Basic_cost, Base_calls,[Call],_,Phi,_)
       ),
	nad_glb(Forward_inv,Phi,Phi1),
	term_variables((Head,Call),TVars),
	foldl(accumulate_calls,Base_calls,(Basic_cost,1),(cost(Ub_tops,Lb_tops,Auxs,Bases,Base),_)),
	reverse(Base_calls,Base_calls_inv),
	maplist(term_variables,Base_calls_inv,Base_calls_vars),
	maplist(from_list_sl,Base_calls_vars,Base_calls_sets),
	max_min_constrs_in_cost_equation(Ub_tops,Base_calls_sets,Phi1,TVars,New_Ub_tops,New_auxs1),
	max_min_constrs_in_cost_equation(Lb_tops,Base_calls_sets,Phi1,TVars,New_Lb_tops,New_auxs2),
	ut_flat_list([New_auxs1,New_auxs2,Auxs],New_auxs),
	cstr_join_equal_top_expressions(cost(New_Ub_tops,New_Lb_tops,New_auxs,Bases,Base),Cost).

accumulate_calls((Call,chain(Chain)),(cost(Tops1,LTops1,Auxs1,Bases1,Base1),N),(cost([Tops2|Tops1],[LTops2|LTops1],[Auxs2|Auxs1],Bases,Base),N1)) :-
    N1 is N+1,
    upper_bound(Call,Chain,_Hash,Cost_call),
    cstr_extend_variables_names(Cost_call,n(N),cost(Tops2,LTops2,Auxs2,Bases2,Base2)),
    cexpr_simplify_ctx_free(Base1+Base2,Base),
    append(Bases2,Bases1,Bases).
%substitute_call((Call,external_pattern(Id)),Base_cost,Loops,(Constraints,IConstraints)) :-
%	external_upper_bound(Call,Id,cost(Base_cost,Loops,Constraints,IConstraints)).








