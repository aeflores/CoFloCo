/** <module> upper_bounds

This is the main module that performs upper bound computation.
It basically calls the chain_solver.pl for each chain in a given SCC
and calls ub_solver.pl to obtain closed upper bound expressions.

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

:- module(upper_bounds,[compute_upper_bound_for_scc/2,
			compute_closed_bound/1,
			compute_single_closed_bound/2]).

:- use_module(chain_solver,[compute_chain_cost/3]).
:- use_module(ub_solver,[solve_system/3]).

:- use_module('../db',[add_upper_bound/3,
		  upper_bound/4,
		  add_closed_upper_bound/3,
		  non_terminating_chain/2,
		  closed_upper_bound/4]).

:-use_module('../refinement/invariants',[backward_invariant/4]).

:- use_module('../refinement/chains',[chain/3]).

:- use_module('../IO/params',[get_param/2]).
:- use_module('../utils/cofloco_utils',[bagof_no_fail/3]).
:- use_module('../utils/cost_expressions',[cexpr_simplify/3,cexpr_max/2]).
:- use_module('../utils/cost_structures',[cost_structure_simplify/3]).
					 					 
:- use_module(stdlib(utils),[ut_member/2,ut_sort_rdup/2,ut_split_at_pos/4]).
:- use_module(stdlib(numeric_abstract_domains),[nad_project/3]).
:- use_module(stdlib(polyhedra_ppl),[ppl_my_initialize/0]).

%! compute_upper_bound_for_scc(+Head:term,+RefCnt:int) is det
% compute an upper bound for each chain
compute_upper_bound_for_scc(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	compute_chain_upper_bound(Head,Chain),
	fail.
compute_upper_bound_for_scc(_,_).

%! compute_chain_upper_bound(+Head:term,+Chain:chain) is det
% compute an upper bound for a chain,
% simplify it according to the information of the backward invariant
% and store it,
compute_chain_upper_bound(Head,Chain):-	  
	compute_chain_cost(Head,Chain,UB),   
	backward_invariant(Head,(Chain,_),_,Head_Pattern),
	cost_structure_simplify(UB,Head_Pattern,UB2),
	add_upper_bound(Head,Chain,UB2).

%! compute_closed_bound(+Head:term) is det
% compute a closed bound for each cost structure that has been previously inferred
% and store it
compute_closed_bound(Head):-
	upper_bound(Head,Chain,_Vars,Cost),
	backward_invariant(Head,(Chain,_),_,Head_Pattern),
	Head=..[_|Vars],
	solve_system(Cost,Vars,UB),
	cexpr_simplify(UB,Head_Pattern,UB1),
	add_closed_upper_bound(Head,Chain,UB1),
	fail.
compute_closed_bound(_Head).

%! compute_single_closed_bound(+Head:term,-SimpleExp:cost_expression) is det
% compute a closed bound that is the maximum of all the closed bounds of all the chains in a SCC Head
compute_single_closed_bound(Head,SimpleExp):-
	bagof_no_fail(CExp,
		Chain^E1^closed_upper_bound(Head,Chain,E1,CExp),CExps),
	cexpr_max(CExps,Max),
	cexpr_simplify(Max,[],SimpleExp),!.
	


