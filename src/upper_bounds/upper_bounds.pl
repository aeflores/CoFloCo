/** <module> upper_bounds

This is the main module that performs upper bound computation.
It basically calls the chain_solver.pl for each chain in a given SCC
and calls ub_solver.pl to obtain closed upper bound expressions.

Afterwards, it compresses the upper bounds within each 
external call pattern (if these exists) to obtain external upper bounds
that can be passed on to the callers.

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
%:- use_module(ub_solver,[solve_system/5]).

:- use_module('../db',[
		  external_call_pattern/5,
		  add_upper_bound/3,
		  upper_bound/4,
		  add_external_upper_bound/3,
		  add_closed_upper_bound/3,
		  add_closed_lower_bound/3,
		  add_single_closed_upper_bound/2,
		  closed_upper_bound/4]).

:- use_module('../refinement/invariants',[backward_invariant/4]).
:- use_module('../refinement/chains',[chain/3]).
:- use_module('../utils/cofloco_utils',[bagof_no_fail/3]).
:- use_module('../utils/cost_expressions',[cexpr_simplify/3,cexpr_max/2]).
:- use_module('../utils/cost_structures',[cstr_maxminimization/4,cstr_join_equal_top_expressions/2]).


%! compute_upper_bound_for_scc(+Head:term,+RefCnt:int) is det
% compute an upper bound for each chain
% then, compress the upper bounds for the chains that have been grouped into
% external call patterns
compute_upper_bound_for_scc(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	compute_chain_upper_bound(Head,Chain),
	fail.

compute_upper_bound_for_scc(Head,RefCnt):-
	compress_upper_bounds_for_external_calls(Head,RefCnt).

%! compute_chain_upper_bound(+Head:term,+Chain:chain) is det
% compute an upper bound for a chain,
% simplify it according to the information of the backward invariant
% and store it,
compute_chain_upper_bound(Head,Chain):-
	compute_chain_cost(Head,Chain,UB),!,  
	cstr_join_equal_top_expressions(UB,UB2),
	add_upper_bound(Head,Chain,UB2).
compute_chain_upper_bound(Head,Chain):-
	throw(fatal_error('failed to compute chain bound',Head,Chain)).
	
%! compute_closed_bound(+Head:term) is det
% compute a closed bound for each cost structure that has been previously inferred
% and store it
compute_closed_bound(Head):-
	upper_bound(Head,Chain,_Vars,Cost),
	backward_invariant(Head,(Chain,_),_,_Head_Pattern),
	cstr_maxminimization(Cost,max,UB,simple),
	%cexpr_simplify(UB,Head_Pattern,UB1),
	cstr_maxminimization(Cost,min,LB,complete),
	add_closed_upper_bound(Head,Chain,UB),
	%cexpr_simplify(LB,Head_Pattern,LB1),
	add_closed_lower_bound(Head,Chain,LB),
	fail.
compute_closed_bound(_Head).

	
%! compress_upper_bounds_for_external_calls(+Head:term,+RefCnt:int) is det
% For each external call pattern, it computes an upper bound and store it
% as a external_upper_bound/3.
% If there are no expternal call patterns, it does nothing.
%
% Each call pattern contains a set of chains. The upper bound (cost structure)
% is obtained by compressing the upper bound of these chains into one.
%compress_upper_bounds_for_external_calls(Head,RefCnt):-
%	external_call_pattern(Head,(Precondition_id,RefCnt),_Terminating,Components,Inv),
%	bagof_no_fail(Cost_structure,Chain^E1^(
%		    member(Chain,Components),
%	        upper_bound(Head,Chain,E1,Cost_structure)
%	        ),Cost_structures),       
%	compress_cost_structures(Cost_structures,Head,Inv,Final_cost_structure),
%%	add_external_upper_bound(Head,Precondition_id,Final_cost_structure),
%	fail.
compress_upper_bounds_for_external_calls(_,_).	

%! compute_single_closed_bound(+Head:term,-SimpleExp:cost_expression) is det
% compute a closed bound that is the maximum of all the closed bounds of all the chains in a SCC Head
compute_single_closed_bound(Head,SimpleExp):-
	bagof_no_fail(CExp,
		Chain^E1^closed_upper_bound(Head,Chain,E1,CExp),CExps),
	cexpr_max(CExps,Max),
	cexpr_simplify(Max,[],SimpleExp),!,
	add_single_closed_upper_bound(Head,SimpleExp).
	

