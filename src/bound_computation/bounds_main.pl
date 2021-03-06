/** <module> bounds_main

This is the main module that performs bound computation.
It basically calls the chain_solver.pl for each chain in a given SCC


Afterwards, it compresses the upper bounds within each 
external call pattern (if these exists) to obtain external bounds
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

:- module(bounds_main,[compute_bound_for_scc/3,
			compute_closed_bound/1,
			compute_single_closed_bound/3]).

:- use_module(chain_solver,[compute_chain_cost/3]).
%:- use_module(ub_solver,[solve_system/5]).
:- use_module(cost_structure_solver,[cstr_maxminimization/5]).
:- use_module('../db',[
		  external_call_pattern/5,
		  add_upper_bound/3,
		  upper_bound/4,
		  add_external_upper_bound/3,
		  add_closed_upper_bound/3,
		  add_closed_lower_bound/3,
		  add_single_closed_upper_bound/2,
		  closed_upper_bound/3]).

:- use_module('../refinement/invariants',[backward_invariant/4]).
:- use_module('../refinement/chains',[chain/3]).
:- use_module('../utils/cofloco_utils',[bagof_no_fail/3,zip_with_op/3]).
:- use_module('../utils/cost_expressions',[cexpr_simplify/3]).
:- use_module('../utils/structured_cost_expression',[strexp_simplify_max_min/2,strexp_to_cost_expression/2]).
:- use_module('../utils/cost_structures',[cstr_or_compress/2,
										  cstr_extend_variables_names/3]).

:- use_module('../IO/params',[get_param/2]).

:- use_module(stdlib(numeric_abstract_domains),[nad_list_lub/2]).
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list),[from_list_sl/2]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).

%! compute_bound_for_scc(+Head:term,+RefCnt:int,Last:bool) is det
% compute a bound for each chain
% then, compress the bounds for the chains that have been grouped into
% external call patterns only if we are not at the last scc
compute_bound_for_scc(Head,RefCnt,_Last):-
	chain(Head,RefCnt,Chain),
	compute_chain_bound(Head,Chain),
	fail.
	
compute_bound_for_scc(Head,RefCnt,false):-	
	compress_bounds_for_external_calls(Head,RefCnt).
compute_bound_for_scc(_Head,_RefCnt,true).


%! compute_chain_bound(+Head:term,+Chain:chain) is det
% compute a bound for a chain,
% simplify it according to the information of the backward invariant
% and store it,
compute_chain_bound(Head,Chain):-
	compute_chain_cost(Head,Chain,UB),!,  
	add_upper_bound(Head,Chain,UB).
compute_chain_bound(Head,Chain):-
	throw(fatal_error('failed to compute chain bound',Head,Chain)).
	
%! compress_upper_bounds_for_external_calls(+Head:term,+RefCnt:int) is det
% For each external call pattern, it computes an upper bound and store it
% as a external_upper_bound/3.
% If there are no expternal call patterns, it does nothing.
%
% Each call pattern contains a set of chains. The upper bound (cost structure)
% is obtained by compressing the upper bound of these chains into one.
compress_bounds_for_external_calls(Head,RefCnt):-
	external_call_pattern(Head,(Precondition_id,RefCnt),_Terminating,Components,_Inv),
	bagof_no_fail(Cost_structure,Chain^E1^Cost_structure_1^(
		    member(Chain,Components),
	        upper_bound(Head,Chain,E1,Cost_structure_1),
	        %only extend if there are several
	        (Components\=[_]->
	        	cstr_extend_variables_names(Cost_structure_1,ch(Chain),Cost_structure)
	        	;
	        	Cost_structure_1=Cost_structure
	        )
	        ),Cost_structures),    
	cstr_or_compress(Cost_structures,Final_cost_structure),
	add_external_upper_bound(Head,Precondition_id,Final_cost_structure),
	fail.
compress_bounds_for_external_calls(_,_).		
	
	
	
%! compute_closed_bound(+Head:term) is det
% compute a closed bound for each cost structure that has been previously inferred
% and store it
compute_closed_bound(Head):-
	upper_bound(Head,Chain,_Vars,Cost),
	backward_invariant(Head,(Chain,_),_,Head_Pattern),
	(get_param(compute_ubs,[])->
	  cstr_maxminimization(Cost,max,Head,Head_Pattern,UB),  
	  add_closed_upper_bound(Head,Chain,UB)
	; 
	  true
	),
    (get_param(compute_lbs,[])->
	  cstr_maxminimization(Cost,min,Head,Head_Pattern,LB),
	  add_closed_lower_bound(Head,Chain,LB)
	  ;
	  true
	 ),
	fail.
compute_closed_bound(_Head).

	


%! compute_single_closed_bound(+Head:term,+RefCnt:int,-SimpleExp:cost_expression) is det
% compute a closed bound that is the maximum of all the closed bounds of all the chains in a SCC Head
compute_single_closed_bound(Head,RefCnt,UB1):-
	bagof_no_fail(CExp,
		Chain^closed_upper_bound(Head,Chain,CExp),CExps),
	maplist(zip_with_op(_),Lists,CExps),
		bagof_no_fail(Head_Pattern,
		Chain^X^backward_invariant(Head,(Chain,RefCnt),X,Head_Pattern),Head_Patterns),
	nad_list_lub(Head_Patterns,General_invariant),
	ut_flat_list(Lists,List),
	from_list_sl(List,Set_costs),
	strexp_simplify_max_min(max(Set_costs),Cost_max_min_simple),
	strexp_to_cost_expression(Cost_max_min_simple,UB),
	cexpr_simplify(UB,General_invariant,UB1),
	add_single_closed_upper_bound(Head,UB1).
	

