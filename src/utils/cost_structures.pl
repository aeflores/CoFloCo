/** <module> cost_structures

 This module implements the predicates that simplify
 cost structures.

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


:- module(cost_structures,[
		cost_structure_simplify/3,
		simplify_or_cost_structure/6,
		compress_cost_structures/4]).

:- use_module('../upper_bounds/constraints_maximization',[
				  compress_or_constraints/4]).	
:- use_module(cost_expressions,[cexpr_simplify/3]).	
:- use_module('../utils/cost_expressions',[cexpr_simplify/3,cexpr_max/2]).	
:- use_module(stdlib(set_list)).
	
%! compress_cost_structures(+Cs_list:list(cost_structure),+Inv:polyhedron,-Cost_structure:cost_structure) is det
% obtain a cost structure that is a safe approximation of the disjuntion of the cost
% structures in Cs_list
compress_cost_structures(Cs_list,Head,Inv,cost(Exp1,Loops1,Norms3)):-
    maplist(get_cost_structure_components,Cs_list,Exps,Loops,Norms),
    cexpr_simplify(max(Exps),Inv,Exp1),
    maplist(maplist(normalize_norm),Norms,Norms1),
    maplist(from_list_sl,Norms1,Norms2),
 %   unions_sl(Norms2,Norms3),
   compress_or_constraints(Norms2,Head,none,Norms3),
    append(Loops,Loops1).

normalize_norm(norm(Its,Exp),norm(Its1,Exp)):-
	from_list_sl(Its,Its1).

get_cost_structure_components(cost(Exp,Loops,Norms),Exp,Loops,Norms).
	
%! cost_structure_simplify(+Cost_structure:cost_structure,+Ctx:polyhedron,-Cost_structure:cost_structure) is det
% simplify the cost structure Cost_structure.
% Simplify the base expressions and the loops. If some loops can be eliminated, remove the corresponding
% iteration variables from the norms
cost_structure_simplify(cost(Exp,Loops,Norms),Ctx,cost(Exp2,Loops3,Norms2)):-
		       cexpr_simplify(Exp,Ctx,Exp2),
		       find_removable_it_vars(Norms,[],It_vars_set),
		       exclude(loop_contains(It_vars_set),Loops,Loops2),
		       ce_loops_simplify(Loops2,Ctx,Loops3,It_vars_set,Removed_it_vars),
		       ce_norms_simplify(Norms,Ctx,Removed_it_vars,[],Norms2).
		       
%! simplify_or_cost_structure(+Loops:list(loop_cost),+NormsList:list(list(norm)),+Ctx:polyhedron,-Removed_it_vars:list_set(var),-Loops2:list(loop_cost),-NormsList2:list(list(norm))) is det
% Simplify the loops Loops. If the content of a loop is empty, it can be eliminated. Then remove the corresponding
% iteration variables from the norms and collect the removed iteration variables in Removed_it_vars
%
%  * Note that NormsList is a list of list of norms
simplify_or_cost_structure(Loops,NormsList,Ctx,Removed_it_vars,Loops2,NormsList2):-
	    ce_loops_simplify(Loops,Ctx,Loops2,[],Removed_it_vars),
	    maplist(ce_norms_simplify_1(Ctx,Removed_it_vars,[]),NormsList,NormsList2).

	

%! ce_loops_simplify(+Loops:list(loop_cost),+Ctx:polyhedron,-Loops_out:list(loop_cost),+Rem_it_vars1:list(var),-Rem_it_vars_out:list(var)) is det
% Simplify a list of loop costs
% First simplify the internal cost. If the resulting simplified cost is 0, we can remove the loop completely.
% We record the removed iteration variables to be able to update the norms in the next level.
ce_loops_simplify([],_,[],Rem_it_vars,Rem_it_vars).
ce_loops_simplify([loop(It_var,Exp,InternalLoops,Norms)|Loops],Ctx,Loops_out,Rem_it_vars1,Rem_it_vars_out):-
	      cexpr_simplify(Exp,Ctx,Exp2),
	      find_removable_it_vars(Norms,[],Rem_it_vars_internal1),
	      exclude(loop_contains(Rem_it_vars_internal1),InternalLoops,InternalLoops2),
	      ce_loops_simplify(InternalLoops2,Ctx,InternalLoops3,Rem_it_vars_internal1,Rem_it_vars_internal2),
	      ce_norms_simplify(Norms,Ctx,Rem_it_vars_internal2,[],Norms2),
	      ( (Exp2==0, InternalLoops3=[])->
		 Loops_out=Loops2,
		 insert_sl(Rem_it_vars1,It_var,Rem_it_vars2)
	      ;
		Loops_out=[loop(It_var,Exp2,InternalLoops3,Norms2)|Loops2],
		Rem_it_vars2=Rem_it_vars1
	      ),
	      ce_loops_simplify(Loops,Ctx,Loops2,Rem_it_vars2,Rem_it_vars_out).



%! ce_norms_simplify(+Norms:list(norm),-Ctx:polyhedron,+Removed_its:list(var),+Norms_accum:list(norm),-Norms_out:list(norm)) is det
% remove the iteration variables Removed_its from each norm in Norms.
% if the transformed norm is empty (no iteration variables) we discard it.
ce_norms_simplify([],_,_,Norms2,Norms2).
ce_norms_simplify([norm(It_vars,Exp)|Norms],Ctx,Removed_its,Norms_accum,Norms_out):-
	from_list_sl(It_vars,It_vars1),
	difference_sl(It_vars1,Removed_its,It_vars2),
	(It_vars2=[]->
	  ce_norms_simplify(Norms,Ctx,Removed_its,Norms_accum,Norms_out)
	;
	  ce_norms_simplify(Norms,Ctx,Removed_its,[norm(It_vars2,Exp)|Norms_accum],Norms_out)
	).
	
ce_norms_simplify_1(Ctx,Removed_it_vars,Norm_accum,Norms,Norms2):-
	ce_norms_simplify(Norms,Ctx,Removed_it_vars,Norm_accum,Norms2).	


	
loop_contains(It_var_set,loop(It_var,_,_,_)):-
	contains_sl(It_var_set,It_var).

%! find_removable_it_vars(+Norms:list(norm),+Accum:list(var),-It_vars_rem:list(var)) is det
% collect the interation variables that are constrained by a norm
% that is 0 or negative.
find_removable_it_vars([],Accum,Accum).
find_removable_it_vars([norm(It_vars,Exp)|More],Accum,It_vars_rem):-
	number(Exp),Exp=<0,!,
	union_sl(It_vars,Accum,Accum2),
	find_removable_it_vars(More,Accum2,It_vars_rem).
find_removable_it_vars([_|More],Accum,It_vars_rem):-
		find_removable_it_vars(More,Accum,It_vars_rem).	
		
