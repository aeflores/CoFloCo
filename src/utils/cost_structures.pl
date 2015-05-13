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
		cost_structure_simplify_it_vars/2,
		compress_cost_structures/4]).

:- use_module('../upper_bounds/constraints_maximization',[
				  compress_or_constraints/5]).	
:- use_module('../IO/params',[get_param/2]).				  
:- use_module(cost_expressions,[cexpr_simplify/3]).	
:- use_module(cofloco_utils,[tuple/3]).	
:- use_module(stdlib(set_list)).
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).
:- use_module(stdlib(utils),[ut_flat_list/2]).

%! compress_cost_structures(+Cs_list:list(cost_structure),+Inv:polyhedron,-Cost_structure:cost_structure) is det
% obtain a cost structure that is a safe approximation of the disjuntion of the cost
% structures in Cs_list
compress_cost_structures(Cs_list,Head,Inv,New_cost):-
    maplist(get_cost_structure_components,Cs_list,Exps,Loops,Norms_INorms),
    maplist(tuple,Norms,INorms,Norms_INorms),
    cexpr_simplify(max(Exps),Inv,Exp1),
    maplist(maplist(sort_it_vars),Norms,Norms1),
    maplist(from_list_sl,Norms1,Norms2),
    maplist(from_list_sl,INorms,INorms1),
    unions_sl(INorms1,INorms2),
    compress_or_constraints(Norms2,Head,none,max,Norms3),
    append(Loops,Loops1),
    cost_structure_simplify_it_vars(cost(Exp1,Loops1,Norms3,INorms2),New_cost).         
    
%! sort_it_vars(+Norm:norm,-Norm1:norm) is det
% sort the iteration variables list so they can be treated as a set.
sort_it_vars(norm(Its,Exp),norm(Its1,Exp)):-
	from_list_sl(Its,Its1).

get_cost_structure_components(cost(Exp,Loops,Norms,INorms),Exp,Loops,(Norms,INorms)).
	
%! cost_structure_simplify(+Cost_structure:cost_structure,+Ctx:polyhedron,-Cost_structure:cost_structure) is det
% simplify the cost structure Cost_structure.
% Simplify the base expressions and the loops. If some loops can be eliminated, remove the corresponding
% iteration variables from the norms
cost_structure_simplify(cost(Exp,Loops,Norms,INorms),Ctx,Cost):-
		       cexpr_simplify(Exp,Ctx,Exp2),
		       find_removable_it_vars(Norms,[],It_vars_set),
		       exclude(loop_contains(It_vars_set),Loops,Loops2),
		       ce_loops_simplify(Loops2,Ctx,Loops3,It_vars_set,Removed_it_vars),
		       ce_norms_simplify(Norms,Ctx,Removed_it_vars,[],Norms2),	
		       ce_norms_simplify(INorms,Ctx,Removed_it_vars,[],INorms2),		       
		       cost_structure_simplify_it_vars(cost(Exp2,Loops3,Norms2,INorms2),Cost).
		       
		       
%! simplify_or_cost_structure(+Loops:list(loop_cost),+NormsList:list(list(norm)),+Ctx:polyhedron,-Removed_it_vars:list_set(var),-Loops2:list(loop_cost),-NormsList2:list(list(norm))) is det
% Simplify the loops Loops. If the content of a loop is empty, it can be eliminated. Then remove the corresponding
% iteration variables from the norms and collect the removed iteration variables in Removed_it_vars
%
%  * Note that NormsList is a list of list of norms
simplify_or_cost_structure(Loops,NormsList,Ctx,Removed_it_vars,Loops2,NormsList2):-
	    ce_loops_simplify(Loops,Ctx,Loops2,[],Removed_it_vars),
	    maplist(ce_norms_simplify_1(Ctx,Removed_it_vars,[]),NormsList,NormsList2).

%! cost_structure_simplify_it_vars(+Cost_structure:cost_structure,-Simplified_cost_structure:cost_structure) is det
% take a cost structure and remove loops and their corresponding iteration variables that are duplicated.
% a loop Loop1 is a duplicate of another Loop2 if they have the same internal cost and the iteration variable
% it2 of Loop2 is binded by all the norm that bind it2  (from loop2).
%
% example: 
%loop(it1,N,[],[]) is a duplicate of loop(it2,N,[],[]) for the following norms:
% norm([it1],X), norm([it1,it2],Y)
% on the contrary loop(it2,N,[],[]) is not a duplicate of loop(it1,N,[],[]) because loop(it1,N,[],[]) has
% an additional norm norm([it1],X).
%
% Finally, if a loop whose cost is guaranteed to be positive has no norm, we know the cost is infinity.
cost_structure_simplify_it_vars(cost(Exp,[],Norms,INorms),cost(Exp,[],Norms,INorms)):-!.     		      
cost_structure_simplify_it_vars(cost(Exp,_,_,_),cost(Exp,[],[],[])):-
          Exp==inf,!.   		      

%FIXME INorms
% deactivated for negative costs
cost_structure_simplify_it_vars(Cost,Cost):-get_param(negative,[]),!.           

cost_structure_simplify_it_vars(cost(Exp,Loops,Norms,INorms),Cost):-	            
		       number_norms(Norms,0,Numbered_norms),
		       group_similar_loops(Loops,Grouped_loops),
		       %remove duplicated loops and return the corresponding it_vars that have to be removed
		       maplist(compress_loop_group(Numbered_norms),Grouped_loops,Resulting_loops_pairs,Removed_it_vars),
		       ut_flat_list(Resulting_loops_pairs,Resulting_loops_pairs_flat),
		       (infinite_loop(Resulting_loops_pairs_flat)->
		          Cost=cost(inf,[],[],[])
		       ;
		       maplist(tuple,_,Resulting_loops,Resulting_loops_pairs_flat),
		       from_list_sl(Resulting_loops,Resulting_loops_set),
		       ut_flat_list(Removed_it_vars,Removed_it_vars_flat),
		       from_list_sl(Removed_it_vars_flat,Removed_it_vars_set),
		       % remove the iteration variables of loops that have been eliminated
		       ce_norms_simplify(Norms,[],Removed_it_vars_set,[],Norms2),
		       from_list_sl(Norms2,Norms2_set),
		       ce_norms_simplify(INorms,[],Removed_it_vars_set,[],INorms2),
		       from_list_sl(INorms2,INorms2_set),
		       Cost=cost(Exp,Resulting_loops_set,Norms2_set,INorms2_set)
		       ).
		       
%! infinite_loop(+Loop_pairs:list((list(int),loop))) is semidet
% The loop pairs are loops annotated with the numbers associated to each norm.
% It succeeds if there is a loop in Loop_pairs that is not binded by any norm
infinite_loop(Loop_pairs):-
  member(([],loop(_,Exp,_,_,_)),Loop_pairs),
  number(Exp),
  Exp > 0.
  
%! number_norms(+Norms:list(norms),+N:int,-Norm_pairs:list((norm,int))) is det
% assign a unique integer identifier to each norm	       
number_norms([],_,[]).
number_norms([norm(Its,Exp)|Norms],N,[(norm(Its,Exp),N)|Norms2]):-
	N1 is N+1,
	number_norms(Norms,N1,Norms2).
	
%! group_similar_loops(Loops:list(loop),Grouped_loops:list(list(loop))) is det 
% group loops that are equal	
group_similar_loops(Loops,Grouped_loops):-
	maplist(get_loop_hash,Loops,Hash_loop_pairs),
	from_pair_list_mm(Hash_loop_pairs,Multimap_loops),
	maplist(tuple,_,Grouped_loops,Multimap_loops).

get_loop_hash(loop(It_var,Exp,InternalLoops,Norms,INorms),(Hash,loop(It_var,Exp,InternalLoops,Norms,INorms))):-
	copy_term((Exp,InternalLoops,Norms,INorms),Term),
	numbervars(Term,0,_),
	term_hash(Term,Hash).

%! compress_loop_group(N_norms:list((norm,int)),Group_loops:list(loop),Loops_out:list((list(int),loop)),Removed_it_vars:list(var)) is det
% given a list of equivalent loops, discard all the loops that are "subsumed" by other loops.
% First, annotate each loop with the norms that contain its iteration variable.
% Then, if the set of norms of one loop L1 is a superset of the norms of a loop L2. We can discard L1.
compress_loop_group(N_norms,Group_loops,Loops_out,Removed_it_vars):-
	maplist(annotate_loop(N_norms),Group_loops,Annotated_loops),
	keep_minimal_loops(Annotated_loops,[],[],Loops_out,Removed_it_vars).
	
% annotate the loops with the norm identifiers	
annotate_loop(N_norms,loop(It_var,Exp,InternalLoops,Norms,INorms),(Set,loop(It_var,Exp,InternalLoops,Norms,INorms))):-
	get_norm_numbers(N_norms,It_var,[],Set).

get_norm_numbers([],_,Accum,Accum2):-
	reverse(Accum,Accum2).
get_norm_numbers([(norm(Its,_),N)|Norms],It_var,Accum,Set):-
	contains_sl(Its,It_var),!,
	get_norm_numbers(Norms,It_var,[N|Accum],Set).
get_norm_numbers([_|Norms],It_var,Accum,Set):-
	get_norm_numbers(Norms,It_var,Accum,Set).	
	
% discard the loops whose norms are a superset of the norms of another loop	
keep_minimal_loops([],Loops,It_vars,Loops,It_vars).
keep_minimal_loops([Loop|Loops],Loops_accum,It_vars_accum,Loops_out,It_vars_out):-
	check_loop(Loops,Loop,Remaining_loops,Loops_to_keep,Rem_it_vars),
	append(Loops_to_keep,Loops_accum,Loops_accum2),
	append(Rem_it_vars,It_vars_accum,It_vars_accum2),
	keep_minimal_loops(Remaining_loops,Loops_accum2,It_vars_accum2,Loops_out,It_vars_out).
	
check_loop([],(Set,Loop),[],[(Set,Loop)],[]).
check_loop([(Set1,Loop1)|Loops],(Set,Loop),[(Set1,Loop1)|Loops],[],[It_var]):-
	difference_sl(Set1,Set,[]),!,
	Loop=loop(It_var,_,_,_,_).
check_loop([(Set1,Loop1)|Loops],(Set,Loop),Loops_rest,Loops_to_keep,[It_var|It_vars1]):-
	difference_sl(Set,Set1,[]),!,
	Loop1=loop(It_var,_,_,_,_),
	check_loop(Loops,(Set,Loop),Loops_rest,Loops_to_keep,It_vars1).
	
check_loop([(Set1,Loop1)|Loops],(Set,Loop),[(Set1,Loop1)|Loops_rest],Loops_to_keep,It_vars):-
	check_loop(Loops,(Set,Loop),Loops_rest,Loops_to_keep,It_vars).


%! ce_loops_simplify(+Loops:list(loop_cost),+Ctx:polyhedron,-Loops_out:list(loop_cost),+Rem_it_vars1:list(var),-Rem_it_vars_out:list(var)) is det
% Simplify a list of loop costs
% First simplify the internal cost. If the resulting simplified cost is 0, we can remove the loop completely.
% We record the removed iteration variables to be able to update the norms in the next level.
ce_loops_simplify([],_,[],Rem_it_vars,Rem_it_vars).
ce_loops_simplify([loop(It_var,Exp,InternalLoops,Norms,INorms)|Loops],Ctx,Loops_out,Rem_it_vars1,Rem_it_vars_out):-
	      Exp=Exp2,
	      find_removable_it_vars(Norms,[],Rem_it_vars_internal1),
	      exclude(loop_contains(Rem_it_vars_internal1),InternalLoops,InternalLoops2),
	      ce_loops_simplify(InternalLoops2,Ctx,InternalLoops3,Rem_it_vars_internal1,Rem_it_vars_internal2),
	      ce_norms_simplify(Norms,Ctx,Rem_it_vars_internal2,[],Norms2),
	      ce_norms_simplify(INorms,Ctx,Rem_it_vars_internal2,[],INorms2),
	      ( (Exp2==0, InternalLoops3=[])->
		 Loops_out=Loops2,
		 insert_sl(Rem_it_vars1,It_var,Rem_it_vars2)
	      ;
		Loops_out=[loop(It_var,Exp2,InternalLoops3,Norms2,INorms2)|Loops2],
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


	
loop_contains(It_var_set,loop(It_var,_,_,_,_)):-
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
		
