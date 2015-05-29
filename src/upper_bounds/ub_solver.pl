/** <module> ub_solver

This module solves cost structures into regular cost expressions.
Right now, we take a very simple approach that guarantees
 soundness of the inferred cost expression.
For a discussion of how to solve cost structures
 in a more general way see section 5 of 
"Resource Analysis of Complex Programs with Cost Equations" .

Specific "data types" of this module:
  * it_group:it_group(list(var),list(norm))
    A group of norms that have iteration variables in common
    and the set of iteration variables that the norms contain.

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

:- module(ub_solver,[solve_system/5]).


:- use_module('../IO/params',[get_param/2]).
:- use_module('../utils/cofloco_utils',[
		     zip_with_op/4,
			 tuple/3,
			 sort_with/3,
			 get_it_vars_in_loop/2,
			 assign_right_vars/3]).
:- use_module('../utils/cost_expressions',[
					      cexpr_add_list/2,
					      cexpr_mul/3,
					      cexpr_add/3,
					      cexpr_max/2,
					      cexpr_min/2,
					      cexpr_simplify_aux/3,
					      cexpr_simplify/3,
					      is_linear_exp/1,
					      get_asymptotic_class/2
]).
:- use_module('../utils/polyhedra_optimizations',[nad_entails_aux/3]).

:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_project/3,
						nad_list_lub/2,
						nad_lub/6,
						nad_glb/3,
						nad_consistent_constraints/1]).

:- use_module(stdlib(parsing_writing),[write_sum/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Maximize a explicit cost expression or part of it

%! solve_system(+Cost:cost_structure,+Vars:list(var),Max_Min:flag,-Max:cost_expression) is det
% solve a cost structure Cost into a regular cost expression Max
%  * solve the cost structures inside the loops
%  * solve the constraints of the loops and add the base cost

	
%solve with negative costs!!!
solve_system(cost(Base,Loops,External_constrs,I_External_constrs),Vars,Cs,max,Max):-
	maplist(solve_loop(Vars,Cs,max),Loops,It_vars,It_costs),
	maplist(cexpr_simplify_aux(Cs),It_costs,It_costs_simple),
	split_positive_and_negative(It_costs_simple,It_vars,Cs,It_costs_pos,It_vars_pos,It_costs_neg,It_vars_neg),
	
	filter_ub_constraints(External_constrs,It_vars_pos,External_constrs1),
	group_same_its_constraints(External_constrs1,Cs,max,External_constrs2),
	group_dependant_it_constrs(External_constrs2,It_vars_pos,Grouped_It_vars_pos),
	maplist(zip_with_op(p),It_vars_pos,It_costs_pos,It_pairs_pos),
	maplist(solve_constr_group(It_pairs_pos,Vars,max),Grouped_It_vars_pos,Costs_pos),
	
	filter_lb_constraints(I_External_constrs,It_vars_neg,I_External_constrs1),	
	group_same_its_constraints(I_External_constrs1,Cs,min,I_External_constrs2),
	group_dependant_it_constrs(I_External_constrs2,It_vars_neg,Grouped_It_vars_neg),
	maplist(zip_with_op(p),It_vars_neg,It_costs_neg,It_pairs_neg),
	maplist(solve_constr_group(It_pairs_neg,Vars,min),Grouped_It_vars_neg,Costs_neg),
	
	%remove_zero_costs(It_vars,It_costs_simple_positive,Selected_constrs,It_vars1,It_costs1,External_constrs1),
	append(Costs_neg,Costs_pos,Costs),
	cexpr_add_list([Base|Costs],Max),!.		

/*
solve_system(cost(Base,Loops,External_constrs,I_External_constrs),Vars,Cs,Max_Min,Max):-
	(Max_Min=max->
	   Selected_constrs=External_constrs
	   ;
	   Selected_constrs=I_External_constrs
	 ),
	maplist(solve_loop(Vars,Cs,Max_Min),Loops,It_vars,It_costs),
	maplist(cexpr_simplify_aux(Cs),It_costs,It_costs_simple),
	maplist(avoid_negative_costs(Cs),It_costs_simple,It_costs_simple_positive),
	remove_zero_costs(It_vars,It_costs_simple_positive,Selected_constrs,It_vars1,It_costs1,External_constrs1),
	group_same_its_constraints(External_constrs1,Cs,Max_Min,External_constrs2),
	group_dependant_it_constrs(External_constrs2,It_vars1,Grouped_It_vars),
	maplist(zip_with_op(p),It_vars1,It_costs1,It_pairs),
	maplist(solve_constr_group(It_pairs,Vars,Max_Min),Grouped_It_vars,Costs),
	cexpr_add_list([Base|Costs],Max),!.	
*/

%! solve_loop(+Vars:list(var),+Loop:loop_cost,-It_var:var,-Cost:cost_expression) is det
% solve the cost structure inside the loop Loop and return the cost Cost and
% the iteration variable of the loop It_var
solve_loop(Vars,Cs,Max_Min,loop(It_var,Base,Loops,Constr,IConstr),It_var,Cost):-
	solve_system(cost(Base,Loops,Constr,IConstr),Vars,Cs,Max_Min,Cost).

%! avoid_negative_costs(+Cs:polyhedron,+Cost:cost_expression,-Cost2:cost_expression) is det
% If the body of a loop has negative cost, we approximate to cost 0
% if the body might be negative, we wrap it into a nat() expression
avoid_negative_costs(_,Number,Cost2):-
	number(Number),!,
	(Number< 0->
	   Cost2=0
	   ;
	   Cost2=Number
	).

avoid_negative_costs(Cs,Cost,Cost2):-
	is_linear_exp(Cost),!,
	term_variables((Cs,Cost),Vars),
	(nad_entails_aux(Vars,Cs,[Cost>=0])->
	 	Cost2=Cost
	;
	(nad_entails_aux(Vars,Cs,[Cost=<0])->
	      Cost2=0
	      ;
	      Cost2=nat(Cost)
	)).
	
avoid_negative_costs(_,Cost,nat(Cost)).



split_positive_and_negative([],[],_Cs,[],[],[],[]).
split_positive_and_negative([C|Costs],[It_var|It_vars],Cs,[C|Costs_pos],[It_var|It_vars_pos],Costs_neg,It_vars_neg):-
	is_positive(C,Cs),!,
	split_positive_and_negative(Costs,It_vars,Cs,Costs_pos,It_vars_pos,Costs_neg,It_vars_neg).
	
split_positive_and_negative([C|Costs],[It_var|It_vars],Cs,Costs_pos,It_vars_pos,[C|Costs_neg],[It_var|It_vars_neg]):-
	is_negative(C,Cs),!,	
	split_positive_and_negative(Costs,It_vars,Cs,Costs_pos,It_vars_pos,Costs_neg,It_vars_neg).
	
split_positive_and_negative([C|Costs],[It_var|It_vars],Cs,[nat(C)|Costs_pos],[It_var|It_vars_pos],[min([C,0])|Costs_neg],[It_var|It_vars_neg]):-
	split_positive_and_negative(Costs,It_vars,Cs,Costs_pos,It_vars_pos,Costs_neg,It_vars_neg).
	
is_positive(Exp,_Cs):-
	number(Exp),Exp >= 0,!.
is_positive(Exp,Cs):-
	is_linear_exp(Exp),
	term_variables((Cs,Exp),Vars),
	nad_entails_aux(Vars,Cs,[Exp>=0]),!.
	
is_negative(Exp,_Cs):-
	number(Exp),Exp >= 0,!.
is_negative(Exp,Cs):-
	is_linear_exp(Exp),
	term_variables((Cs,Exp),Vars),
	nad_entails_aux(Vars,Cs,[Exp=<0]),!.	
	
	
filter_ub_constraints(External_constrs,It_vars_keep,External_constrs1):-
	filter_ub_constraints_1(External_constrs,It_vars_keep,[],External_constrs1).
filter_ub_constraints_1([],_,Norms2,Norms2).
filter_ub_constraints_1([norm(It_vars,Exp)|Norms],It_vars_keep,Norms_accum,Norms_out):-
	from_list_sl(It_vars,It_vars1),
	intersection_sl(It_vars1,It_vars_keep,It_vars2),
	(It_vars2=[]->
	  filter_ub_constraints_1(Norms,It_vars_keep,Norms_accum,Norms_out)
	;
	  filter_ub_constraints_1(Norms,It_vars_keep,[norm(It_vars2,Exp)|Norms_accum],Norms_out)
	).
	
filter_lb_constraints(External_constrs,It_vars_keep,External_constrs1):-
	filter_lb_constraints_1(External_constrs,It_vars_keep,[],External_constrs1).
filter_lb_constraints_1([],_,Norms2,Norms2).
filter_lb_constraints_1([norm(It_vars,Exp)|Norms],It_vars_keep,Norms_accum,Norms_out):-
	from_list_sl(It_vars,It_vars1),
	intersection_sl(It_vars1,It_vars_keep,It_vars2),
	length(It_vars1,N),
	(length(It_vars2,N)->
		filter_lb_constraints_1(Norms,It_vars_keep,[norm(It_vars2,Exp)|Norms_accum],Norms_out)  
	;
		filter_lb_constraints_1(Norms,It_vars_keep,Norms_accum,Norms_out)
	).
	
%! remove_zero_costs(+It_vars:list(var),+It_costs:list(cost_expression),+Norms:list(norm),-It_vars1:list(var),-It_costs1:list(cost_expression),-Norms1:list(norm)) is det
% remove the iteration variables whose loop cost is 0
% from the list of iteration variables and from the norms
remove_zero_costs(It_vars,It_costs,Norms,It_vars1,It_costs1,Norms1):-
	maplist(remove_zero_cost,It_vars,It_costs),
	exclude(is_zero,It_vars,It_vars1),
	exclude(is_zero,It_costs,It_costs1),
	filter_zeroes_in_norms(Norms,Norms1).

%! remove_zero_cost(-It_var:var,+It_cost:cost_expression) is det
% If It_cost is zero, assign It_var to zero
remove_zero_cost(0,Cost):-Cost==0,!.
remove_zero_cost(_,_).

%! filter_zeroes_in_norms(+Norms:list(norm),-Norms1:list(norm)) is det
% remove all the iteration variables that have been assigned to 0 from Norms
filter_zeroes_in_norms([],[]).
filter_zeroes_in_norms([norm(Its,Rf)|Norms],[norm(Its1,Rf)|Filtered_norms]):-
	exclude(is_zero,Its,Its1),
	Its1\=[],!,
	filter_zeroes_in_norms(Norms,Filtered_norms).
filter_zeroes_in_norms([_|Norms],Filtered_norms):-
	filter_zeroes_in_norms(Norms,Filtered_norms).

%! group_same_its_constraints(+Norms:list(norm),-Norms2:list(norm)) is det
% put all the norms that contain the same set of iteration variables together.
% For example, if we have norm([I1,I2],A) and norm([I1,I2],B), it generates norm([I1,I2],min([A,B]))
group_same_its_constraints(Norms,Cs,Max_min,Norms2):-
	maplist(zip_with_op(norm),Its_list,Exps,Norms),
	maplist(tuple,Its_list,Exps,Pair_list),
	from_pair_list_mm(Pair_list,Multimap),
	maplist(generate_1_norm(Cs,Max_min),Multimap,Norms2).

generate_1_norm(_,(Its,[Exp]),norm(Its,Exp)):-!.
generate_1_norm(Cs,max,(Its,Exps),norm(Its,Cost_simple)):-
	cexpr_simplify(min(Exps),Cs,Cost_simple).
generate_1_norm(Cs,min,(Its,Exps),norm(Its,Cost_simple)):-
	cexpr_simplify(max(Exps),Cs,Cost_simple).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! group_dependant_it_constrs(+Constrs:list(norm),+It_vars:list(var),-Grouped_It_vars:list(it_group)) is det
% group the iteration variables and the norms that depend on each other
% so they can be solved separately
% it_group:it_group(list(var),list(norm))
group_dependant_it_constrs(Constrs,It_vars,Grouped_It_vars):-
	maplist(create_initial_it_group,It_vars,It_groups_ini),
	from_list_sl(It_vars,It_vars_set),
	group_dependant_it_constrs_1(Constrs,It_vars_set,It_groups_ini,Grouped_It_vars).

create_initial_it_group(V,it_group([V],[])).

%! group_dependant_it_constrs_1(+Norms:list(norm),+It_set:list(var),+It_Grs_accum:list(it_group),-It_Grs_out:list(it_group)) is det
% for each norm, join the groups where its iteration variables appear and add the norm to the group
group_dependant_it_constrs_1([],_,It_Grs,It_Grs).
group_dependant_it_constrs_1([norm(Its,Rf)|Constrs],It_set,It_Grs_in,It_Grs):-
	from_list_sl(Its,I_set),
	intersection_sl(I_set,It_set,Inter_set),
	join_groups(It_Grs_in,Inter_set,[],it_group([],[]),[Joined_group|It_Grs_aux]),
	add_constr_to_group(norm(Its,Rf),Joined_group,Joined_group1),
	It_Grs_aux2=[Joined_group1|It_Grs_aux],
	group_dependant_it_constrs_1(Constrs,It_set,It_Grs_aux2,It_Grs).


%! join_groups(+It_groups:list(it_group),+Vars:list_set(var),+Grs_aux:list(it_group),+Group_accum:it_group,-Grs_out:list(it_group)) is det
% examine the elements of It_groups. If a group contains any of the variables in Vars,
% we join it with the Group_accum and will be part of a new group.
% Otherwise, we put it in Grs_aux with the other groups that are not joined but the vars Vars.
% In the end, we return the non joined groups plus the new accumulated group in Grs_out.
join_groups([],_,Grs_aux,it_group(Vars_group,Cs),[it_group(Vars_group,Cs)|Grs_aux]).

join_groups([it_group(V1,Cs1)|More],Vars,Grs_aux,Group_accum,Grs_out):-
	intersection_sl(V1,Vars,[]),!,
	join_groups(More,Vars,[it_group(V1,Cs1)|Grs_aux],Group_accum,Grs_out).
join_groups([it_group(V1,Cs1)|More],Vars,Grs_aux,Group_accum,Grs_out):-
	join_two_groups(it_group(V1,Cs1),Group_accum,Group_accum1),
	join_groups(More,Vars,Grs_aux,Group_accum1,Grs_out).

join_two_groups(it_group(V1,Cs1),it_group(V2,Cs2),it_group(V3,Cs3)):-
	union_sl(V1,V2,V3),
	union_sl(Cs1,Cs2,Cs3).

add_constr_to_group(C,it_group(V,Cs),it_group(V,Cs2)):-
	insert_sl(Cs,C,Cs2).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%! solve_constr_group(+It_vars:list(p(var,cost_expression)),+EntryVars:list(var),+It_group:it_group,-Cost:cost_expression) is det
% Solve an iteration group It_group that represent a subset of norms that depend
% on each other. We select a set of constraints according to heuristic criteria.
% Then we maximize each iteration variable and constraint one by one.
% The current criterion guarantees that this approach is safe.
solve_constr_group(It_pairs,EntryVars,max,it_group(Vars,Norms_all),Cost):-
	%FIXME when solve_precise we should check that the set of constraints generates
	% an acyclic dependency graph, otherwise the result could be unsound
	%(get_param(solve_precise,[N_extra])->
	%constraint_selection(it_group(Vars,Norms_all),N_extra,it_group(Vars,Norms))
	%;
	% this greedy constraint selection makes all the constraints independent from each other
	% this guarantees that the constraints can be maximized one by one
	aggresive_constraint_selection(it_group(Vars,Norms_all),it_group(Vars,Norms))
	%)
	,
	%get the costs that correspond to the iteration variables Vars
	include(has_iteration_variable(Vars),It_pairs,It_pairs1),
	from_list_sl(Norms,Maximized_norms_set),
	incremental_maximization(It_pairs1,EntryVars,Maximized_norms_set,Cost).
	

solve_constr_group(It_pairs,EntryVars,min,it_group(Vars,Norms_all),Cost):-
	aggresive_constraint_selection_min(it_group(Vars,Norms_all),it_group(Vars,Norms)),
	%get the costs that correspond to the iteration variables Vars
	include(has_iteration_variable(Vars),It_pairs,It_pairs1),
	from_list_sl(Norms,Maximized_norms_set),
	incremental_minimization(It_pairs1,EntryVars,Maximized_norms_set,Cost).


has_iteration_variable(Vars,p(It_var,_)):-
	contains_sl(Vars,It_var).

%! incremental_maximization(+It_pairs:p(var,cost_expression),EVars:list(var),Norms:list(norm),Cost:cost_expression) is det
% given a list of pairs of iteration variables and their cost It_pairs and a list of norms Norms
% find a cost expression that is a safe upper bound.
incremental_maximization([],_,_,0).

incremental_maximization(It_pairs,EVars,Norms,Cost):-
	findall((EVars,Cost1),
% for every iteration variable,
   		(select(p(It_var,It_cost),It_pairs,It_pairs_rem),
	
   		 findall((EVars,Cost_inter),
   		 (
   		   partition(contains_it_var(It_var),Norms,Norms_related,_Norms_rest),
       (Norms_related=[_|_]->
%   select a norm that cover It_var      
         member(norm(Its,Rf),Norms_related),
%       set the iteration variable to the expression of the norm Rf         
         It_var=Rf,
%       and the rest of the iteration variables of the constrain to 0         
         maplist(assign_zero_if_possible(Rf),Its),
% remove pairs whose iteration variable has taken the 0 value         
         exclude(zero_it_var,It_pairs_rem,Remaining_it_pairs),
% all the norms norm([Its,It_var],Exp) that contain It_var are transformed into norm([Its],Exp-Rf)
         maplist(transform_norms(Rf),Norms,Transformed_norms),
% exclude norms that are left empty        
         exclude(empty_norm,Transformed_norms,Remaining_norms),

         (Remaining_it_pairs=[]->
	      Cost_aux=0
          ;
          %recursive call
          incremental_maximization(Remaining_it_pairs,EVars,Remaining_norms,Cost_aux)
          ),
          % accumulate the cost
          % Cost_iter= Rf*It_cost+ Cost_aux
         cexpr_mul(nat(Rf),It_cost,Loop_CExpr),
         cexpr_add(Loop_CExpr,Cost_aux,Cost_inter)
       ;
       % the pair is not bounded by any constraint!
	     Cost_inter=inf
       )  
       ),Inter_costs),
   	   assign_right_vars(Inter_costs,EVars,Inter_costs2),
   	   % keep the minimum of considering different constraints
   	   cexpr_min(Inter_costs2,Cost1)
   	),Costs),
   	assign_right_vars(Costs,EVars,Costs2),
   	%keep the maximum of maximizing iteration variables in different order
   	cexpr_max(Costs2,Cost).
   	
      
%! transform_norms(+Rf_used:cost_expression,+Norm:norm,-Norm:norm) is det
% remove the iteration variables that have been set to 0
% and if the norm contains the iteration variable that has been assigned,
% change it to the other side of the inequality
transform_norms(Rf_used,norm(Its,Rf),norm(Its2,Rf1)):-
	from_list_sl(Its,Its_set),
	exclude(is_zero,Its_set,Its1),
	(contains_sl(Its1,Rf_used)->
	    difference_sl(Its1,[Rf_used],Its2),
	    Rf1=Rf+(-1*Rf_used)
	;
	 Rf1=Rf,
	 Its2=Its1
	).


assign_zero_if_possible(Rf,Var):-Rf==Var,!.
assign_zero_if_possible(_,0):-!.
assign_zero_if_possible(_).


contains_it_var(It_var,norm(Its,_)):-
	contains_sl(Its,It_var).
	
is_zero(Var):-
	Var==0.

zero_it_var(p(It_var,_)):-
	It_var==0.
	
empty_norm(norm([],_)).



incremental_minimization([],_,_,0).

incremental_minimization(It_pairs,EVars,Norms,Cost):-
	findall((EVars,Cost1),
% for every iteration variable,
   		(select(p(It_var,It_cost),It_pairs,It_pairs_rem),
	
   		 findall((EVars,Cost_inter),
   		 (
   		   partition(contains_it_var(It_var),Norms,Norms_related,_Norms_rest),
       (Norms_related=[_|_]->
%   select a norm that cover It_var      
         member(norm(Its,Rf),Norms_related),
%       set the iteration variable to the expression of the norm Rf         
         It_var=Rf,
%       and the rest of the iteration variables of the constrain to 0         
         maplist(assign_zero_if_possible(Rf),Its),
% remove pairs whose iteration variable has taken the 0 value         
         exclude(zero_it_var,It_pairs_rem,Remaining_it_pairs),
% all the norms norm([Its,It_var],Exp) that contain It_var are transformed into norm([Its],Exp-Rf)
         maplist(transform_norms(Rf),Norms,Transformed_norms),
% exclude norms that are left empty        
         exclude(empty_norm,Transformed_norms,Remaining_norms),

         (Remaining_it_pairs=[]->
	      Cost_aux=0
          ;
          %recursive call
          incremental_minimization(Remaining_it_pairs,EVars,Remaining_norms,Cost_aux)
          ),
          % accumulate the cost
          % Cost_iter= Rf*It_cost+ Cost_aux
         cexpr_mul(nat(Rf),It_cost,Loop_CExpr),
         cexpr_add(Loop_CExpr,Cost_aux,Cost_inter)
       ;
       % the pair is not bounded by any constraint!
	     Cost_inter=0
       )  
       ),Inter_costs),
   	   assign_right_vars(Inter_costs,EVars,Inter_costs2),
   	   % keep the minimum of considering different constraints
   	   cexpr_max(Inter_costs2,Cost1)
   	),Costs),
   	assign_right_vars(Costs,EVars,Costs2),
   	%keep the maximum of maximizing iteration variables in different order
   	cexpr_min(Costs2,Cost).






%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% select the norms
 
 % this method for  selecting norms allows better precission and is adjustable but an additional check is needed to
 % guarantee that the obtained set of constraints can be safely incrementally maximized
 /*  	
constraint_selection(it_group(Vars,Norms),N_extra,it_group(Vars,Taken_norms)):-
	order_norms_heuristically(Norms,Ordered_norms),
	length(Vars,NVars),
	take_norms_until_covered(Ordered_norms,NVars,N_extra,[],[],Taken_norms).
	
take_norms_until_covered([],_NVars,_,_Collected_vars,Selected_norms,Selected_norms).
take_norms_until_covered([norm(Vars,Exp)|More],NVars,N_extra,Collected_vars,Selected_norms,Selected_norms_out):-
	length(Collected_vars,N),
	union_sl(Vars,Collected_vars,Collected_vars1),
	length(Collected_vars1,N1),
	(N1 > N ->
	  (N1=NVars ->
	     take_n(More,N_extra,[norm(Vars,Exp)|Selected_norms],Selected_norms_out)

	     ;
	     take_norms_until_covered(More,NVars,N_extra,Collected_vars1,[norm(Vars,Exp)|Selected_norms],Selected_norms_out)
	  )
	  ;
	  (N_extra > 0->
	    N_extra2 is N_extra-1,
	    take_norms_until_covered(More,NVars,N_extra2,Collected_vars1,[norm(Vars,Exp)|Selected_norms],Selected_norms_out)
	  ;
	    take_norms_until_covered(More,NVars,N_extra,Collected_vars,Selected_norms,Selected_norms_out)
	  )
	  ).
take_n([],_,Selected_norms,Selected_norms).
take_n([Norm|More],N,Selected_norms,Selected_norms_out):-
	N > 0,!,
	N1 is N-1,
	take_n(More,N1,[Norm|Selected_norms],Selected_norms_out).
take_n(_,0,Selected_norms,Selected_norms).
*/		
aggresive_constraint_selection_min(it_group(Vars,Norms),it_group(Vars,Taken_norms)):-
	order_norms_heuristically_min(Norms,Ordered_norms),
	take_norms_agressive_min(Ordered_norms,Vars,Taken_norms).

%! take_norms_agressive(+Norms:list(norm),+Vs:list_set(var),-Norms1:list(norm)) is det
% collect norms until all the iteration variables are covered
% each time we take one, remove the covered iteration variables from the remaining norms (thus eliminating dependencies)
% and re-order the transformed norms
take_norms_agressive_min([],_NVars,[]).
take_norms_agressive_min([norm(Vars,Exp)|Norms],Rest_vars,[norm(Vars,Exp)| Taken_norms]):-
	difference_sl(Rest_vars,Vars,Rest_vars1),
	(Rest_vars1=[] ->
	       Taken_norms=[]
	;
	       exclude(norm_contains_it_vars(Vars),Norms,Norms1),
	       order_norms_heuristically_min(Norms1,Ordered_norms),
	       take_norms_agressive_min(Ordered_norms,Rest_vars1, Taken_norms)
	 ).	
norm_contains_it_vars(Its1,norm(Its,_)):-
	intersection_sl(Its1,Its,[_|_]).	 
	 
%! aggresive_constraint_selection(+It_group:it_group,-It_group2:it_group) is det	
% select a set of norms that will be taken into account and ignore the rest.
% the selection is done according to the following heuristics:
%  * asymptotic complexity of the expression in thenorm
%  * number of iteration variables
%  * number of variables in the expression
%
% The iteration variables that are already covered by a norm are deleted from the rest of the norm.
% That way, we get rid of all the dependencies (but we could lose precission).
aggresive_constraint_selection(it_group(Vars,Norms),it_group(Vars,Taken_norms)):-
	order_norms_heuristically(Norms,Ordered_norms),
	take_norms_agressive(Ordered_norms,Vars,Taken_norms).

%! take_norms_agressive(+Norms:list(norm),+Vs:list_set(var),-Norms1:list(norm)) is det
% collect norms until all the iteration variables are covered
% each time we take one, remove the covered iteration variables from the remaining norms (thus eliminating dependencies)
% and re-order the transformed norms
take_norms_agressive([],_NVars,[]).
take_norms_agressive([norm(Vars,Exp)|Norms],Rest_vars,[norm(Vars,Exp)| Taken_norms]):-
	difference_sl(Rest_vars,Vars,Rest_vars1),
	(Rest_vars1=[] ->
	       Taken_norms=[]
	;
	       keep_it_vars(Norms,Rest_vars1,Norms1),
	       order_norms_heuristically(Norms1,Ordered_norms),
	       take_norms_agressive(Ordered_norms,Rest_vars1, Taken_norms)
	 ).

%! keep_it_vars(+Norms:list(norm),+Vs:list_set(var),-Norms1:list(norm)) is det    
% keep only the iteration variables Vs in the Norms 
% if a norm becomes empty, ignore it
keep_it_vars([],_,[]).
keep_it_vars([norm(Vars,Exp)|Norms],Vs,Norms1):-
	intersection_sl(Vars,Vs,Vars1),
	(Vars1\=[]->
	   Norms1=[norm(Vars1,Exp)|Norms_aux]
	   ;
	   Norms1=Norms_aux
	 ),
	 keep_it_vars(Norms,Vs,Norms_aux).
	   

order_norms_heuristically(Norms,Ordered_norms):-
	sort_with(Norms,bigger_heuristic,Ordered_norms).

order_norms_heuristically_min(Norms,Ordered_norms):-
	sort_with(Norms,smaller_heuristic,Ordered_norms).
%! bigger_heuristic(+Norm1:norm,+Norm2:norm) is semidet
% define an heuristic criteron to sort norms according to:
%  *if both norms are numbers, the value of the numbers 
%  *asymptotic complexity of the expression in the norm
%  *number of iteration variables (here we want the maximum number of iteration variables to be smaller)
%  *number of variables in the expression
bigger_heuristic(norm(_Vars1,Expression1),norm(_Vars2,Expression2)):-
	number(Expression1),
	number(Expression2),
	Expression1 > Expression2,!.

bigger_heuristic(norm(_Vars1,Expression1),norm(_Vars2,Expression2)):-
	get_asymptotic_class(Expression1,Class1),
	get_asymptotic_class(Expression2,Class2),
	(Class1 > Class2),!.
	
bigger_heuristic(norm(Vars1,Expression1),norm(Vars2,Expression2)):-
	get_asymptotic_class(Expression1,Class1),
	get_asymptotic_class(Expression2,Class2),
	(Class1 == Class2),
	length(Vars1,N1),length(Vars2,N2),
	(N1 < N2),!.

bigger_heuristic(norm(Vars1,Expression1),norm(Vars2,Expression2)):-
	length(Vars1,N1),length(Vars2,N1),
	get_asymptotic_class(Expression1,Class1),
	get_asymptotic_class(Expression2,Class1),
	term_variables(Expression1,VarsExp1),length(VarsExp1,NVars1),
	term_variables(Expression2,VarsExp2),length(VarsExp2,NVars2),
	NVars1 < NVars2,!.
	

	
smaller_heuristic(norm(_Vars1,Expression1),norm(_Vars2,Expression2)):-
	number(Expression1),
	number(Expression2),
	Expression1 < Expression2,!.

smaller_heuristic(norm(_Vars1,Expression1),norm(_Vars2,Expression2)):-
	get_asymptotic_class(Expression1,Class1),
	get_asymptotic_class(Expression2,Class2),
	(Class1 < Class2),!.
	
smaller_heuristic(norm(Vars1,Expression1),norm(Vars2,Expression2)):-
	get_asymptotic_class(Expression1,Class1),
	get_asymptotic_class(Expression2,Class2),
	(Class1 == Class2),
	length(Vars1,N1),length(Vars2,N2),
	(N1 > N2),!.
	
	
	