/** <module> cost_structure_solver

 This module solves cost structures into cost expressions

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
    

This module uses the following auxiliary cost structures:

 * partial_strexp: partial(index,strexp) | strexp
   represents a cost but strexp can still contain variables that correspond to intermediate variables
   this correspondence is recorded in index
 * partial_bconstr: bound(op,partial_strexp,list(itvar))
   It is like a bconstr but contains a partial_strexp

*/

:- module(cost_structure_solver,[
		cstr_maxminimization/5
	]).

:- use_module('../IO/params',[get_param/2]).	

:- use_module('../utils/cost_structures',[
		max_min_ub_lb/2,
		cstr_empty/1,
		cstr_from_cexpr/2,	
		new_itvar/1,
		get_loop_itvar/2,
		fconstr_new/4,
		fconstr_new_inv/4,
		is_ub_bconstr/1,
		bconstr_get_bounded/2,
		bconstr_annotate_bounded/2,
		basic_cost_to_astrexp/4,
		cstr_remove_cycles/2,
		cstr_extend_variables_names/3,
		cstr_join/3,
		cstr_shorten_variables_names/3,
		cstr_simplify/5]).
:- use_module('../utils/structured_cost_expression',[
		partial_strexp_estimate_complexity/3,
		partial_strexp_complexity/2,
		strexp_to_cost_expression/2,
		strexp_get_multiplied_factors/3,
		get_all_pairs/3,
		strexp_simplify/2]).		
		
:- use_module('../utils/cofloco_utils',[sort_with/3,
		tuple/3,
		is_rational/1,
		assign_right_vars/3]).	


:- use_module(stdlib(linear_expression),[parse_le/2,write_le/2,negate_le/2,
    is_constant_le/1,
	integrate_le/3,
	write_le/2,
	elements_le/2,
	constant_le/2]).	

:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4,ut_sort/2,ut_var_member/2]).	
:- use_module(stdlib(multimap),[put_mm/4,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).
:- use_module(stdlib(fraction)).
:- use_module(stdlib(set_list),[difference_sl/3,contains_sl/2,from_list_sl/2,unions_sl/2,union_sl/3,insert_sl/3,intersection_sl/3]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).

			
cstr_maxminimization(Cost_long,Max_min,Head,Inv,Cost_final):-
	Head=..[_|Vars],
	max_min_ub_lb(Max_min,Op),
	cstr_shorten_variables_names(Cost_long,no_list,Cost_short),	
	cstr_simplify(Cost_short,Vars,Inv,Max_min,cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,BSummands,BConstant)),
	basic_cost_to_astrexp(BSummands,BConstant,Max_min,Exp_cost),
	%join all constraints
	ut_flat_list([Ub_fconstrs,Lb_fconstrs,Iconstrs],All_bconstrs),
	
	maplist(bconstr_annotate_bounded,All_bconstrs,All_bconstrs_annotated),
	%obtain the itvars that have to be assigned incrementally
	foldl(get_non_deterministic_vars,All_bconstrs_annotated,[],Non_det_vars),
	%solve all constraints with a single bounded itvar
	compress_constraints(All_bconstrs_annotated,Non_det_vars,Remaining_constrs,[],Map),
	astrexp_to_partial_strexp(Exp_cost,main,Op,Non_det_vars,Map,Solved_exp),
	% group itvars and constraints that depend on each other
	group_remaining_constrs(Remaining_constrs,Groups),
	% generate all possible maximizations or minimizations
	findall((Vars,Cost_closed),
		(
		incremental_maxminization(Groups,Solved_exp,Cost),
		remove_undefined_vars(Cost,Cost_closed)
		)
	,Costs_list),
	assign_right_vars(Costs_list,Vars,Costs_list_right),
	from_list_sl(Costs_list_right,Cost_set),!,
	%tranform into cost expressions
	%maplist(writeln,Cost_set),
	maplist(strexp_to_cost_expression,Cost_set,Cost_set_p),
	%maplist(writeln,Cost_set_p),
	%take the maximum or minimum of all the possibilities
	Cost_final=..[Max_min,Cost_set_p],!.

%this predicate should never fail
cstr_maxminimization(Cost_long,Max_min,_):-
	throw(maximization_failed(Cost_long,Max_min)).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_non_deterministic_vars(bound(_,_,[_Bounded]),Accum_set,Accum_set):-!.
get_non_deterministic_vars(bound(_,_,Bounded),Accum_set,Accum_set2):-
	union_sl(Bounded,Accum_set,Accum_set2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!compress_constraints(Bconstrs:list(bconstr),Non_det_vars:list_set(itvar),Remaining_constrs:list(partial_bconstr),Map_accum:list_map(itvar,(int,partial_strexp)),Map_out:list_map(itvar,(int,partial_strexp)))
% assign all the itvars that are bounded alone in the Bconstrs
% Remaining_constrs are the Bconstrs that bound multiple itvar, they contain partial_strexp which are strexp with some unknown variables
% the Max_out maps itvars to pairs (Estimated_complexity:int,Solved_exp:partial_strexp)
compress_constraints([],_,[],Map,Map).
compress_constraints([bound(Op,Exp,Bounded)|Bconstrs],Non_det_vars,Remaining_constrs,Map_accum,Map_out):-
	% transform a astrexp into a partial_strexp
	astrexp_to_partial_strexp(Exp,aux,Op,Non_det_vars,Map_accum,Partial_strexp),
	partial_strexp_estimate_complexity(Partial_strexp,Map_accum,Estimated_complexity),
	%check if the constraint is non-deterministic or not
	Bounded=[Bounded1|_],
	(contains_sl(Non_det_vars,Bounded1)->
		%if non-deterministic accumulate to solve later
		Remaining_constrs=[bound(Op,Partial_strexp,Bounded)|Remaining_constrs1],
		% store the estimated complexity of the bounded vars
		foldl(add_to_bound_map((Estimated_complexity,unknown)),Bounded,Map_accum,Map_accum2)
	;
		%update the map that stores the resulting expressions and their estimated complexity
	 	add_to_bound_map((Estimated_complexity,Partial_strexp),Bounded1,Map_accum,Map_accum2),
	 	Remaining_constrs=Remaining_constrs1
	),
	compress_constraints(Bconstrs,Non_det_vars,Remaining_constrs1,Map_accum2,Map_out).

%! astrexp_to_partial_strexp(+Exp:exp,+Main_flag:flag,+Op:flag,+Non_det_vars:list_set(itvar),+Map_itvars:list_map(itvar,(int,partial_strexp)),-Partial_strexp:partial_strexp)
% solve an expression Exp that can be a nlinexp or a astrexp into a partial_strexp
% using Map_itvars for the deterministic itvars and Non_det_vars to detect the non-deterministic ones
%
% Main_flag indicates if we are solving the main expression or an intermediate one
% the main expression can be between -inf and +inf while an intermediate expression is always non-negative
astrexp_to_partial_strexp(Exp,Main_flag,_Op,Non_det_vars,Map_accum,Partial_strexp):-
	% Exp is a astrexp
	% make a copy
	copy_term(Exp,exp(Index_pos,Index_neg,Pos,Neg)),
	% join the indexes
	append(Index_pos,Index_neg,Index_total),
	% split between solved itvars and non-deterministic itvars
	partition(index_in_set(Non_det_vars),Index_total,Index_non_det,Index_det),
	% substitute deterministic itvars by their partial expressions 
	%(the partial expressions might had their own indexes that we have to add)
	maplist(substitute_index_by(Map_accum),Index_det,Extra_index),!,
	ut_flat_list([Index_non_det,Extra_index],Index_flat),
	Neg=add(Summands_neg),
	Pos=add(Summands_pos),
	maplist(negate_summand,Summands_neg,Summands_negated),
	append(Summands_pos,Summands_negated,All_summands),

	(Main_flag=main->
		strexp_simplify(add(All_summands),Simple_exp)
	;
		strexp_simplify(nat(add(All_summands)),Simple_exp)
	),
	(Index_flat=[]->
		Partial_strexp=Simple_exp
	;
		Partial_strexp=partial(Index_flat,Simple_exp)
	).

%these are the cases where there is an unbounded element in the expression	
astrexp_to_partial_strexp(exp(_Index_pos,_Index_neg,_Pos,_Neg),_,ub,_Non_det_vars,_Map_accum,inf).
% only the main expression can be negative
astrexp_to_partial_strexp(exp(_Index_pos,_Index_neg,_Pos,_Neg),aux,lb,_Non_det_vars,_Map_accum,0).		
astrexp_to_partial_strexp(exp(_Index_pos,_Index_neg,_Pos,_Neg),main,lb,_Non_det_vars,_Map_accum,-inf).		

% the cases where we have a alinexp
% the main expression can never be a alinexp
astrexp_to_partial_strexp([]+C,aux,_Op,_,_Map_accum,C):-
	geq_fr(C,0),!.
astrexp_to_partial_strexp(Lin_exp,aux,_,_,_Map_accum,nat(Lin_exp_print)):-	
	write_le(Lin_exp,Lin_exp_print).

%! add_to_bound_map(Solved_exp:(int,partial_strexp),Itvar:itvar,Map:list_map(itvar,(int,partial_strexp)),Map2:list_map(itvar,(int,partial_strexp)))
% add the pair Solved_exp to the Map
% we only keep one solution for each itvar according to the estimated complexity
add_to_bound_map(Solved_exp,Itvar,Map,Map2):-
	lookup_lm(Map,Itvar,Expr),!,
	Itvar=..[Op|_],
	select_best_expr(Op,Expr,Solved_exp,New_exp),
	insert_lm(Map,Itvar,New_exp,Map2).
add_to_bound_map(Solved_exp,Itvar,Map,Map2):-
	insert_lm(Map,Itvar,Solved_exp,Map2).	

select_best_expr(ub,(C1,Exp1),(C2,Exp2),Selected):-
	(C1<C2->
		Selected=(C1,Exp1)
	;
		(C2<C1->	
			Selected=(C2,Exp2)
		;
			(Exp1=partial(_,_)->
				Selected=(C2,Exp2)
				
			;
				Selected=(C1,Exp1)
			)
		)
	).

select_best_expr(lb,(C1,Exp1),(C2,Exp2),Selected):-
	(C1<C2->
		Selected=(C2,Exp2)
	;
		(C2<C1->	
			Selected=(C1,Exp1)
		;
			(Exp1=partial(_,_)->
				Selected=(C2,Exp2)
				
			;
				Selected=(C1,Exp1)
			)
		)
	).	

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% create groups of variables that are defined together
group_remaining_constrs(Constrs,Groups):-
	split_remaining_constrs(Constrs,Grouped_constrs),
	exclude(=([]),Grouped_constrs,Grouped_constrs1),
	maplist(create_group,Grouped_constrs1,Groups).

split_remaining_constrs([],[]).
split_remaining_constrs(Remaining_constrs,Final_groups):-
		take_group(Remaining_constrs,[],Group,Rest),
		partition(is_ub_bconstr,Group,Ub_group,Lb_group),
		split_independent_vars(Ub_group,Ub_groups),
		reverse(Ub_groups,Ub_groups_rev),
		split_independent_vars(Lb_group,Lb_groups),
		reverse(Lb_groups,Lb_groups_rev),
		append(Ub_groups_rev,Lb_groups_rev,All_new_groups),
		append(All_new_groups,Groups,Final_groups),
		split_remaining_constrs(Rest,Groups).


split_independent_vars([],[]).
split_independent_vars([Bound|Bounds],[Group|Groups]):-
	Bound=bound(_,_,Bounded),
	from_list_sl(Bounded,Bounded_set),
	take_related(Bounds,[Bound],Bounded_set,Group,Rest),
	split_independent_vars(Rest,Groups).
	
take_related([],Accum,_,Accum,[]).
take_related(List,Accum,Vars_set,Group,Rest):-
	filter_related(List,Accum,Vars_set,Accum2,Vars_set2,Remaining),!,
	length(Vars_set,N),
	length(Vars_set2,N1),
	(N1>N->
	  take_related(Remaining,Accum2,Vars_set2,Group,Rest)
	 ;
	  Group=Accum2,
	  Rest=Remaining
	).
filter_related([],Accum,Vars_set,Accum,Vars_set,[]).
filter_related([Bound|Bounds],Accum,Vars_set,Group,Vars_set_out,Rest):-
	Bound=bound(_,_,Bounded),
	from_list_sl(Bounded,Bounded_set),
	intersection_sl(Bounded_set,Vars_set,[_|_]),!,
	union_sl(Bounded_set,Vars_set,Vars_set2),
	filter_related(Bounds,[Bound|Accum],Vars_set2,Group,Vars_set_out,Rest).
	
filter_related([Bound|Bounds],Accum,Vars_set,Group,Vars_set_out,[Bound|Rest]):-
	filter_related(Bounds,Accum,Vars_set,Group,Vars_set_out,Rest).

take_group([],_,[],[]).
take_group([bound(Op,partial(Index,Exp),Bounded)|Constrs],Vars,[bound(Op,partial(Index,Exp),Bounded)|Group],Rest):-
	maplist(index_not_in_set(Vars),Index),!,
	union_sl(Bounded,Vars,Vars1),
	take_group(Constrs,Vars1,Group,Rest).
	
take_group([bound(Op,partial(Index,Exp),Bounded)|Constrs],_Vars,[],[bound(Op,partial(Index,Exp),Bounded)|Constrs]):-!.

take_group([bound(Op,Not_partial,Bounded)|Constrs],Vars,[bound(Op,Not_partial,Bounded)|Group],Rest):-
	union_sl(Bounded,Vars,Vars1),
	take_group(Constrs,Vars1,Group,Rest).
		
create_group(Group,group(Op,Group,Bounded_vars)):-
	Group=[bound(Op,_,_)|_],
	maplist(bconstr_get_bounded,Group,Bounded_lists),
	unions_sl(Bounded_lists,Bounded_vars).	
	

	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% solve one group after another in a non-determinisitic manner		
incremental_maxminization([],Exp,Exp).
incremental_maxminization([Group|Rest],Semi_solved_exp,Exp):-
	Group=group(_,_,Vars),
	check_well_formedness_of_constraints(Rest,Semi_solved_exp,Vars,Multiplied_pairs),
	solve_group(Group,Multiplied_pairs,Map),
	maplist(evaluate_group(Map),Rest,Rest1),
	simplify_partial_exp(Semi_solved_exp,Map,Semi_solved_exp1),
	remove_unused_vars_backwards(Rest1,Semi_solved_exp1,_Used_vars,Rest2),
	incremental_maxminization(Rest2,Semi_solved_exp1,Exp).


remove_unused_vars_backwards([],partial(Vars,_Exp),Names_set,[]):-!,
	maplist(tuple,Names,_,Vars),
	from_list_sl(Names,Names_set).
remove_unused_vars_backwards([],_,[],[]).
	
remove_unused_vars_backwards([group(Op,Cons,Vars)|Rest],Main_exp,Vars_set2,Rest_out):-
	remove_unused_vars_backwards(Rest,Main_exp,Vars_set,Rest2),
	intersection_sl(Vars,Vars_set,Vars2),
	(Vars2=[]->
	   Vars_set2=Vars_set,
	   Rest_out=Rest2
	   ;
	   foldl(remove_unused_var_constr(Vars_set),Cons,[],Cons2),
	   foldl(accum_partial_vars,Cons2,Vars_set,Vars_set2),
	   Rest_out=[group(Op,Cons2,Vars)|Rest2]
	   ),!.

remove_unused_var_constr(Var_set,bound(ub,Exp,Bounded),Accum,Accum2):-
	intersection_sl(Var_set,Bounded,Bounded1),
	(Bounded1=[]->
	   Accum2=Accum
	   ;
	   Accum2=[bound(ub,Exp,Bounded1)|Accum]
	  ).
remove_unused_var_constr(Var_set,bound(lb,Exp,Bounded),Accum,Accum2):-
	intersection_sl(Var_set,Bounded,Bounded1),
	length(Bounded1,N1),
	length(Bounded,N),
	(N1< N ->
	   Accum2=Accum
	   ;
	   Accum2=[bound(ub,Exp,Bounded)|Accum]
	  ).	  

accum_partial_vars(bound(_,partial(Vars,_),_),Vars_set,Vars_set2):-!,	
	maplist(tuple,Names,_,Vars),
	from_list_sl(Names,Names_set),
	union_sl(Names_set,Vars_set,Vars_set2).
accum_partial_vars(_,Vars_set,Vars_set).

solve_group(group(ub,Cons,_),Multiplied_pairs,Map):-
	sort_with(Cons,better_ubs,Cons_sorted),
	simplify_group(Cons_sorted,[],Cons_sorted1),
	solve_group_1(Cons_sorted1,[],Multiplied_pairs,Map).
	
solve_group(group(lb,Cons,_),Multiplied_pairs,Map):-
	sort_with(Cons,better_lbs,Cons_sorted),
	simplify_group(Cons_sorted,[],Cons_sorted1),
	solve_group_1(Cons_sorted1,[],Multiplied_pairs,Map).

%we select constraints with a greedy strategy based on the complexity and number of bounded variables

better_ubs(bound(ub,Exp,_Bounded),bound(ub,Exp2,_Bounded2)):-
	partial_strexp_complexity(Exp,C1),
	partial_strexp_complexity(Exp2,C2),
	C1>C2,!.
	
better_ubs(bound(ub,Exp,Bounded),bound(ub,Exp2,Bounded2)):-
	partial_strexp_complexity(Exp,C1),
	partial_strexp_complexity(Exp2,C2),
	C1=C2,
	length(Bounded,N),length(Bounded2,N2),N<N2.

	
better_lbs(bound(lb,Exp,_Bounded),bound(lb,Exp2,_Bounded2)):-
	partial_strexp_complexity(Exp,C1),
	partial_strexp_complexity(Exp2,C2),
	C1<C2,!.
	
better_lbs(bound(lb,Exp,Bounded),bound(lb,Exp2,Bounded2)):-
	partial_strexp_complexity(Exp,C1),
	partial_strexp_complexity(Exp2,C2),
	C1=C2,
	length(Bounded,N),length(Bounded2,N2),N>N2.	
	
	
simplify_group([],_,[]):-!.
simplify_group([bound(ub,_Exp,Bounded)|Cons],Vars,Cons1):-
	difference_sl(Bounded,Vars,[]),!,
	simplify_group(Cons,Vars,Cons1).
simplify_group([bound(ub,Exp,Bounded)|Cons],Vars,[bound(ub,Exp,Bounded1)|Cons1]):-
	difference_sl(Bounded,Vars,Bounded1),!,
	union_sl(Bounded1,Vars,Vars1),
	simplify_group(Cons,Vars1,Cons1).
simplify_group([bound(lb,Exp,Bounded)|Cons],Vars,[bound(lb,Exp,Bounded)|Cons1]):-
	intersection_sl(Bounded,Vars,[]),!,
	union_sl(Bounded,Vars,Vars1),
	simplify_group(Cons,Vars1,Cons1).
simplify_group([bound(lb,_Exp,_Bounded)|Cons],Vars,Cons1):-
	simplify_group(Cons,Vars,Cons1).			

solve_group_1([],Map,_Multiplied_pairs,Map).
solve_group_1([bound(_Op,add([]),Bounded)|Cons],Map_accum,Multiplied_pairs,Map):-!,
	foldl(insert_zero_value,Bounded,Map_accum,Map_accum2),
	solve_group_1(Cons,Map_accum2,Multiplied_pairs,Map).
	
solve_group_1([bound(_Op,nat(Add),Bounded)|Cons],Map_accum,Multiplied_pairs,Map):-
    nonvar(Add),Add==add([]),!,
	foldl(insert_zero_value,Bounded,Map_accum,Map_accum2),
	solve_group_1(Cons,Map_accum2,Multiplied_pairs,Map).
	
solve_group_1([bound(_Op,nat(Add),Bounded)|Cons],Map_accum,Multiplied_pairs,Map):-
	nonvar(Add),Add==add([mult([add([])])]),!,
	foldl(insert_zero_value,Bounded,Map_accum,Map_accum2),
	solve_group_1(Cons,Map_accum2,Multiplied_pairs,Map).
		
solve_group_1([bound(_Op,Add,Bounded)|Cons],Map_accum,Multiplied_pairs,Map):-
	Add==nat(add([mult([nat(add([mult([add([])])]))])])),!,
	foldl(insert_zero_value,Bounded,Map_accum,Map_accum2),
	solve_group_1(Cons,Map_accum2,Multiplied_pairs,Map).	

%If we are want speed over precision we solve constraints:
%it1+it2+...+itn\leq exp
% by assigning it1=exp, it2=exp...itn=exp
solve_group_1([bound(ub,Exp,Bounded)|Cons],Map_accum,Multiplied_pairs,Map):-
    get_param(solve_fast,[]),!,
	foldl(insert_value(Exp),Bounded,Map_accum,Map_accum2),
	solve_group_1(Cons,Map_accum2,Multiplied_pairs,Map).

%otherwise
solve_group_1([bound(ub,Exp,Bounded)|Cons],Map_accum,Multiplied_pairs,Map):-
	join_dependent_bounded(Bounded,Multiplied_pairs,Bounded_joined),
	select(Selected,Bounded_joined,Bounded1),
	foldl(insert_value(Exp),Selected,Map_accum,Map_accum1),
	ut_flat_list(Bounded1,Bounded1_flat),
	foldl(insert_zero_value,Bounded1_flat,Map_accum1,Map_accum2),
	solve_group_1(Cons,Map_accum2,Multiplied_pairs,Map).

%if there are dependent constraints and it's a lower bound constraint all goes to 0
solve_group_1([bound(lb,_Exp,Bounded)|Cons],Map_accum,Multiplied_pairs,Map):-
	Multiplied_pairs=[_|_],!,
	foldl(insert_zero_value,Bounded,Map_accum,Map_accum2),
	solve_group_1(Cons,Map_accum2,Multiplied_pairs,Map).

%if we are computing lower bound and there are no dependent pairs we try with each variable	
solve_group_1([bound(lb,Exp,Bounded)|Cons],Map_accum,[],Map):-
	select(Selected,Bounded,Bounded1),
	insert_lm(Map_accum,Selected,Exp,Map_accum1),
	foldl(insert_zero_value,Bounded1,Map_accum1,Map_accum2),
	solve_group_1(Cons,Map_accum2,[],Map).	

join_dependent_bounded(Bounded,Pairs,Bounded_joined):-
	maplist(put_in_list,Bounded,Bounded_list),
	foldl(join_dependent,Pairs,Bounded_list,Bounded_joined).

join_dependent((X,Y),Bounded_lists,Bounded_lists_joined):-
	get_set_with(Bounded_lists,X,X_set,Bounded_lists1),
	(contains_sl(X_set,Y)-> 
		Bounded_lists_joined=[X_set|Bounded_lists1]
		;
		get_set_with(Bounded_lists1,Y,Y_set,Bounded_lists2),
		union_sl(X_set,Y_set,XY_set),
		Bounded_lists_joined=[XY_set|Bounded_lists2]
	).

get_set_with([Set|Sets],Elem,Set,Sets):-
	contains_sl(Set,Elem),!.
get_set_with([Set|Sets_rest],Elem,Set_elem,[Set|Sets]):-
	get_set_with(Sets_rest,Elem,Set_elem,Sets).
	
put_in_list(X,[X]).
insert_value(Val,Var,Map,Map1):-
	insert_lm(Map,Var,Val,Map1).
insert_zero_value(Var,Map,Map1):-
	insert_lm(Map,Var,0,Map1).
insert_one_value(Var,Map,Map1):-
	insert_lm(Map,Var,1,Map1).	
% given the new values assigned to the variables of the group, we substitute in the rest of the constraints and simplify

evaluate_group(Map,group(Op,Constrs,Vars),group(Op,Constrs1,Vars)):-
	maplist(evaluate_constr(Map),Constrs,Constrs1).
	
evaluate_constr(Map,bound(Op,Exp,Bounded),bound(Op,Exp1,Bounded)):-
	simplify_partial_exp(Exp,Map,Exp1).
	

simplify_partial_exp(partial(Index,Exp),Map,Solved_exp):-!,
	maplist(substitute_index_by_optional(Map),Index,Extra_index),
	ut_flat_list(Extra_index,Index_flat),
	strexp_simplify(Exp,Simple_exp),
	term_variables(Simple_exp,Unknowns),
	from_list_sl(Unknowns,Unknowns_set),
	include(index_var_in_set(Unknowns_set),Index_flat,Index_final),
	(Index_final=[]->
		Solved_exp=Simple_exp
	;
		Solved_exp=partial(Index_final,Simple_exp)
	).	
	
simplify_partial_exp(Exp,_Map,Exp).

remove_undefined_vars(partial(Index,Exp),Exp):-!,
	maplist(substitute_index_by_default,Index).
remove_undefined_vars(Exp,Exp).







%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% accesing and updating different maps

substitute_index_by_default((lb(_),0)).
substitute_index_by_default((ub(_),inf)).

substitute_index_by_optional(Map_accum,(Name,Var),[]):-
		lookup_lm(Map_accum,Name,Var),!.
substitute_index_by_optional(_Map_accum,(Name,Var),[(Name,Var)]).

substitute_index_by(Map_accum,(Name,Var1),Index1):-
		lookup_lm(Map_accum,Name,(_,Exp)),!,
		(Exp=partial(Index,Var)->	
			Index1=Index,
			Var1=Var
			;
			Var1=Exp,
			Index1=[]
		).
		
substitute_index_by(_Map_accum,(lb(_Name),add([])),[]).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% make sure the constraints that we have admit greedy maximization strategy
% this is true if there are no products of two variables that are bounded by the same constraint group

check_well_formedness_of_constraints(Rest,Semi_solved_exp,Vars,Multiplied_pairs):-
	maplist(get_constraints_from_group,Rest,Cons_list),
	ut_flat_list(Cons_list,All_cons_rest),	
	(get_multiplied_vars(All_cons_rest,Semi_solved_exp,Vars,[],[],Multiplied_pairs)->
	 true
	;
	throw(implementation_error(predicate_failed(get_multiplied_vars(All_cons_rest,Semi_solved_exp,Vars))))
	).

get_constraints_from_group(group(_,Cons,_),Cons).

get_multiplied_vars([],Exp,Important_vars,Pairs_accum,Dep_map,Final_pairs):-
	get_exp_multiplied_vars(Exp,Important_vars,Var_pairs),
	foldl(accumulate_pairs_of_original_vars(Dep_map),Var_pairs,Pairs_accum,Final_pairs).
	
get_multiplied_vars([bound(_,Exp,Bounded)|Constrs],Exp_final,Important_vars,Pairs_accum,Dep_map,Final_pairs):-
	get_exp_multiplied_vars(Exp,Important_vars,Var_pairs),!,
	foldl(accumulate_pairs_of_original_vars(Dep_map),Var_pairs,Pairs_accum,Pairs_accum1),
	update_dependency_map(Exp,Bounded,Important_vars,Dep_map,Important_vars1,Dep_map1),
	get_multiplied_vars(Constrs,Exp_final,Important_vars1,Pairs_accum1,Dep_map1,Final_pairs).
	
accumulate_pairs_of_original_vars(Dep_map,(X,Y),Pairs_accum,Final_pairs):-
	(lookup_lm(Dep_map,X,ListX)->true;ListX=[X]),
	(lookup_lm(Dep_map,Y,ListY)->true ;ListY=[Y]),
	get_all_pairs([ListX,ListY],Pairs_accum,Final_pairs).
	

update_dependency_map(partial(Index,_),Bounded,Important_vars,Dep_map,Important_vars1,Dep_map1):-
	include(index_in_set(Important_vars),Index,Index_selected),
	Index_selected\=[],!,
	maplist(tuple,Names,_,Index_selected),
	from_list_sl(Names,Names_set),
	union_sl(Bounded,Important_vars,Important_vars1),
	foldl(update_multimap(Names_set),Bounded,Dep_map,Dep_map1).
update_dependency_map(_,_,Important_vars,Dep_map,Important_vars,Dep_map).

update_multimap(Set,Key,Map,Map1):-
	lookup_lm(Map,Key,Set1),!,
	union_sl(Set1,Set,Set2),
	insert_lm(Map,Key,Set2,Map1).
update_multimap(Set,Key,Map,Map1):-
	insert_lm(Map,Key,Set,Map1).

get_exp_multiplied_vars(partial(Index,Exp),Important_vars,Name_pairs):-!,
	include(index_in_set(Important_vars),Index,Index_selected),
	maplist(tuple,_,Vars,Index_selected),
	from_list_sl(Vars,Vars_set),
	strexp_get_multiplied_factors(Exp,Vars_set,Var_pairs),
	copy_term((Index_selected,Var_pairs),(Index2,Name_pairs)),
	maplist(unify_pair,Index2).
get_exp_multiplied_vars(_,_,[]).


	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
index_in_set(Set,(Elem,_)):-
	contains_sl(Set,Elem).
index_not_in_set(Set,(Elem,_)):-
	\+contains_sl(Set,Elem).	
	
index_var_in_set(Set,(_Name,Var)):-
	contains_sl(Set,Var),!.	
	
unify_pair((X,X)).


negate_summand(mult(Factors),mult([-1|Factors])).