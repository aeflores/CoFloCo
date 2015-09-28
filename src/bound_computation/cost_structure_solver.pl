:- module(cost_structure_solver,[
		cstr_maxminimization/3
	]).

:- use_module('../utils/cost_structures',[
		cstr_empty/1,
		cstr_extract_top_maxs/3,
		cstr_extract_top_mins/3,
		cstr_from_cexpr/2,	
		cstr_name_aux_var/1,
		cstr_get_it_name/2,
		cstr_generate_top_exp/4,
		cstr_generate_top_exp_inv/4,
		cstr_get_cexpr_from_normalform/2,
		cstr_get_cexpr_from_normalform_ground/2,
		cstr_remove_cycles/2,
		cstr_extend_variables_names/3,
		cstr_propagate_summatory/4,
		cstr_join/3,
		cstr_get_lin_exp_from_tops/3,
		cstr_join_equal_top_expressions/2,
		cstr_remove_useless_constrs_max_min/3,
		cstr_shorten_variables_names/3]).
:- use_module('../utils/structured_cost_expression',[
		partial_str_cost_exp_estimate_complexity/3,
		partial_str_cost_exp_complexity/2,
		str_cost_exp_complexity/2,
		str_cost_exp_2_cost_expression/2,
		str_cost_exp_get_multiplied_factors/3,
		str_cost_exp_simplify/2]).		
		
:- use_module('../utils/cofloco_utils',[sort_with/3,
		tuple/3,
		is_rational/1,
		assign_right_vars/3]).	


:- use_module(stdlib(linear_expression),[parse_le/2,write_le/2,negate_le/2]).	
:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4,ut_sort/2,ut_var_member/2]).	
:- use_module(stdlib(multimap),[put_mm/4,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).
:- use_module(stdlib(fraction)).
:- use_module(stdlib(set_list),[difference_sl/3,contains_sl/2,from_list_sl/2,unions_sl/2,union_sl/3,insert_sl/3,intersection_sl/3]).
		
	
cstr_maxminimization(Cost_long,Max_min,Cost_final):-
	cstr_shorten_variables_names(Cost_long,no_list,Cost_short),	
	cstr_remove_useless_constrs_max_min(Cost_short,Max_min,cost(Ub_tops,Lb_tops,Aux_exps,Bases,Base)),
	generate_constraint_with_base(Bases,Base,Max_min,bound(Op,Exp_cost,_)),
	term_variables((Ub_tops,Lb_tops),Entry_vars),
	ut_flat_list([Ub_tops,Lb_tops,Aux_exps],All_constrs),
	maplist(annotate_bounded,All_constrs,All_constrs_annotated),
	get_non_deterministic_vars(All_constrs_annotated,[],Non_det_vars),
	compress_constraints(All_constrs_annotated,Non_det_vars,[],Remaining_constrs,[],Map),
	%maplist(writeln,Map),
	solve_expression(Exp_cost,Op,Non_det_vars,Map,Solved_exp),
	group_remaining_constrs(Remaining_constrs,Groups),
	findall((Entry_vars,Cost_closed),
	(
	incremental_maxminization(Groups,Solved_exp,Cost),
	remove_undefined_vars(Cost,Cost_closed))
	,Costs_list),
	assign_right_vars(Costs_list,Entry_vars,Costs_list_right),
	from_list_sl(Costs_list_right,Cost_set),!,
	%maplist(writeln,Cost_set),
	maplist(str_cost_exp_2_cost_expression,Cost_set,Cost_set_p),
	%maplist(writeln,Cost_set_p),
	Cost_final=..[Max_min,Cost_set_p],!.

%this predicate should never fail
cstr_maxminimization(Cost_long,Max_min,_):-
	throw(maximization_failed(Cost_long,Max_min)).	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% create groups of variables that are defined together
group_remaining_constrs(Constrs,Groups):-
	split_remaining_constrs(Constrs,Grouped_constrs),
	exclude(=([]),Grouped_constrs,Grouped_constrs1),
	maplist(create_group,Grouped_constrs1,Groups).

split_remaining_constrs([],[]).
split_remaining_constrs(Remaining_constrs,[Ub_group,Lb_group|Groups]):-
		take_group(Remaining_constrs,[],Group,Rest),
		partition(is_ub_bound,Group,Ub_group,Lb_group),
		split_remaining_constrs(Rest,Groups).
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
	maplist(get_constr_bounded,Group,Bounded_lists),
	unions_sl(Bounded_lists,Bounded_vars).	
	
annotate_bounded(bound(Op,exp(Pos_index,Neg_index,Pos,Neg),Bounded),bound(Op,exp(Pos_index1,Neg_index1,Pos,Neg),Bounded_set)):-!,
	opposite_operator(Op,Op_neg),
	maplist(annotate_bounded_vars(Op),Bounded,Bounded1),
	from_list_sl(Bounded1,Bounded_set),
	maplist(annotate_bounded_pair(Op),Pos_index,Pos_index1),
	maplist(annotate_bounded_pair(Op_neg),Neg_index,Neg_index1).
annotate_bounded(bound(Op,Top,Bounded),bound(Op,Top,Bounded_set)):-
	maplist(annotate_bounded_vars(Op),Bounded,Bounded1),
	from_list_sl(Bounded1,Bounded_set).

annotate_bounded_vars(Op,Var,Var1):-
	Var1=..[Op,Var].
annotate_bounded_pair(Op,(Name,Var),(Name1,Var)):-
	Name1=..[Op,Name].	
	
remove_undefined_vars(partial(Index,Exp),Exp):-!,
	maplist(substitute_index_by_default,Index).
remove_undefined_vars(Exp,Exp).
		

	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% solve one group after another in a non-determinisitic manner		
incremental_maxminization([],Exp,Exp).
incremental_maxminization([Group|Rest],Semi_solved_exp,Exp):-
	Group=group(_,_,Vars),
	check_well_formedness_of_constraints(Rest,Semi_solved_exp,Vars),
	solve_group(Group,Map),
	maplist(evaluate_group(Map),Rest,Rest1),
	simplify_partial_exp(Semi_solved_exp,Map,Semi_solved_exp1),
	incremental_maxminization(Rest1,Semi_solved_exp1,Exp).


solve_group(group(ub,Cons,_),Map):-
	sort_with(Cons,better_ubs,Cons_sorted),
	simplify_group(Cons_sorted,[],Cons_sorted1),
	solve_group_1(Cons_sorted1,[],Map).
	
solve_group(group(lb,Cons,_),Map):-
	sort_with(Cons,better_lbs,Cons_sorted),
	simplify_group(Cons_sorted,[],Cons_sorted1),
	solve_group_1(Cons_sorted1,[],Map).

%we select constraints with a greedy strategy based on the complexity and number of bounded variables

better_ubs(bound(ub,Exp,_Bounded),bound(ub,Exp2,_Bounded2)):-
	partial_str_cost_exp_complexity(Exp,C1),
	partial_str_cost_exp_complexity(Exp2,C2),
	C1>C2,!.
	
better_ubs(bound(ub,Exp,Bounded),bound(ub,Exp2,Bounded2)):-
	partial_str_cost_exp_complexity(Exp,C1),
	partial_str_cost_exp_complexity(Exp2,C2),
	C1=C2,
	length(Bounded,N),length(Bounded2,N2),N<N2.

	
better_lbs(bound(lb,Exp,_Bounded),bound(lb,Exp2,_Bounded2)):-
	partial_str_cost_exp_complexity(Exp,C1),
	partial_str_cost_exp_complexity(Exp2,C2),
	C1<C2,!.
	
better_lbs(bound(lb,Exp,Bounded),bound(lb,Exp2,Bounded2)):-
	partial_str_cost_exp_complexity(Exp,C1),
	partial_str_cost_exp_complexity(Exp2,C2),
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

solve_group_1([],Map,Map).
solve_group_1([bound(_Op,add([]),Bounded)|Cons],Map_accum,Map):-!,
	foldl(insert_zero_value,Bounded,Map_accum,Map_accum2),
	solve_group_1(Cons,Map_accum2,Map).

solve_group_1([bound(_Op,Exp,Bounded)|Cons],Map_accum,Map):-
	select(Selected,Bounded,Bounded1),
	insert_lm(Map_accum,Selected,Exp,Map_accum1),
	foldl(insert_zero_value,Bounded1,Map_accum1,Map_accum2),
	solve_group_1(Cons,Map_accum2,Map).

insert_zero_value(Var,Map,Map1):-
	insert_lm(Map,Var,0,Map1).
	
% given the new values assigned to the variables of the group, we substitute in the rest of the constraints and simplify

evaluate_group(Map,group(Op,Constrs,Vars),group(Op,Constrs1,Vars)):-
	maplist(evaluate_constr(Map),Constrs,Constrs1).
	
evaluate_constr(Map,bound(Op,Exp,Bounded),bound(Op,Exp1,Bounded)):-
	simplify_partial_exp(Exp,Map,Exp1).
	

simplify_partial_exp(partial(Index,Exp),Map,Solved_exp):-!,
	maplist(substitute_index_by_optional(Map),Index,Extra_index),
	ut_flat_list(Extra_index,Index_flat),
	str_cost_exp_simplify(Exp,Simple_exp),
	(Index_flat=[]->
		Solved_exp=Simple_exp
	;
		Solved_exp=partial(Index_flat,Simple_exp)
	).	
simplify_partial_exp(Exp,_Map,Exp).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%generate the main constraint from the basic costs

generate_constraint_with_base(Bases,Base,Max_min,Final_constraint):-
	get_constr_op(Max_min,Op),
	opposite_operator(Op,Op_neg),
	cstr_name_aux_var(Bound_var),
	generate_summands_from_bases(Bases,Index_pos,Index_neg,Summands_pos,Summands_neg),
	maplist(annotate_bounded_pair(Op),Index_pos,Index_pos1),
	maplist(annotate_bounded_pair(Op_neg),Index_neg,Index_neg1),
	(geq_fr(Base,0)->
		Exp=exp(Index_pos1,Index_neg1,add([mult([Base])|Summands_pos]),add(Summands_neg))
	;
		negate_fr(Base,Base_neg),
		Exp=exp(Index_pos1,Index_neg1,add(Summands_pos),add([mult([Base_neg])|Summands_neg]))
	),
	Final_constraint=bound(Op,Exp,[Bound_var]).
	
	
generate_summands_from_bases([],[],[],[],[]).
generate_summands_from_bases([(Name,1)|Bases],[(Name,Var)|Index_pos],Index_neg,[mult([Var])|Summands_pos],Summands_neg):-!,
	generate_summands_from_bases(Bases,Index_pos,Index_neg,Summands_pos,Summands_neg).
	
generate_summands_from_bases([(Name,Coeff)|Bases],[(Name,Var)|Index_pos],Index_neg,[mult([Var,Coeff])|Summands_pos],Summands_neg):-
	geq_fr(Coeff,0),!,
	generate_summands_from_bases(Bases,Index_pos,Index_neg,Summands_pos,Summands_neg).
generate_summands_from_bases([(Name,Coeff)|Bases],Index_pos,[(Name,Var)|Index_neg],Summands_pos,[mult([Var,Coeff_neg])|Summands_neg]):-
	negate_fr(Coeff,Coeff_neg),
	generate_summands_from_bases(Bases,Index_pos,Index_neg,Summands_pos,Summands_neg).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_non_deterministic_vars([],Accum_set,Accum_set).
get_non_deterministic_vars([bound(_,_,[_Bounded])|Constrs],Accum_set,Non_det_vars):-!,
	get_non_deterministic_vars(Constrs,Accum_set,Non_det_vars).
get_non_deterministic_vars([bound(_,_,Bounded)|Constrs],Accum_set,Non_det_vars):-
	union_sl(Bounded,Accum_set,Accum_set2),
	get_non_deterministic_vars(Constrs,Accum_set2,Non_det_vars).	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%get rid of all the single variable constraints and substitute the rest and the main expression for their corresponding partially solved expressions

compress_constraints([],_,_,[],Map,Map).
compress_constraints([bound(Op,Exp,Bounded)|Constrs],Non_det_vars,Estimated_complexity_map,Remaining_constrs,Map_accum,Map_out):-
	solve_expression(Exp,Op,Non_det_vars,Map_accum,Solved_exp),
	partial_str_cost_exp_estimate_complexity(Solved_exp,Estimated_complexity_map,Estimated_complexity),
	Bounded=[Bounded1|_],
	(contains_sl(Non_det_vars,Bounded1)->
		Remaining_constrs=[bound(Op,Solved_exp,Bounded)|Remaining_constrs1],
		foldl(add_estimated_complexity(Estimated_complexity),Bounded,Estimated_complexity_map,Estimated_complexity_map1),
		Map_accum2=Map_accum
	;
	 	add_to_bound_map(Map_accum,Bounded1,(Estimated_complexity,Solved_exp),Map_accum2),
	 	Estimated_complexity_map1=Estimated_complexity_map,
	 	Remaining_constrs=Remaining_constrs1
	),
	compress_constraints(Constrs,Non_det_vars,Estimated_complexity_map1,Remaining_constrs1,Map_accum2,Map_out).

	
solve_expression(Exp,_Op,Non_det_vars,Map_accum,Solved_exp):-
	copy_term(Exp,exp(Index_pos,Index_neg,Pos,Neg)),
	append(Index_pos,Index_neg,Index_total),
	partition(index_in_set(Non_det_vars),Index_total,Index_non_det,Index_det),
	maplist(substitute_index_by(Map_accum),Index_det,Extra_index),!,
	ut_flat_list([Index_non_det,Extra_index],Index_flat),
	Neg=add(Summands_neg),
	Pos=add(Summands_pos),
	maplist(negate_summand,Summands_neg,Summands_negated),
	append(Summands_pos,Summands_negated,All_summands),
	str_cost_exp_simplify(nat(add(All_summands)),Simple_exp),
	(Index_flat=[]->
		Solved_exp=Simple_exp
	;
		Solved_exp=partial(Index_flat,Simple_exp)
	).
	
solve_expression(exp(_Index_pos,_Index_neg,_Pos,_Neg),ub,_Non_det_vars,_Map_accum,inf).
solve_expression(exp(_Index_pos,_Index_neg,_Pos,_Neg),lb,_Non_det_vars,_Map_accum,0).		

solve_expression([]+C,_Op,_,_Map_accum,C):-
	geq_fr(C,0),!.
solve_expression(Lin_exp,_Op,_,_Map_accum,nat(Lin_exp_print)):-	
	write_le(Lin_exp,Lin_exp_print).
	

add_to_bound_map(Map,Bounded,Solved_exp,Map2):-
	lookup_lm(Map,Bounded,Expr),!,
	Bounded=..[Op|_],
	select_best_expr(Op,Expr,Solved_exp,New_exp),
	insert_lm(Map,Bounded,New_exp,Map2).
add_to_bound_map(Map,Bounded,Solved_exp,Map2):-
	insert_lm(Map,Bounded,Solved_exp,Map2).	

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

	
	
add_estimated_complexity(Complexity,Bounded_name,Map,Map1):-
	lookup_lm(Map,Bounded_name,Complexity_old),!,
	(Bounded_name=ub(_)->
	New_complx is min(Complexity,Complexity_old)
	;
	New_complx is max(Complexity,Complexity_old)
	),
	insert_lm(Map,Bounded_name,New_complx,Map1).
add_estimated_complexity(Complexity,Bounded_name,Map,Map1):-
	insert_lm(Map,Bounded_name,Complexity,Map1).	



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% make sure the constraints that we have admit greedy maximization strategy
% this is true if there are no products of two variables that are bounded by the same constraint group

check_well_formedness_of_constraints(Rest,Semi_solved_exp,Vars):-
	maplist(get_constraints_from_group,Rest,Cons_list),
	ut_flat_list(Cons_list,All_cons_rest),	
	(get_multiplied_vars(All_cons_rest,Semi_solved_exp,Vars,[],[],Multiplied_pairs)->
	(Multiplied_pairs\=[]->throw(bad_behaving_constraints);true)
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
	str_cost_exp_get_multiplied_factors(Exp,Vars_set,Var_pairs),
	copy_term((Index_selected,Var_pairs),(Index2,Name_pairs)),
	maplist(unify_pair,Index2).
get_exp_multiplied_vars(_,_,[]).


	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
index_in_set(Set,(Elem,_)):-
	contains_sl(Set,Elem).
index_not_in_set(Set,(Elem,_)):-
	\+contains_sl(Set,Elem).	
	
unify_pair((X,X)).

get_constr_op(max,ub).
get_constr_op(min,lb).
	
opposite_operator(ub,lb).
opposite_operator(lb,ub).

is_ub_bound(bound(ub,_,_)).		
	
get_constr_bounded(bound(_,_,Bounded),Bounded).
	
	
negate_summand(mult(Factors),mult([-1|Factors])).