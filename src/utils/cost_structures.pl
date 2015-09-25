/** <module> cost_structures

 This module implements the predicates that deal with
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
		cstr_empty/1,
		cstr_extract_top_maxs/3,
		cstr_extract_top_mins/3,
		cstr_from_cexpr/2,
		cstr_maxminimization/3,
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
		cstr_shorten_variables_names/3]).
:- use_module(cofloco_utils,[sort_with/3,write_sum/2,write_product/2,tuple/3,assign_right_vars/3]).	
:- use_module(cost_expressions,[cexpr_simplify/3,is_linear_exp/1]).	

:- use_module(stdlib(linear_expression),[parse_le/2,write_le/2,negate_le/2]).	
:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4,ut_sort/2,ut_var_member/2]).	
:- use_module(stdlib(multimap),[put_mm/4,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).
:- use_module(stdlib(fraction)).
:- use_module(stdlib(set_list),[difference_sl/3,contains_sl/2,from_list_sl/2,unions_sl/2,union_sl/3,insert_sl/3,intersection_sl/3]).

:-dynamic short_db/3.


cstr_extract_top_maxs(cost(Top_exps,Top_exps_min,Aux,Elems,Base),cost([],Top_exps_min,Aux,Elems,Base),Top_exps).
cstr_extract_top_mins(cost(Top_exps,Top_exps_min,Aux,Elems,Base),cost(Top_exps,[],Aux,Elems,Base),Top_exps_min).

cstr_empty(cost([],[],[],[],0)).

cstr_from_cexpr(N,cost([],[],[],[],N)):-
	ground(N),!.
cstr_from_cexpr(Exp,cost(Top_exps,Top_exps_neg,[],[(Aux1,1),(Aux2,-1)],0)):-
	is_linear_exp(Exp),!,
	parse_le(Exp,Lin_exp),
	negate_le(Lin_exp,Lin_exp_negated),
	cstr_name_aux_var(Aux1),
	cstr_name_aux_var(Aux2),
	Top_exps=[bound(ub,Lin_exp,[Aux1]),bound(ub,Lin_exp_negated,[Aux2])],
	Top_exps_neg=[bound(lb,Lin_exp,[Aux1]),bound(lb,Lin_exp_negated,[Aux2])].
	
cstr_from_cexpr(nat(Exp),cost(Top_exps,Top_exps_neg,[],[(Aux1,1)],0)):-
	parse_le(Exp,Lin_exp),!,
	cstr_name_aux_var(Aux1),
	Top_exps=[bound(ub,Lin_exp,[Aux1])],
	Top_exps_neg=[bound(lb,Lin_exp,[Aux1])].
cstr_from_cexpr(Exp,_):-
	throw(invalid_cost_expression(Exp)).

cstr_name_aux_var([aux(Num)]):-
	counter_increase(aux_vars,1,Num).

cstr_get_it_name(Loop,[it(Loop)]).

cstr_generate_top_exp(Bounded,Op,Max,bound(Op,Max,Bounded)).
cstr_generate_top_exp_inv(Max,Op,Bounded,bound(Op,Max,Bounded)).

cstr_generate_aux_exp(exp(Index,Index_neg,Exp,Exp_neg),Op,Bounded,bound(Op,exp(Index,Index_neg,Exp,Exp_neg),Bounded)).


cstr_get_lin_exp_from_tops(Op,Tops,Exps_set):-
 	maplist(cstr_get_expression_from_top(Op),Tops,Exps),
 	from_list_sl(Exps,Exps_set).
cstr_get_expression_from_top(Op,bound(Op,Exp,_),Exp).
	


cstr_join_equal_top_expressions(cost(Ub_tops,Lb_tops,Auxs,Bases,Base),cost(Ub_tops2,Lb_tops2,Auxs2,Bases,Base)):-
	cstr_constrs_join_equal_top_expressions(Ub_tops,Ub_tops2,Extra_auxs1),
	cstr_constrs_join_equal_top_expressions(Lb_tops,Lb_tops2,Extra_auxs2),
	ut_flat_list([Extra_auxs1,Extra_auxs2,Auxs],Auxs2).
	
cstr_constrs_join_equal_top_expressions(Tops,Tops2,New_aux):-
	foldl(add_top_to_expr_top_multimap,Tops,[],Exp_Tops_multimap),
	partition(unitary_multimap_entry,Exp_Tops_multimap,Non_repeated_tops_pairs,Repeated_tops_pairs),
	maplist(tuple,_,Non_repeated_tops,Non_repeated_tops_pairs),
	maplist(generate_compressed_top,Repeated_tops_pairs,New_tops,New_aux),
	ut_flat_list([Non_repeated_tops,New_tops],Tops2).

add_top_to_expr_top_multimap(bound(Op,Exp,Bounded),Multimap,Multimap1):-
	put_mm( Multimap, Exp, bound(Op,Exp,Bounded), Multimap1).
	
unitary_multimap_entry((_,[_])).

generate_compressed_top((Exp,Tops),New_top,New_auxs):-
	Tops=[bound(Op,_,_)|_],
	cstr_name_aux_var(Name),
	cstr_generate_top_exp([Name],Op,Exp,New_top),
	maplist(cstr_generate_top_exp_inv(_Exp,Op),Bounded_list,Tops),
	maplist(cstr_generate_aux_exp(exp([(Name,Var)],[],add([mult([Var])]),add([])),Op),Bounded_list,New_auxs).
	
	
	
cstr_remove_cycles(cost(Ub_tops,Lb_tops,Aux_exps,Bases,Base),Short):-
	get_top_bounded(Ub_tops,[],Ub_Bounded_set),
	get_top_bounded(Lb_tops,[],Lb_Bounded_set),
	remove_not_bounded(Aux_exps,Ub_Bounded_set,Lb_Bounded_set,Aux_exps2),
	cstr_remove_useless_constrs(cost(Ub_tops,Lb_tops,Aux_exps2,Bases,Base),Simplified),
	cstr_shorten_variables_names(Simplified,list,Short).


get_top_bounded([],Set,Set).
get_top_bounded([bound(_,_Exp,Bounded)|Top_exps],Set,Set_out):-
	from_list_sl(Bounded,Bounded_set),
	union_sl(Bounded_set,Set,Set_aux),
	get_top_bounded(Top_exps,Set_aux,Set_out).

remove_not_bounded(Aux_exps,Ub_Set,Lb_Set,Aux_exp_out):-
	split_bounded(Aux_exps,Ub_Set,Lb_Set,Ub_Set_1,Lb_Set_1,Bounded,Not_bounded),
	(Bounded=[]->
	  Aux_exp_out=[]
	;
	  remove_not_bounded(Not_bounded,Ub_Set_1,Lb_Set_1,Aux_exp_aux),
	  append(Bounded,Aux_exp_aux,Aux_exp_out)
	  ).
	  
split_bounded([],Ub_Set,Lb_Set,Ub_Set,Lb_Set,[],[]).
split_bounded([bound(ub,exp(Index,Index_neg,Exp,Exp_neg),Bounded)|Aux_exps],Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,[bound(ub,exp(Index,Index_neg,Exp,Exp_neg),Bounded)|Exp_Bounded],Exp_Not_bounded):-
	maplist(tuple,Names,_Vars,Index),
	maplist(contains_sl(Ub_Set),Names),!,
	from_list_sl(Bounded,Bounded_set),
	union_sl(Bounded_set,Ub_Set,Ub_Set_aux),
	split_bounded(Aux_exps,Ub_Set_aux,Lb_Set,Ub_Set_out,Lb_Set_out,Exp_Bounded,Exp_Not_bounded).
	
split_bounded([bound(lb,exp(Index,Index_neg,Exp,Exp_neg),Bounded)|Aux_exps],Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,[bound(lb,exp(Index,Index_neg,Exp,Exp_neg),Bounded)|Exp_Bounded],Exp_Not_bounded):-
	maplist(tuple,Names,_,Index),
	maplist(contains_sl(Lb_Set),Names),
	maplist(tuple,Names_neg,_,Index_neg),
	maplist(contains_sl(Ub_Set),Names_neg),!,
	from_list_sl(Bounded,Bounded_set),
	union_sl(Bounded_set,Lb_Set,Lb_Set_aux),
	split_bounded(Aux_exps,Ub_Set,Lb_Set_aux,Ub_Set_out,Lb_Set_out,Exp_Bounded,Exp_Not_bounded).	

split_bounded([Bound|Aux_exps],Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,Exp_Bounded,[Bound|Exp_Not_bounded]):-
	split_bounded(Aux_exps,Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,Exp_Bounded,Exp_Not_bounded).

cstr_remove_useless_constrs(cost(Ub_tops,Lb_tops,Auxs,Bases,Base),cost(Ub_tops2,Lb_tops2,Auxs2,Bases2,Base)):-
	foldl(compute_initial_reference_set(max),Bases,([],[]),(Bases1,Ref_set1)),
	foldl(compute_initial_reference_set(min),Bases1,([],Ref_set1),(Bases2,Ref_set2)),
	reverse(Auxs,Aux_rev),
	remove_useless_aux_constrs(Aux_rev,Ref_set2,[],Ref_set3,Auxs2),
	exclude(useless_top_constr(Ref_set3),Ub_tops,Ub_tops2),
	exclude(useless_top_constr(Ref_set3),Lb_tops,Lb_tops2).

cstr_remove_useless_constrs_max_min(cost(Ub_tops,Lb_tops,Auxs,Bases,Base),Max_min,cost(Ub_tops2,Lb_tops2,Auxs2,Bases2,Base)):-
	foldl(compute_initial_reference_set(Max_min),Bases,([],[]),(Bases2,Ref_set)),
	reverse(Auxs,Aux_rev),
	remove_useless_aux_constrs(Aux_rev,Ref_set,[],Ref_set1,Auxs2),
	exclude(useless_top_constr(Ref_set1),Ub_tops,Ub_tops2),
	exclude(useless_top_constr(Ref_set1),Lb_tops,Lb_tops2).

	
compute_initial_reference_set(_,(_Name,0),(Bases,Ref_set),(Bases,Ref_set)).
compute_initial_reference_set(min,(Name,Value),(Bases,Ref_set),([(Name,Value)|Bases],Ref_set2)):-
	(greater_fr(Value,0)->
		insert_sl(Ref_set,lb(Name),Ref_set2)
		;
		insert_sl(Ref_set,ub(Name),Ref_set2)
		).
compute_initial_reference_set(max,(Name,Value),(Bases,Ref_set),([(Name,Value)|Bases],Ref_set2)):-
	(greater_fr(Value,0)->
		insert_sl(Ref_set,ub(Name),Ref_set2)
		;
		insert_sl(Ref_set,lb(Name),Ref_set2)
		).	

opposite_sign(ub,lb).
opposite_sign(lb,ub).

remove_useless_aux_constrs([],Ref_set,Auxs,Ref_set,Auxs).
remove_useless_aux_constrs([bound(Op,Exp,Bounded)|Auxs],Ref_set_accum,Auxs_accum,Ref_set,Auxs_out):-
	opposite_sign(Op,Op_neg),
	maplist(zip_with(Op),Bounded,Bounded_op),	
	from_list_sl(Bounded_op,Bounded_set),
	(Op=ub->
	intersection_sl(Ref_set_accum,Bounded_set,Bounded1_op),
	Bounded1_op\=[]
	;
	intersection_sl(Ref_set_accum,Bounded_set,Bounded_set),
	Bounded1_op=Bounded_set
	),!,
	maplist(zip_with(Op),Bounded1,Bounded1_op),
	Exp=exp(Index,Index_neg,_,_),
	add_elements_from_index(Op,Index,Ref_set_accum,Ref_set_accum1),
	add_elements_from_index(Op_neg,Index_neg,Ref_set_accum1,Ref_set_accum2),
	remove_useless_aux_constrs(Auxs,Ref_set_accum2,[bound(Op,Exp,Bounded1)|Auxs_accum],Ref_set,Auxs_out).


remove_useless_aux_constrs([_|Auxs],Ref_set_accum,Auxs_accum,Ref_set,Auxs_out):-	
	remove_useless_aux_constrs(Auxs,Ref_set_accum,Auxs_accum,Ref_set,Auxs_out).		

zip_with(Op,Elem,Zipped):-
	Zipped=..[Op,Elem].
	
add_elements_from_index(Op,Index,Set,Set1):-
	maplist(tuple,Names,_,Index),
	maplist(zip_with(Op),Names,Names_op),
	from_list_sl(Names_op,Names_set),
	union_sl(Names_set,Set,Set1).

useless_top_constr(Ref_set,bound(Op,_,Bounded)):-
	maplist(zip_with(Op),Bounded,Bounded_op),	
	from_list_sl(Bounded_op,Bounded_set),
	(Op=ub->
	intersection_sl(Bounded_set,Ref_set,[])
	;
	\+intersection_sl(Bounded_set,Ref_set,Bounded_set)
	).
		

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
	
opposite_operator(ub,lb).
opposite_operator(lb,ub).

is_ub_bound(bound(ub,_,_)).	
	
cstr_maxminimization(Cost_long,Max_min,Cost_final):-
	cstr_shorten_variables_names(Cost_long,no_list,Cost_short),	
	cstr_remove_useless_constrs_max_min(Cost_short,Max_min,cost(Ub_tops,Lb_tops,Aux_exps,Bases,Base)),
	generate_constraint_with_base(Bases,Base,Max_min,bound(Op,Exp_cost,_)),
	term_variables((Ub_tops,Lb_tops),Entry_vars),
	ut_flat_list([Ub_tops,Lb_tops,Aux_exps],All_constrs),
	maplist(annotate_bounded,All_constrs,All_constrs_annotated),
	get_non_deterministic_vars(All_constrs_annotated,[],Non_det_vars),
	compress_constraints(All_constrs_annotated,Non_det_vars,Remaining_constrs,[],Map),
	%maplist(writeln,Map),
	solve_expression(Exp_cost,Op,Non_det_vars,Map,Solved_exp),
	split_remaining_constrs(Remaining_constrs,Remaining_groups),
	exclude(=([]),Remaining_groups,Remaining_groups1),
	maplist(annotate_group,Remaining_groups1,Remaining_groups2),
	findall((Entry_vars,Cost_closed),
	(incremental_maxminization(Remaining_groups2,Solved_exp,Cost),
	remove_undefined_vars(Cost,Cost_closed))
	,Costs_list),
	assign_right_vars(Costs_list,Entry_vars,Costs_list_right),
	from_list_sl(Costs_list_right,Cost_set),!,
	%maplist(writeln,Cost_set),
	maplist(cstr_get_cexpr_from_normalform_deep,Cost_set,Cost_set_p),
	%maplist(writeln,Cost_set_p),
	Cost_final=..[Max_min,Cost_set_p],!.

cstr_maxminimization(Cost_long,Max_min,_):-
	throw(maximization_failed(Cost_long,Max_min)).	
	
	
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
		
substitute_index_by_default((lb(_),0)).
substitute_index_by_default((ub(_),inf)).
		
incremental_maxminization([],Exp,Exp).
incremental_maxminization([Group|Rest],Semi_solved_exp,Exp):-
	solve_group(Group,Map),
	maplist(evaluate_group(Map),Rest,Rest1),
	simplify_partial_exp(Semi_solved_exp,Map,Semi_solved_exp1),
	incremental_maxminization(Rest1,Semi_solved_exp1,Exp).

evaluate_group(Map,group(Op,Constrs),group(Op,Constrs1)):-
	maplist(evaluate_constr(Map),Constrs,Constrs1).
	
evaluate_constr(Map,bound(Op,Exp,Bounded),bound(Op,Exp1,Bounded)):-
	simplify_partial_exp(Exp,Map,Exp1).
	

simplify_partial_exp(partial(Index,Exp),Map,Solved_exp):-!,
	maplist(substitute_index_by_optional(Map),Index,Extra_index),
	ut_flat_list(Extra_index,Index_flat),
	simplify_expression(Exp,Simple_exp),
	(Index_flat=[]->
		Solved_exp=Simple_exp
	;
		Solved_exp=partial(Index_flat,Simple_exp)
	).	
simplify_partial_exp(Exp,_Map,Exp).

substitute_index_by_optional(Map_accum,(Name,Var),[]):-
		lookup_lm(Map_accum,Name,Var),!.
		
substitute_index_by_optional(_Map_accum,(Name,Var),[(Name,Var)]).

annotate_group(Group,group(Op,Group)):-
	Group=[bound(Op,_,_)|_].

solve_group(group(ub,Cons),Map):-
	sort_with(Cons,better_ubs,Cons_sorted),
	simplify_group(Cons_sorted,[],Cons_sorted1),
	solve_group_1(Cons_sorted1,[],Map).
	
solve_group(group(lb,Cons),Map):-
	sort_with(Cons,better_lbs,Cons_sorted),
	simplify_group(Cons_sorted,[],Cons_sorted1),
	solve_group_1(Cons_sorted1,[],Map).

better_ubs(bound(ub,Exp,_Bounded),bound(ub,Exp2,_Bounded2)):-
	complexity(Exp,C1),
	complexity(Exp2,C2),
	C1>C2,!.
	
better_ubs(bound(ub,Exp,Bounded),bound(ub,Exp2,Bounded2)):-
	complexity(Exp,C1),
	complexity(Exp2,C2),
	C1=C2,
	length(Bounded,N),length(Bounded2,N2),N<N2.

	
better_lbs(bound(lb,Exp,_Bounded),bound(lb,Exp2,_Bounded2)):-
	complexity(Exp,C1),
	complexity(Exp2,C2),
	C1<C2,!.
	
better_lbs(bound(lb,Exp,Bounded),bound(lb,Exp2,Bounded2)):-
	complexity(Exp,C1),
	complexity(Exp2,C2),
	C1=C2,
	length(Bounded,N),length(Bounded2,N2),N>N2.	
	

complexity(partial(_,_),100).
complexity(Summand,N):-
	complexity_internal(Summand,N).
	
complexity_internal(add(Summands),N):-
	(Summands=[_|_]->
	maplist(complexity_internal,Summands,N_list),
	max_list(N_list,N)
	;
	N=0).
complexity_internal(mult(Factors),N):-
	maplist(complexity_internal,Factors,N_list),
	sum_list(N_list,N).
complexity_internal(max(Factors),N):-
	maplist(complexity_internal,Factors,N_list),
	max_list(N_list,N).
complexity_internal(min(Factors),N):-
	maplist(complexity_internal,Factors,N_list),
	min_list(N_list,N).	
complexity_internal(nat(Factor),N):-
	nonvar(Factor),
	Factor=add(_Summands),!,
	complexity_internal(Factor,N).
complexity_internal(nat(Factor),0):-
	ground(Factor),!.
complexity_internal(nat(_Factor),1).
complexity_internal(inf,100):-!.
complexity_internal(N,0):-
	is_fraction(N),!.
	
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

	
get_constr_op(max,ub).
get_constr_op(min,lb).

get_non_deterministic_vars([],Accum_set,Accum_set).
get_non_deterministic_vars([bound(_,_,[_Bounded])|Constrs],Accum_set,Non_det_vars):-!,
	get_non_deterministic_vars(Constrs,Accum_set,Non_det_vars).
get_non_deterministic_vars([bound(_,_,Bounded)|Constrs],Accum_set,Non_det_vars):-
	union_sl(Bounded,Accum_set,Accum_set2),
	get_non_deterministic_vars(Constrs,Accum_set2,Non_det_vars).	


compress_constraints([],_,[],Map,Map).
compress_constraints([bound(Op,Exp,Bounded)|Constrs],Non_det_vars,Remaining_constrs,Map_accum,Map_out):-
	solve_expression(Exp,Op,Non_det_vars,Map_accum,Solved_exp),
	Bounded=[Bounded1|_],
	(contains_sl(Non_det_vars,Bounded1)->
		Remaining_constrs=[bound(Op,Solved_exp,Bounded)|Remaining_constrs1],
		Map_accum2=Map_accum
	;
	 	add_to_bound_map(Map_accum,Bounded1,Solved_exp,Map_accum2),
	 	Remaining_constrs=Remaining_constrs1
	),
	compress_constraints(Constrs,Non_det_vars,Remaining_constrs1,Map_accum2,Map_out).
	
add_to_bound_map(Map,Bounded,Solved_exp,Map2):-
	lookup_lm(Map,Bounded,Expr),!,
	Bounded=..[Op|_],
	combine_expression(Op,Expr,Solved_exp,New_exp),
	insert_lm(Map,Bounded,New_exp,Map2).
add_to_bound_map(Map,Bounded,Solved_exp,Map2):-
	insert_lm(Map,Bounded,Solved_exp,Map2).	

combine_expression(Op,partial(Index,Exp),partial(Index2,Exp2),partial(Index3,Exp3)):-!,
	append(Index,Index2,Index3),
	combine_expression_1(Op,Exp,Exp2,Exp3).
combine_expression(Op,partial(Index,Exp),Exp2,partial(Index,Exp3)):-!,
	combine_expression_1(Op,Exp,Exp2,Exp3).	
combine_expression(Op,Exp,partial(Index,Exp2),partial(Index,Exp3)):-!,
	combine_expression_1(Op,Exp,Exp2,Exp3).		
combine_expression(Op,Exp,Exp2,Exp3):-!,
	combine_expression_1(Op,Exp,Exp2,Exp3).	
		

combine_expression_1(ub,min(List),Exp,min([Exp|List])):-!.
combine_expression_1(ub,Exp1,Exp2,min([Exp1,Exp2])).	
combine_expression_1(lb,max(List),Exp,max([Exp|List])):-!.
combine_expression_1(lb,Exp1,Exp2,max([Exp1,Exp2])).
	
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
	simplify_expression(nat(add(All_summands)),Simple_exp),
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
	
substitute_index_by(Map_accum,(Name,Var1),Index1):-
		lookup_lm(Map_accum,Name,Exp),!,
		(Exp=partial(Index,Var)->	
			Index1=Index,
			Var1=Var
			;
			Var1=Exp,
			Index1=[]
		).
		
substitute_index_by(_Map_accum,(lb(_Name),add([])),[]).


cstr_get_cexpr_from_normalform_deep(add(Summands),Exp3):-
	maplist(write_product_deep,Summands,Summands2),
	write_sum(Summands2,Exp3).
cstr_get_cexpr_from_normalform_deep(nat(Lin_exp),nat(Lin_exp)):-var(Lin_exp),!.

cstr_get_cexpr_from_normalform_deep(nat(add(Summands)),nat(Exp3)):-!,
	maplist(write_product_deep,Summands,Summands2),
	write_sum(Summands2,Exp3).
	
cstr_get_cexpr_from_normalform_deep(Else,Else).	
	
write_product_deep(mult(List),Product):-
	maplist(write_factor_deep,List,List_p),
	write_product(List_p,Product).

write_factor_deep(max(Elems),max(Elems_p)):-!,
	maplist(cstr_get_cexpr_from_normalform_deep,Elems,Elems_p).
write_factor_deep(min(Elems),min(Elems_p)):-!,
	maplist(cstr_get_cexpr_from_normalform_deep,Elems,Elems_p).	

write_factor_deep(nat(Elem),nat(Exp)):-nonvar(Elem),
	functor(Elem,add,1),!,
	cstr_get_cexpr_from_normalform_deep(Elem,Exp).
write_factor_deep(add(Elem),Exp):-!,
	cstr_get_cexpr_from_normalform_deep(add(Elem),Exp).	
write_factor_deep(X,X).

simplify_expression(Exp,Exp):-var(Exp),!.
simplify_expression(Exp,Simple_exp):-
	nonvar(Exp),
	Exp=nat(Exp_internal),
	nonvar(Exp_internal),
	Exp_internal=add(Summands),
	!,
	simplify_summands(Summands,Summands_simple),
	(Summands_simple==[]->
		Simple_exp=add([])
	;
		Simple_exp=nat(add(Summands_simple))
	).
simplify_expression(Exp,Simple_exp):-
	nonvar(Exp),
	Exp=add(Summands),!,
	simplify_summands(Summands,Summands_simple),
	Simple_exp=add(Summands_simple).	
	
simplify_expression(Exp,Exp).
	

simplify_summands(Summands,Summands_compressed):-
	maplist(simplify_factor,Summands,Summands_simple),
	ut_flat_list(Summands_simple,Summands_simple_flat),
	compress_summads(Summands_simple_flat,Summands_compressed).

compress_summads(Summands_simple_flat,Summands_compressed_sorted):-
	maplist(extract_constant_factor_and_normalize,Summands_simple_flat,Summand_pairs),
	add_all_equal(Summand_pairs,[],Map),
	maplist(recover_factor,Map,Summands_compressed),
	exclude(zero_factor_var,Summands_compressed,Summands_compressed1),
	from_list_sl(Summands_compressed1,Summands_compressed_sorted).

extract_constant_factor_and_normalize(mult(Factors),(mult(Not_numbers_sorted),Amount)):-
	partition(is_fraction,Factors,Numbers,Not_numbers),
	ut_sort(Not_numbers,Not_numbers_sorted),
%	(ut_var_member(add([]),Not_numbers)->
	%	Amount=0
%		;
	foldl(multiply_fr,Numbers,1,Amount).
%	).

add_all_equal([],Map,Map).
add_all_equal([(Elem,Amount)|Pairs],Map,Map_out):-
	lookup_lm(Map,Elem,Amount2),!,
	sum_fr(Amount,Amount2,Amount_new),
	insert_lm(Map,Elem,Amount_new,Map1),
	add_all_equal(Pairs,Map1,Map_out).
	
add_all_equal([(Elem,Amount)|Pairs],Map,Map_out):-
	insert_lm(Map,Elem,Amount,Map1),
	add_all_equal(Pairs,Map1,Map_out).	

recover_factor((mult([]),1),mult([1])):-!.	
recover_factor((mult(Factors),1),mult(Factors)):-!.
recover_factor((mult(_Factors),0),mult([0])):-!.
recover_factor((mult(Factors),Amount),mult([Amount|Factors])).	
	
simplify_factor(mult(Factors),Summands_final):-
	select_not_var(Factors,add(Summands),Factors1),!,
	maplist(multiply_by_factors(Factors1),Summands,Summands1),
	ut_flat_list(Summands1,Summands_flat),
	maplist(simplify_factor,Summands_flat,Summands_final).

simplify_factor(mult(Factors),mult(Factors1)):-
	maplist(simplify_factor_internal,Factors,Factors1),!.
	
	
multiply_by_factors(Factors1,mult(Summand),mult(Factors2)):-
	append(Factors1,Summand,Factors2).	
	
simplify_factor_internal(Var,Var):-var(Var),!.

simplify_factor_internal(min(List),Res):-!,
	maplist(simplify_expression,List,List_simplified),
	from_list_sl(List_simplified,Set),
	(Set=[One]->
		Res=One
	;
		Res=min(Set)
	).
simplify_factor_internal(max(List),Res):-!,
	maplist(simplify_expression,List,List_simplified),
	from_list_sl(List_simplified,Set),
	(Set=[One]->
		Res=One
	;
		Res=max(Set)
	).
simplify_factor_internal(Factor,Factor_simple):-
	simplify_expression(Factor,Factor_simple),!.


index_in_set(Set,(Elem,_)):-
	contains_sl(Set,Elem).
index_not_in_set(Set,(Elem,_)):-
	\+contains_sl(Set,Elem).	
	
unify_pair((X,X)).
	
	
select_not_var([Factor|Factors],Factor1,Factors):-
	\+var(Factor),
	Factor=Factor1.
select_not_var([Factor|Factors],Factor1,[Factor|Factors1]):-
	select_not_var(Factors,Factor1,Factors1).
	
is_fraction(N):-nonvar(N),number(N).
is_fraction(N/M):-nonvar(N),number(N),number(M).

zero_factor_var(mult([Zero])):-nonvar(Zero),Zero==0.	


	
negate_summand(mult(Factors),mult([-1|Factors])).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
cstr_get_cexpr_from_normalform_ground(exp(Index1,Index2,add(Summands),add(Summands2)),Exp3):-
	cstr_get_cexpr_from_normalform(add(Summands),Exp1),
	cstr_get_cexpr_from_normalform(add(Summands2),Exp2),
	( Exp2==0 ->
	  Exp3=Exp1
	  ;
	  Exp3=Exp1-Exp2
	 ),
	maplist(tuple,X,X,Index1),
	maplist(tuple,X2,X2,Index2).
	
	
cstr_get_cexpr_from_normalform(add(Summands),Exp3):-
	maplist(write_product_1,Summands,Summands2),
	write_sum(Summands2,Exp3).

write_product_1(mult(List),Product):-
	write_product(List,Product).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cstr_extend_variables_names(cost(Ub_tops,Lb_tops,Aux_exps,Bases,Base),Prefix,cost(Ub_tops1,Lb_tops1,Aux_exps1,Bases1,Base)):-
		maplist(extend_top_exp_name(Prefix),Ub_tops,Ub_tops1),
		maplist(extend_top_exp_name(Prefix),Lb_tops,Lb_tops1),
		maplist(extend_aux_exp_name(Prefix),Aux_exps,Aux_exps1),
		maplist(extend_base_name(Prefix),Bases,Bases1).


extend_base_name(Prefix,(Name,Value),([Prefix|Name],Value)).
extend_aux_exp_name(Prefix,bound(Op,Exp,Bounded),bound(Op,Exp1,Bounded2)):-
	extend_aux_exp_name_1(Prefix,Exp,Exp1),
	maplist(append([Prefix]),Bounded,Bounded2).

extend_aux_exp_name_1(Prefix,exp(Index,Index_neg,Exp,Exp_neg),exp(Index2,Index_neg2,Exp,Exp_neg)):-
	maplist(extend_base_name(Prefix),Index,Index2),
	maplist(extend_base_name(Prefix),Index_neg,Index_neg2).
	
extend_top_exp_name(Prefix,bound(Op,Expression,Bounded),bound(Op,Expression,Bounded2)):-
	maplist(append([Prefix]),Bounded,Bounded2).	
	
cstr_shorten_variables_names(cost(Ub_tops,Lb_tops,Aux_exps,Bases,Base),Flag,cost(Ub_tops1,Lb_tops1,Aux_exps1,Bases1,Base)):-
		maplist(shorten_top_exp_name(Flag),Ub_tops,Ub_tops1),
		maplist(shorten_top_exp_name(Flag),Lb_tops,Lb_tops1),
		maplist(shorten_aux_exp_name(Flag),Aux_exps,Aux_exps1),
		maplist(shorten_base_name(Flag),Bases,Bases1).
		
shorten_base_name(Flag,(Name,Value),(Short_name,Value)):-
	shorten_name(Flag,Name,Short_name).
shorten_aux_exp_name(Flag,bound(Op,Expression,Bounded),bound(Op,Expression2,Bounded2)):-
	shorten_aux_exp_name_1(Flag,Expression,Expression2),
	maplist(shorten_name(Flag),Bounded,Bounded2).
	
shorten_aux_exp_name_1(Flag,exp(Index,Index_neg,Exp,Exp_neg),exp(Index2,Index_neg2,Exp,Exp_neg)):-
	maplist(shorten_base_name(Flag),Index,Index2),
	maplist(shorten_base_name(Flag),Index_neg,Index_neg2).
	
shorten_top_exp_name(Flag,bound(Op,Expression,Bounded),bound(Op,Expression,Bounded2)):-
	maplist(shorten_name(Flag),Bounded,Bounded2).	


shorten_name(list,Name,Short_name):-
	term_hash(Name,Hash),
	(short_db(Hash,Name,Short_name)->
		true
		;
	 	counter_increase(short_terms,1,Id),
	 	assert(short_db(Hash,Name,[s(Id)])),
	 	Short_name=[s(Id)]
	 	).
shorten_name(no_list,Name,Short_name):-
	term_hash(Name,Hash),
	(short_db(Hash,Name,Short_name)->
		true
		;
	 	counter_increase(short_terms,1,Id),
	 	assert(short_db(Hash,Name,s(Id))),
	 	Short_name=s(Id)
	 	).	 	
	 	
cstr_join(cost(T,A,Auxs,Bs,B),cost(T2,A2,Auxs2,B2s,B2),cost(T3,A3,Auxs3,B3s,B3)):-
	append(T,T2,T3),
	append(A,A2,A3),
	append(Auxs,Auxs2,Auxs3),
	append(Bs,B2s,B3s),
	sum_fr(B,B2,B3).	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cstr_propagate_summatory(Loop,cost(Ub_tops,Lb_tops,Auxs,Bases,Base),cost(Ub_tops2,Lb_tops2,Aux2,[([it(Loop)],Base)|Bases1],0),(Ub_Summatories,Lb_Summatories)):-
	generate_initial_sum_map(Bases,[],Sum_map_initial,Bases1),
	propagate_sum_aux_backwards(Auxs,Sum_map_initial,Aux2,Sum_map,Max_map),
	get_maxs(Ub_tops,Max_map,Ub_tops2),
	get_summatories(Ub_tops,Sum_map,Ub_Summatories),
	get_maxs(Lb_tops,Max_map,Lb_tops2),
	get_summatories(Lb_tops,Sum_map,Lb_Summatories).

	
get_maxs([],_,[]).
get_maxs([bound(Op,Exp,Bounded)|Tops],Max_set,Tops2):-
	include(contains_sl(Max_set),Bounded,Non_summatories),
	(Non_summatories\=[]->
		Tops2=[bound(Op,Exp,Non_summatories)|Tops1]
		;
		Tops2=Tops1
		),
	get_maxs(Tops,Max_set,Tops1).
	
get_summatories([],_,[]).
get_summatories([bound(Op,Exp,Bounded)|Tops],Sum_map,Tops2):-
	get_mapped(Bounded,Sum_map,New_names),
	(New_names\=[]->
		Tops2=[bound(Op,Exp,New_names)|Tops1]
		;
		Tops2=Tops1
		),
	get_summatories(Tops,Sum_map,Tops1).

generate_initial_sum_map([],Map,Map,[]).
generate_initial_sum_map([(Name,Val)|Bases],Map,Map_out,[(Name2,Val)|Bases1]):-
	lookup_lm(Map,Name,Name2),!,
	generate_initial_sum_map(Bases,Map,Map_out,Bases1).
generate_initial_sum_map([(Name,Val)|Bases],Map,Map_out,[(Name2,Val)|Bases1]):-
	cstr_name_aux_var(Name2),
	insert_lm(Map,Name,Name2,Map1),
	generate_initial_sum_map(Bases,Map1,Map_out,Bases1).
	
	
propagate_sum_aux_backwards([],Sum_map,[],Sum_map,[]).
propagate_sum_aux_backwards([bound(Op,Exp,Bounded)|Aux_ini],Sum_map_initial,Aux3,Sum_map3,Max_map4):-	
	Exp=exp(Index1,Index2,Std_exp,Std_exp_neg),
	append(Index1,Index2,Index_total),
	propagate_sum_aux_backwards(Aux_ini,Sum_map_initial,Aux,Sum_map,Max_map),
	get_mapped(Bounded,Sum_map,New_names),
	include(contains_sl(Max_map),Bounded,Non_summatories),
	(Non_summatories\=[]->
		Aux2=[bound(Op,Exp,Non_summatories)|Aux],
		foldl(add_indexes_to_set,Index_total,Max_map,Max_map2)
	;
	  Aux2=Aux,
	  Max_map2=Max_map
	),
	(New_names\=[]->

	%this means some are multiplied (the new names can be the same as the old if they did not coicide
	update_max_set(Index1,Std_exp,Index1_max,Max_map2,Max_map3),
	update_max_set(Index2,Std_exp_neg,Index2_max,Max_map3,Max_map4),
	
	update_sum_map(Index1,Std_exp,Index1_sum,Max_map4,Sum_map,Sum_map2),
	append(Index1_max,Index1_sum,Index1_final),
	update_sum_map(Index2,Std_exp_neg,Index2_sum,Max_map3,Sum_map2,Sum_map3),
	append(Index2_max,Index2_sum,Index2_final),
	Aux3=[bound(Op,exp(Index1_final,Index2_final,Std_exp,Std_exp_neg),New_names)|Aux2]
	;
	Aux3=Aux2,
	Sum_map3=Sum_map,
	Max_map4=Max_map2
	).

get_mapped([],_,[]).
get_mapped([X|Xs],Map,[New_name|New_names]):-
	lookup_lm(Map,X,New_name),!,
	get_mapped(Xs,Map,New_names).
get_mapped([_|Xs],Map,New_names):-
	get_mapped(Xs,Map,New_names).
	
add_indexes_to_set((Name,_Var),Max_map,Max_map2):-
	insert_sl(Max_map,Name,Max_map2).
	
update_max_set(Index,Expr,Index_max,Max_set,Max_set2):-
	get_all_but_first_factor(Expr,Vars_set),
	include(pair_contains(Vars_set),Index,Index_max),
	maplist(tuple,Names,_,Index_max),
	from_list_sl(Names,Names_set),
	union_sl(Names_set,Max_set,Max_set2).
	
pair_contains(Set,(_,Var)):-
	contains_sl(Set,Var).
get_all_but_first_factor(add(Summands),Vars):-
	maplist(get_all_but_first_factor_1,Summands,Vars_list),
	unions_sl(Vars_list,Vars).
get_all_but_first_factor_1(mult([_|Rest_factors]),Vars_set):-
	term_variables(Rest_factors,Vars),
	from_list_sl(Vars,Vars_set).
	
get_first_factor(add(Summands),Vars):-	
	maplist(get_first_factor_1,Summands,Vars_list),
	unions_sl(Vars_list,Vars).
get_first_factor_1(mult([First|_]),Vars_set):-
	term_variables(First,Vars),
	from_list_sl(Vars,Vars_set).

update_sum_map(Index,Expr,Index_sum_substituted,Max_map,Sum_map,Sum_map2):-
	get_first_factor(Expr,Vars_set),
	include(pair_contains(Vars_set),Index,Index_sum),
	substitute_by_new_name(Index_sum,Max_map,Sum_map,Index_sum_substituted,Sum_map2).

substitute_by_new_name([],_Max_map,Sum_map,[],Sum_map).
substitute_by_new_name([(Name,Var)|Index_sum],Max_map,Sum_map,[(New_name,Var)|Index_sum_substituted],Sum_map3):-
%	contains_sl(Max_map,Name),!,
	(lookup_lm(Sum_map,Name,New_name),Sum_map2=Sum_map
	;
	cstr_name_aux_var(New_name),
	insert_lm(Sum_map,Name,New_name,Sum_map2)),
	substitute_by_new_name(Index_sum,Max_map,Sum_map2,Index_sum_substituted,Sum_map3).