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
		cstr_constant/2,
		cstr_naive_maximization/2,
		cstr_name_aux_var/1,
		cstr_get_it_name/2,
		cstr_generate_top_exp/3,
		cstr_generate_top_exp_inv/3,
		cstr_get_cexpr_from_normalform/2,
		cstr_remove_cycles/2,
		cstr_extend_variables_names/3,
		cstr_propagate_summatory/4,
		cstr_join/3,
		cstr_get_lin_exp_from_tops/2,
		cstr_join_equal_top_expressions/2,
		cstr_shorten_variables_names/2]).
:- use_module(cofloco_utils,[write_sum/2,write_product/2,tuple/3]).	
:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(utils),[ut_flat_list/2]).	
:- use_module(stdlib(multimap),[put_mm/4,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).
:- use_module(stdlib(set_list),[contains_sl/2,from_list_sl/2,unions_sl/2,union_sl/3,insert_sl/3,intersection_sl/3]).

:-dynamic short_db/3.

cstr_empty(cost(([],[]),([],[]),[],0)).
cstr_constant(C,cost(([],[]),([],[]),[],C)).

cstr_name_aux_var([aux(Num)]):-
	counter_increase(aux_vars,1,Num).

cstr_get_it_name(Loop,[it(Loop)]).

cstr_generate_top_exp(Bounded,Max,bound(Max,Bounded)).
cstr_generate_top_exp_inv(Max,Bounded,bound(Max,Bounded)).

cstr_generate_aux_exp(Index,Exp,Bounded,bound(Index,Exp,Bounded)).


cstr_get_lin_exp_from_tops(Tops,Exps_set):-
 	maplist(cstr_get_expression_from_top,Tops,Exps),
 	from_list_sl(Exps,Exps_set).
cstr_get_expression_from_top(bound(Exp,_),Exp).


cstr_naive_maximization(Cost_long,Cost):-
	cstr_shorten_variables_names(Cost_long,cost((Top_exps,Aux_exps),_,Bases,Base)),	
	get_top_bounded(Top_exps,[],Map_bounded),
	remove_not_bounded(Aux_exps,Map_bounded,Map_final,_Aux_exps2,_Removed),
	maplist(substitute_base(Map_final,max),Bases,Concrete_bases),
	write_sum([Base|Concrete_bases],Cost).
	
/*	
cstr_minimization(Cost_long,Exp+Base):-
	term_variables(Tops_exps,Vars),
	cstr_shorten_variables_names(Cost_long,cost(_,(Top_exps,Aux_exps),Bases,Base)),	
	append(Tops_exps,Aux_exps,All_exps),
	incremental_minimization(All_exps,Vars,[],Bases,Exp).
	
incremental_minimization([],_,Map,Bases,Cost):-
	maplist(substitute_base(Map,min),Bases,Concrete_bases),
	write_sum([Base|Concrete_bases],Cost).

incremental_minimization([bound(Exp,[Bounded])|Exps],Vars,Map,Bases,Cost):-!,
	add_bound_to_multimap(Exp),Bounded,Map,Map_aux)
	incremental_minimization(Exps,Vars,Map_aux,Bases,Cost).	
	
incremental_minimization([bound(Exp,Bounded)|Exps],Vars,Map,Bases,Cost):-
	findall((Vars,Costs),
		member(Bounded1,Bounded),
	add_bound_to_multimap(Exp),Bounded,Map,Map_aux),
	incremental_minimization(Exps,Map_aux,Bases,Cost).		
	
	maplist(tuple,Names,Vars,Elems),
	maplist(values_of_mm(Map),Names,Expressions),!,
	maplist(min_expression,Expressions,Expressions2),
	copy_term((Vars,Exp),(Vars2,Exp2)),
	cstr_get_cexpr_from_normalform(Exp2,Exp3),
	Vars2=Expressions2,
	foldl(add_bound_to_multimap(Exp3),Bounded,Map,Map_aux),
*/	
substitute_base(_Map,_,(_Name,0),0):-!.
substitute_base(_Map,_,(_Name,N),0):-number(N),N < 0.

substitute_base(Map,max,(Name,Val),Concrete):-
	values_of_mm(Map,Name,Values),!,
	(Values=[One]->
		Concrete=Val*One
		;
		Concrete=min(Values)*Val
		).
substitute_base(_Map,max,(_Name,_Val),inf).	


substitute_base(Map,min,(Name,Val),Concrete):-
	values_of_mm(Map,Name,Values),!,
	(Values=[One]->
		Concrete=Val*One
		;
		Concrete=max(Values)*Val
		).
substitute_base(_Map,min,(_Name,_Val),0).	

cstr_join_equal_top_expressions(cost(Ub_cons,Lb_cons,Bases,Base),cost(Ub_cons2,Lb_cons2,Bases,Base)):-
	cstr_constrs_join_equal_top_expressions(Ub_cons,Ub_cons2),
	cstr_constrs_join_equal_top_expressions(Lb_cons,Lb_cons2).
	
cstr_constrs_join_equal_top_expressions((Tops,Auxs),(Tops2,Auxs2)):-
	foldl(add_top_to_expr_top_multimap,Tops,[],Exp_Tops_multimap),
	partition(unitary_multimap_entry,Exp_Tops_multimap,Non_repeated_tops_pairs,Repeated_tops_pairs),
	maplist(tuple,_,Non_repeated_tops,Non_repeated_tops_pairs),
	maplist(generate_compressed_top,Repeated_tops_pairs,New_tops,New_aux),
	ut_flat_list([Non_repeated_tops,New_tops],Tops2),
	ut_flat_list([New_aux,Auxs],Auxs2).

add_top_to_expr_top_multimap(bound(Exp,Bounded),Multimap,Multimap1):-
	put_mm( Multimap, Exp, bound(Exp,Bounded), Multimap1).
	
unitary_multimap_entry((_,[_])).

generate_compressed_top((Exp,Tops),New_top,New_auxs):-
	cstr_name_aux_var(Name),
	cstr_generate_top_exp([Name],Exp,New_top),
	maplist(cstr_generate_top_exp_inv(_Exp),Bounded_list,Tops),
	maplist(cstr_generate_aux_exp([(Name,Var)],add([mult([Var])])),Bounded_list,New_auxs).
	
	
	
	
cstr_remove_cycles(cost(Ub_cons,Lb_cons,Bases,Base),Short):-
	cstr_remove_constrs_cycles(Ub_cons,Ub_cons2),
	cstr_remove_constrs_cycles(Lb_cons,Lb_cons2),
	cstr_remove_useless_constrs(cost(Ub_cons2,Lb_cons2,Bases,Base),Simplified),
	cstr_shorten_variables_names(Simplified,Short).

cstr_remove_constrs_cycles((Top_exps,Aux_exps),(Top_exps,Aux_exps2)):-
	get_top_bounded(Top_exps,[],Map_bounded),
	remove_not_bounded(Aux_exps,Map_bounded,_Map_final,Aux_exps2,_Removed).

cstr_remove_useless_constrs(cost(Ub_cons,Lb_cons,Bases,Base),cost(Ub_cons2,Lb_cons2,Bases1,Base)):-
	foldl(compute_initial_reference_set,Bases,([],[]),(Bases1,Ref_set)),
	cstr_constr_remove_useless_constrs(Ub_cons,max,Ref_set,Ub_cons2),
	cstr_constr_remove_useless_constrs(Lb_cons,min,Ref_set,Lb_cons2).

cstr_constr_remove_useless_constrs((Tops,Auxs),Max_min,Ref_set,(Tops2,Auxs2)):-
	reverse(Auxs,Aux_rev),
	remove_useless_aux_constrs(Aux_rev,Ref_set,[],Max_min,Ref_set1,Auxs2),
	exclude(useless_top_constr(Ref_set1,Max_min),Tops,Tops2).
	
compute_initial_reference_set((_Name,0),(Bases,Ref_set),(Bases,Ref_set)).
compute_initial_reference_set((Name,Value),(Bases,Ref_set),([(Name,Value)|Bases],Ref_set1)):-
	insert_sl(Ref_set,Name,Ref_set1).

remove_useless_aux_constrs([],Ref_set,Auxs,_,Ref_set,Auxs).
remove_useless_aux_constrs([bound(Index,Exp,Bounded)|Auxs],Ref_set_accum,Auxs_accum,max,Ref_set,Auxs_out):-	
	from_list_sl(Bounded,Bounded_set),
	intersection_sl(Ref_set_accum,Bounded_set,Bounded1),
	Bounded1\=[],!,
	maplist(tuple,Names,_,Index),
	from_list_sl(Names,Names_set),
	union_sl(Names_set,Ref_set_accum,Ref_set_accum2),
	remove_useless_aux_constrs(Auxs,Ref_set_accum2,[bound(Index,Exp,Bounded1)|Auxs_accum],max,Ref_set,Auxs_out).
	
remove_useless_aux_constrs([_|Auxs],Ref_set_accum,Auxs_accum,max,Ref_set,Auxs_out):-	
	remove_useless_aux_constrs(Auxs,Ref_set_accum,Auxs_accum,max,Ref_set,Auxs_out).		

remove_useless_aux_constrs([bound(Index,Exp,Bounded)|Auxs],Ref_set_accum,Auxs_accum,min,Ref_set,Auxs_out):-	
	from_list_sl(Bounded,Bounded_set),
	intersection_sl(Ref_set_accum,Bounded_set,Bounded),!,
	maplist(tuple,Names,_,Index),
	from_list_sl(Names,Names_set),
	union_sl(Names_set,Ref_set_accum,Ref_set_accum2),
	remove_useless_aux_constrs(Auxs,Ref_set_accum2,[bound(Index,Exp,Bounded)|Auxs_accum],min,Ref_set,Auxs_out).
	
remove_useless_aux_constrs([_|Auxs],Ref_set_accum,Auxs_accum,min,Ref_set,Auxs_out):-	
	remove_useless_aux_constrs(Auxs,Ref_set_accum,Auxs_accum,min,Ref_set,Auxs_out).		

useless_top_constr(Ref_set,max,bound(_,Bounded)):-
	from_list_sl(Bounded,Bounded_set),
	intersection_sl(Bounded_set,Ref_set,[]).
useless_top_constr(Ref_set,min,bound(_,Bounded)):-
	from_list_sl(Bounded,Bounded_set),
	\+intersection_sl(Bounded_set,Ref_set,Bounded_set).		

get_top_bounded([],Map,Map).
get_top_bounded([bound(Exp,Bounded)|Top_exps],Map,Map_out):-
	foldl(add_bound_to_multimap(Exp),Bounded,Map,Map_aux),
	get_top_bounded(Top_exps,Map_aux,Map_out).
	
add_bound_to_multimap(Exp,Var,Map,Map1):-
	put_mm(Map,Var,Exp,Map1).


remove_not_bounded(Aux_exps,Map,Map_out,Aux_exp_out,Removed):-
	split_bounded(Aux_exps,Map,Map_1,Bounded,Not_bounded),
	(Bounded=[]->
	  Aux_exp_out=[],
	  Removed=Not_bounded,
	  Map_out=Map_1
	;
	  remove_not_bounded(Not_bounded,Map_1,Map_out,Aux_exp_aux,Removed),
	  append(Bounded,Aux_exp_aux,Aux_exp_out)
	  ).
	  
split_bounded([],Map,Map,[],[]).
split_bounded([bound(Elems,Exp,Bounded)|Aux_exps],Map,Map_out,[bound(Elems,Exp,Bounded)|Exp_Bounded],Exp_Not_bounded):-
	maplist(tuple,Names,Vars,Elems),
	maplist(values_of_mm(Map),Names,Expressions),!,
	maplist(min_expression,Expressions,Expressions2),
	copy_term((Vars,Exp),(Vars2,Exp2)),
	cstr_get_cexpr_from_normalform(Exp2,Exp3),
	Vars2=Expressions2,
	foldl(add_bound_to_multimap(Exp3),Bounded,Map,Map_aux),
	split_bounded(Aux_exps,Map_aux,Map_out,Exp_Bounded,Exp_Not_bounded).
	

split_bounded([bound(Elems,Exp,Bounded)|Aux_exps],Map,Map_out,Exp_Bounded,[bound(Elems,Exp,Bounded)|Exp_Not_bounded]):-
	split_bounded(Aux_exps,Map,Map_out,Exp_Bounded,Exp_Not_bounded).	
	
min_expression([A],A):-!.
min_expression(A,min(A)).

cstr_get_cexpr_from_normalform(add(Summands),Exp3):-
	maplist(write_product_1,Summands,Summands2),
	write_sum(Summands2,Exp3).

write_product_1(mult(List),Product):-
	write_product(List,Product).

cstr_extend_variables_names(cost(Ub_cons,Lb_cons,Bases,Base),Prefix,cost(Ub_cons1,Lb_cons1,Bases1,Base)):-
		cstr_constrs_extend_variables_names(Ub_cons,Prefix,Ub_cons1),
		cstr_constrs_extend_variables_names(Lb_cons,Prefix,Lb_cons1),
		maplist(extend_base_name(Prefix),Bases,Bases1).
		
cstr_constrs_extend_variables_names((Top_exps,Aux_exps),Prefix,(Top_exps1,Aux_exps1)):-
	maplist(extend_top_exp_name(Prefix),Top_exps,Top_exps1),
	maplist(extend_aux_exp_name(Prefix),Aux_exps,Aux_exps1).

extend_base_name(Prefix,(Name,Value),([Prefix|Name],Value)).
extend_aux_exp_name(Prefix,bound(Elems,Expression,Bounded),bound(Elems2,Expression,Bounded2)):-
	maplist(extend_base_name(Prefix),Elems,Elems2),
	maplist(append([Prefix]),Bounded,Bounded2).
extend_top_exp_name(Prefix,bound(Expression,Bounded),bound(Expression,Bounded2)):-
	maplist(append([Prefix]),Bounded,Bounded2).	
	
cstr_shorten_variables_names(cost(Ub_cons,Lb_cons,Bases,Base),cost(Ub_cons1,Lb_cons1,Bases1,Base)):-
		cstr_constrs_shorten_variables_names(Ub_cons,Ub_cons1),
		cstr_constrs_shorten_variables_names(Lb_cons,Lb_cons1),
		maplist(shorten_base_name,Bases,Bases1).
		
cstr_constrs_shorten_variables_names((Top_exps,Aux_exps),(Top_exps1,Aux_exps1)):-
	maplist(shorten_top_exp_name,Top_exps,Top_exps1),
	maplist(shorten_aux_exp_name,Aux_exps,Aux_exps1).
		
shorten_base_name((Name,Value),(Short_name,Value)):-
	shorten_name(Name,Short_name).
shorten_aux_exp_name(bound(Elems,Expression,Bounded),bound(Elems2,Expression,Bounded2)):-
	maplist(shorten_base_name,Elems,Elems2),
	maplist(shorten_name,Bounded,Bounded2).
	
shorten_top_exp_name(bound(Expression,Bounded),bound(Expression,Bounded2)):-
	maplist(shorten_name,Bounded,Bounded2).	


shorten_name(Name,Short_name):-
	term_hash(Name,Hash),
	(short_db(Hash,Name,Short_name)->
		true
		;
	 	counter_increase(short_terms,1,Id),
	 	assert(short_db(Hash,Name,[s(Id)])),
	 	Short_name=[s(Id)]
	 	).
	 	
cstr_join(cost((T,A),(LT,LA),Bs,B),cost((T2,A2),(LT2,LA2),B2s,B2),cost((T3,A3),(LT3,LA3),B3s,B3)):-
	append(T,T2,T3),
	append(A,A2,A3),
	append(LT,LT2,LT3),
	append(LA,LA2,LA3),
	append(Bs,B2s,B3s),
	B3=B+B2.	 	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cstr_propagate_summatory(Loop,cost(Ub_cons,Lb_cons,Bases,Base),cost(Ub_cons2,Lb_cons2,[([it(Loop)],Base)|Bases1],0),(Ub_Summatories,Lb_Summatories)):-
	generate_initial_sum_map(Bases,[],Sum_map_initial,Bases1),
	cstr_constrs_propagate_summatory(Ub_cons,Sum_map_initial,Ub_cons2,Ub_Summatories),
	cstr_constrs_propagate_summatory(Lb_cons,Sum_map_initial,Lb_cons2,Lb_Summatories).
	
	
cstr_constrs_propagate_summatory((Top,Aux),Sum_map_initial,(Top2,Aux2),Summatories):-	
	propagate_sum_aux_backwards(Aux,Sum_map_initial,Aux2,Sum_map,Max_map),
	get_maxs(Top,Max_map,Top2),
	get_summatories(Top,Sum_map,Summatories).
	
get_maxs([],_,[]).
get_maxs([bound(Exp,Bounded)|Tops],Max_set,Tops2):-
	include(contains_sl(Max_set),Bounded,Non_summatories),
	(Non_summatories\=[]->
		Tops2=[bound(Exp,Non_summatories)|Tops1]
		;
		Tops2=Tops1
		),
	get_maxs(Tops,Max_set,Tops1).
	
get_summatories([],_,[]).
get_summatories([bound(Exp,Bounded)|Tops],Sum_map,Tops2):-
	get_mapped(Bounded,Sum_map,New_names),
	(New_names\=[]->
		Tops2=[bound(Exp,New_names)|Tops1]
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
propagate_sum_aux_backwards([bound(Index,Expr,Bounded)|Aux_ini],Sum_map_initial,Aux3,Sum_map2,Max_map3):-	
	propagate_sum_aux_backwards(Aux_ini,Sum_map_initial,Aux,Sum_map,Max_map),
	get_mapped(Bounded,Sum_map,New_names),
	include(contains_sl(Max_map),Bounded,Non_summatories),
	(Non_summatories\=[]->
		Aux2=[bound(Index,Expr,Non_summatories)|Aux],
		foldl(add_indexes_to_set,Index,Max_map,Max_map2)
	;
	  Aux2=Aux,
	  Max_map2=Max_map
	),
	(New_names\=[]->

	%this means some are multiplied (the new names can be the same as the old if they did not coicide
	update_max_set(Index,Expr,Index_max,Max_map2,Max_map3),
	update_sum_map(Index,Expr,Index_sum,Max_map3,Sum_map,Sum_map2),
	append(Index_max,Index_sum,Index_final),
	Aux3=[bound(Index_final,Expr,New_names)|Aux2]
	;
	Aux3=Aux2,
	Sum_map2=Sum_map,
	Max_map3=Max_map2
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