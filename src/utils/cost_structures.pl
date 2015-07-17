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
		cstr_naive_maximization/2,
		cstr_name_aux_var/1,
		cstr_get_it_name/2,
		cstr_generate_top_exp/3,
		cstr_get_cexpr_from_normalform/2,
		cstr_remove_cycles/2,
		cstr_extend_variables_names/3,
		cstr_propagate_summatory/4,
		cstr_join/3,
		cstr_shorten_variables_names/2]).
:- use_module(cofloco_utils,[write_sum/2,write_product/2,tuple/3]).	
:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(multimap),[put_mm/4,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).
:- use_module(stdlib(set_list),[contains_sl/2,from_list_sl/2,unions_sl/2,union_sl/3]).

:-dynamic short_db/3.

cstr_name_aux_var([aux(Num)]):-
	counter_increase(aux_vars,1,Num).

cstr_get_it_name(Loop,[it(Loop)]).
cstr_generate_top_exp(Bounded,Max,ub(Max,Bounded)).

%cstr_naive_maximization(cost(Top_exps,Aux_exps,Bases,Base),Cost):-
cstr_naive_maximization(Cost_long,Cost):-
	cstr_shorten_variables_names(Cost_long,cost(Top_exps,Aux_exps,Bases,Base)),	
	get_top_bounded(Top_exps,[],Map_bounded),
	remove_not_bounded(Aux_exps,Map_bounded,Map_final,_Aux_exps2,_Removed),
	maplist(substitute_base(Map_final),Bases,Concrete_bases),
	write_sum([Base|Concrete_bases],Cost).
	
substitute_base(_Map,(_Name,0),0):-!.

substitute_base(Map,(Name,Val),Concrete):-
	values_of_mm(Map,Name,Values),!,
	(Values=[One]->
		Concrete=Val*One
		;
		Concrete=min(Values)*Val
		).
substitute_base(_Map,(_Name,_Val),inf).	
	
cstr_remove_cycles(cost(Top_exps,Aux_exps,Bases,Base),Short):-
	get_top_bounded(Top_exps,[],Map_bounded),
	remove_not_bounded(Aux_exps,Map_bounded,_Map_final,Aux_exps2,_Removed),
	cstr_shorten_variables_names(cost(Top_exps,Aux_exps2,Bases,Base),Short).

get_top_bounded([],Map,Map).
get_top_bounded([ub(Exp,Bounded)|Top_exps],Map,Map_out):-
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
split_bounded([ub(Elems,Exp,Bounded)|Aux_exps],Map,Map_out,[ub(Elems,Exp,Bounded)|Exp_Bounded],Exp_Not_bounded):-
	maplist(tuple,Names,Vars,Elems),
	maplist(values_of_mm(Map),Names,Expressions),!,
	maplist(min_expression,Expressions,Expressions2),
	copy_term((Vars,Exp),(Vars2,Exp2)),
	cstr_get_cexpr_from_normalform(Exp2,Exp3),
	Vars2=Expressions2,
	foldl(add_bound_to_multimap(Exp3),Bounded,Map,Map_aux),
	split_bounded(Aux_exps,Map_aux,Map_out,Exp_Bounded,Exp_Not_bounded).
	

split_bounded([ub(Elems,Exp,Bounded)|Aux_exps],Map,Map_out,Exp_Bounded,[ub(Elems,Exp,Bounded)|Exp_Not_bounded]):-
	split_bounded(Aux_exps,Map,Map_out,Exp_Bounded,Exp_Not_bounded).	
	
min_expression([A],A):-!.
min_expression(A,min(A)).

cstr_get_cexpr_from_normalform(add(Summands),Exp3):-
	maplist(write_product_1,Summands,Summands2),
	write_sum(Summands2,Exp3).

write_product_1(mult(List),Product):-
	write_product(List,Product).

cstr_extend_variables_names(cost(Top_exps,Aux_exps,Bases,Base),Prefix,cost(Top_exps1,Aux_exps1,Bases1,Base)):-
		maplist(extend_top_exp_name(Prefix),Top_exps,Top_exps1),
		maplist(extend_aux_exp_name(Prefix),Aux_exps,Aux_exps1),
		maplist(extend_base_name(Prefix),Bases,Bases1).

extend_base_name(Prefix,(Name,Value),([Prefix|Name],Value)).
extend_aux_exp_name(Prefix,ub(Elems,Expression,Bounded),ub(Elems2,Expression,Bounded2)):-
	maplist(extend_base_name(Prefix),Elems,Elems2),
	maplist(append([Prefix]),Bounded,Bounded2).
extend_top_exp_name(Prefix,ub(Expression,Bounded),ub(Expression,Bounded2)):-
	maplist(append([Prefix]),Bounded,Bounded2).	
	
cstr_shorten_variables_names(cost(Top_exps,Aux_exps,Bases,Base),cost(Top_exps1,Aux_exps1,Bases1,Base)):-
		maplist(shorten_top_exp_name,Top_exps,Top_exps1),
		maplist(shorten_aux_exp_name,Aux_exps,Aux_exps1),
		maplist(shorten_base_name,Bases,Bases1).
		
shorten_base_name((Name,Value),(Short_name,Value)):-
	shorten_name(Name,Short_name).
shorten_aux_exp_name(ub(Elems,Expression,Bounded),ub(Elems2,Expression,Bounded2)):-
	maplist(shorten_base_name,Elems,Elems2),
	maplist(shorten_name,Bounded,Bounded2).
	
shorten_top_exp_name(ub(Expression,Bounded),ub(Expression,Bounded2)):-
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
	 	
cstr_join(cost(T,A,Bs,B),cost(T2,A2,B2s,B2),cost(T3,A3,B3s,B3)):-
	append(T,T2,T3),
	append(A,A2,A3),
	append(Bs,B2s,B3s),
	B3=B+B2.	 	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cstr_propagate_summatory(Loop,cost(Top,Aux,Bases,Base),cost(Top2,Aux2,[([it(Loop)],Base)|Bases1],0),Summatories):-
	generate_initial_sum_map(Bases,[],Sum_map_initial,Bases1),
	propagate_sum_aux_backwards(Aux,Sum_map_initial,Aux2,Sum_map,Max_map),
	get_maxs(Top,Max_map,Top2),
	get_summatories(Top,Sum_map,Summatories).
	
get_maxs([],_,[]).
get_maxs([ub(Exp,Bounded)|Tops],Max_set,Tops2):-
	include(contains_sl(Max_set),Bounded,Non_summatories),
	(Non_summatories\=[]->
		Tops2=[ub(Exp,Non_summatories)|Tops1]
		;
		Tops2=Tops1
		),
	get_maxs(Tops,Max_set,Tops1).
	
get_summatories([],_,[]).
get_summatories([ub(Exp,Bounded)|Tops],Sum_map,Tops2):-
	get_mapped(Bounded,Sum_map,New_names),
	(New_names\=[]->
		Tops2=[ub(Exp,New_names)|Tops1]
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
propagate_sum_aux_backwards([ub(Index,Expr,Bounded)|Aux_ini],Sum_map_initial,Aux3,Sum_map2,Max_map3):-	
	propagate_sum_aux_backwards(Aux_ini,Sum_map_initial,Aux,Sum_map,Max_map),
	get_mapped(Bounded,Sum_map,New_names),
	include(contains_sl(Max_map),Bounded,Non_summatories),
	(Non_summatories\=[]->
		Aux2=[ub(Index,Expr,Non_summatories)|Aux],
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
	Aux3=[ub(Index_final,Expr,New_names)|Aux2]
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