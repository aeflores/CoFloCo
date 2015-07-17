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
		naive_maximization/2,
		name_aux_var/1,
		get_cost_exp_from_normal_form/2,
		remove_cycles_in_cost/2,
		 extend_variables_names/3,
		 shorten_variables_names/2]).
:- use_module(cofloco_utils,[write_sum/2,write_product/2,tuple/3]).	
:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(multimap),[put_mm/4,values_of_mm/3]).	



:-dynamic short_db/3.

name_aux_var([aux(Num)]):-
	counter_increase(aux_vars,1,Num).

%naive_maximization(cost(Top_exps,Aux_exps,Bases,Base),Cost):-
naive_maximization(Cost_long,Cost):-
	shorten_variables_names(Cost_long,cost(Top_exps,Aux_exps,Bases,Base)),	
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
	
remove_cycles_in_cost(cost(Top_exps,Aux_exps,Bases,Base),Short):-
	get_top_bounded(Top_exps,[],Map_bounded),
	remove_not_bounded(Aux_exps,Map_bounded,_Map_final,Aux_exps2,_Removed),
	shorten_variables_names(cost(Top_exps,Aux_exps2,Bases,Base),Short).

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
	get_cost_exp_from_normal_form(Exp2,Exp3),
	Vars2=Expressions2,
	foldl(add_bound_to_multimap(Exp3),Bounded,Map,Map_aux),
	split_bounded(Aux_exps,Map_aux,Map_out,Exp_Bounded,Exp_Not_bounded).
	

split_bounded([ub(Elems,Exp,Bounded)|Aux_exps],Map,Map_out,Exp_Bounded,[ub(Elems,Exp,Bounded)|Exp_Not_bounded]):-
	split_bounded(Aux_exps,Map,Map_out,Exp_Bounded,Exp_Not_bounded).	
	
min_expression([A],A):-!.
min_expression(A,min(A)).

get_cost_exp_from_normal_form(add(Summands),Exp3):-
	maplist(write_product_1,Summands,Summands2),
	write_sum(Summands2,Exp3).

write_product_1(mult(List),Product):-
	write_product(List,Product).

extend_variables_names(cost(Top_exps,Aux_exps,Bases,Base),Prefix,cost(Top_exps1,Aux_exps1,Bases1,Base)):-
		maplist(extend_top_exp_name(Prefix),Top_exps,Top_exps1),
		maplist(extend_aux_exp_name(Prefix),Aux_exps,Aux_exps1),
		maplist(extend_base_name(Prefix),Bases,Bases1).

extend_base_name(Prefix,(Name,Value),([Prefix|Name],Value)).
extend_aux_exp_name(Prefix,ub(Elems,Expression,Bounded),ub(Elems2,Expression,Bounded2)):-
	maplist(extend_base_name(Prefix),Elems,Elems2),
	maplist(append([Prefix]),Bounded,Bounded2).
extend_top_exp_name(Prefix,ub(Expression,Bounded),ub(Expression,Bounded2)):-
	maplist(append([Prefix]),Bounded,Bounded2).	
	
shorten_variables_names(cost(Top_exps,Aux_exps,Bases,Base),cost(Top_exps1,Aux_exps1,Bases1,Base)):-
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