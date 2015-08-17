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
		cstr_from_cexpr/2,
		cstr_maxminimization/4,
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
		cstr_shorten_variables_names/2]).
:- use_module(cofloco_utils,[write_sum/2,write_product/2,tuple/3,assign_right_vars/3]).	
:- use_module(cost_expressions,[cexpr_simplify/3,is_linear_exp/1,normalize_le/2]).	

:- use_module(stdlib(linear_expression),[parse_le/2,write_le/2,negate_le/2]).	
:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).	
:- use_module(stdlib(multimap),[put_mm/4,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).
:- use_module(stdlib(fraction),[greater_fr/2,sum_fr/3]).
:- use_module(stdlib(set_list),[contains_sl/2,from_list_sl/2,unions_sl/2,union_sl/3,insert_sl/3,intersection_sl/3]).

:-dynamic short_db/3.

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
	cstr_shorten_variables_names(Simplified,Short).


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
	
:-dynamic maximization_mode/1.		
	
cstr_maxminimization(Cost_long,Max_min,Bound,Mode):-
	retractall(maximization_mode(_)),assert(maximization_mode(Mode)),
	cstr_shorten_variables_names(Cost_long,Cost_short),	
	cstr_remove_useless_constrs_max_min(Cost_short,Max_min,cost(Ub_tops,Lb_tops,Aux_exps,Bases,Base)),
	term_variables((Ub_tops,Lb_tops),Vars),
	findall((Vars,Max_Min_case),
		(
		get_top_bounded_map(Ub_tops,[],extra_elems(Aux_exps,Max_min,Bases),Ub_map,extra_elems(Aux_exps2,Max_min,Bases1)),
		get_top_bounded_map(Lb_tops,[],nothing,Lb_map,_),
		%remove_zero_constraints(Aux_exps,Max_min,Ub_map,Bases,Ub_map2,Aux_exps2,Bases1),	
		get_aux_bounded_map(Aux_exps2,Bases1,Ub_map,Lb_map,Ub_map_final,Lb_map_final,Bases2),	
		maplist(substitute_base(Ub_map_final,Lb_map_final,Max_min),Bases2,Concrete_bases_max_min),
		write_sum([Base|Concrete_bases_max_min],Max_Min_case)
		)
		,Maxs_Mins_list),
	assign_right_vars(Maxs_Mins_list,Vars,Maxs_Mins_right),
	zip_with(Max_min,Maxs_Mins_right,Bound).

remove_zero_constraints(Aux_exps,Max_min,Ub_map,Bases,Ub_map2,Aux_exps2,Bases2,Ref_set3):-
	get_zero_bounded(Ub_map,Zeroes),
	propagate_zeroes(Aux_exps,Zeroes,Aux_exps1,Zeroes2),
	foldl(add_bound_to_multimap(0),Zeroes2,Ub_map,Ub_map2),
	exclude(zero_base(Zeroes2),Bases,Bases1),
	foldl(compute_initial_reference_set(Max_min),Bases1,([],[]),(Bases2,Ref_set1)),
	reverse(Aux_exps1,Aux_exps_rev),
	remove_useless_aux_constrs(Aux_exps_rev,Ref_set1,[],Ref_set3,Aux_exps2),!.

zero_base(Zeroes,(Name,_)):-
	contains_sl(Zeroes,Name).
	
get_zero_bounded([],[]).
get_zero_bounded([(Name,Set)|More],[Name|More_set]):-
	contains_sl(Set,0),!,
	get_zero_bounded(More,More_set).
get_zero_bounded([_|More],More_set):-
	get_zero_bounded(More,More_set).	

propagate_zeroes([],Zeroes_out,[],Zeroes_out).
	
propagate_zeroes([bound(ub,Exp,Bounded)|More],Zeroes,Aux_exps_out,Zeroes_out):-
	is_made_zero(Exp,Zeroes,exp(Index_pos,Index_neg,add(Factors_rem),Exp_neg)),
	(Factors_rem=[]->
	from_list_sl(Bounded,Bounded_set),
	union_sl(Zeroes,Bounded_set,Zeroes1),
	propagate_zeroes(More,Zeroes1,Aux_exps_out,Zeroes_out)
	;
	Aux_exps_out=[bound(ub,exp(Index_pos,Index_neg,add(Factors_rem),Exp_neg),Bounded)|Aux_exps_out_aux],
	propagate_zeroes(More,Zeroes,Aux_exps_out_aux,Zeroes_out)
	).
propagate_zeroes([bound(lb,Exp,Bounded)|More],Zeroes,[bound(lb,Exp,Bounded)|Aux_exps_out_aux],Zeroes_out):-
	propagate_zeroes(More,Zeroes,Aux_exps_out_aux,Zeroes_out).	
	
%%propagate_zeroes([bound(Op,Exp,Bounded)|More],Zeroes,[bound(Op,Exp,Bounded)|Aux_exps_out],Zeroes_out):-
%	propagate_zeroes(More,Zeroes,Aux_exps_out,Zeroes_out).
	
is_made_zero(exp(Index_pos,Index_neg,add(Factors),Exp_neg),Zeroes,exp(Index_pos1,Index_neg,add(Factors_rem),Exp_neg)):-
	copy_term((Index_pos,Factors),(Index_pos2,Factors2)),
	maplist(set_to_zero_one(Zeroes),Index_pos2),
	exclude_zero_factor(Factors,Factors2,Factors_rem),
	term_variables(Factors_rem,Vars),from_list_sl(Vars,Vars_set),
	include(index_contains(Vars_set),Index_pos,Index_pos1).

index_contains(Set,(_,Var)):-
	contains_sl(Set,Var).
exclude_zero_factor([],[],[]).
exclude_zero_factor([mult(_F)|More],[mult(F2)|More2],More_out):-
	member(0,F2),!,
	exclude_zero_factor(More,More2,More_out).
exclude_zero_factor([mult(F)|More],[_|More2],[mult(F)|More_out]):-
	exclude_zero_factor(More,More2,More_out).	
	
zero_factor(mult(List)):-	
	member(0,List),!.
	
set_to_zero_one(Zeroes,(Name,0)):-
	contains_sl(Zeroes,Name),!.
set_to_zero_one(_,(_Name,1)).
	
	
substitute_base(Ub_Map,Lb_Map,Max_min,(Name,Val),Concrete):-
	(greater_fr(Val,0)->
	 	(Max_min=max->
	 		lookup_lm(Ub_Map,Name,Values),
	 		Op=min
	 		;
	 		lookup_lm(Lb_Map,Name,Values),
	 		Op=max
	 	)
	 	;
	 	(Max_min=max->
	 		lookup_lm(Lb_Map,Name,Values),
	 		Op=max
	 		;
	 		lookup_lm(Ub_Map,Name,Values),
	 		Op=min
	 	)
	 ),!,
	(Values=[One]->
		(One==0->
		  Concrete=0
		  ;
		Concrete=Val*nat(One)
		)
		;
		Concrete_aux=..[Op,Values],
		Concrete=Val*nat(Concrete_aux)
		).

substitute_base(_,_,Max_min,(_Name,Val),Res):-
	(greater_fr(Val,0)->
	 	(Max_min=max->
	 		Res=inf
	 		;
	 		Res=0
	 	)
	 	;
	 	(Max_min=max->
	 		Res=0
	 		;
	 		Res=0
	 	)
	 ),!.


get_top_bounded_map([],Map,Extra_elems,Map,Extra_elems).


%FIXME we have to be careful with bad behaved sets of constraints
get_top_bounded_map([bound(ub,Lin_exp,Bounded)|Top_exps],Map,Extra_elems,Map_out,Extra_elems_out):-
	maximization_mode(simple),
	write_le(Lin_exp,Exp),
	foldl(add_bound_to_multimap(Exp),Bounded,Map,Map_aux1),
	get_top_bounded_map(Top_exps,Map_aux1,Extra_elems,Map_out,Extra_elems_out).

get_top_bounded_map([bound(ub,Lin_exp,Bounded)|Top_exps],Map,extra_elems(Aux_exps,Max_min,Bases),Map_out,Extra_elems_out):-
	\+maximization_mode(simple),
	write_le(Lin_exp,Exp),
	exclude(already_bounded(Map),Bounded,Bounded_new),
	(Bounded_new\=[]->
		member(Bounded1,Bounded_new),
		delete(Bounded_new,Bounded1,Bounded2),
		foldl(add_bound_to_multimap(Exp),[Bounded1],Map,Map_aux1),
		foldl(add_bound_to_multimap(0),Bounded2,Map_aux1,Map_aux2),
		
		remove_zero_constraints(Aux_exps,Max_min,Map_aux2,Bases,Map_aux3,Aux_exps2,Bases2,Ref_set),	
		exclude(useless_top_constr(Ref_set),Top_exps,Top_exps2),
		get_top_bounded_map(Top_exps2,Map_aux3,extra_elems(Aux_exps2,Max_min,Bases2),Map_out,Extra_elems_out)
	;
		get_top_bounded_map(Top_exps,Map,extra_elems(Aux_exps,Max_min,Bases),Map_out,Extra_elems_out)
	).
	
get_top_bounded_map([bound(lb,Lin_exp,Bounded)|Top_exps],Map,Extra_elems,Map_out,Extra_elems_out):-
	write_le(Lin_exp,Exp),
	member(Bounded1,Bounded),
	delete(Bounded,Bounded1,Bounded2),
	foldl(add_bound_to_multimap(Exp),[Bounded1],Map,Map_aux1),
	foldl(add_bound_to_multimap(0),Bounded2,Map_aux1,Map_aux2),
	get_top_bounded_map(Top_exps,Map_aux2,Extra_elems,Map_out,Extra_elems_out).
		
get_aux_bounded_map(Aux_exps,Bases,Ub_map,Lb_map,Ub_map_out,Lb_map_out,Bases_out):-
	split_bounded_map(Aux_exps,Bases,Ub_map,Lb_map,Ub_map_1,Lb_map_1,Not_bounded,Bases1),
	(Aux_exps==Not_bounded->
	  Ub_map_1=Ub_map_out,
	  Lb_map_1=Lb_map_out,
	  Bases1=Bases_out
	;
	  get_aux_bounded_map(Not_bounded,Bases1,Ub_map_1,Lb_map_1,Ub_map_out,Lb_map_out,Bases_out)
	).
	 
already_bounded(Map,Elem):-
	lookup_lm(Map,Elem,_).
		  
split_bounded_map([],Bases,Ub_map_out,Lb_map_out,Ub_map_out,Lb_map_out,[],Bases).

split_bounded_map([bound(ub,Exp,Bounded)|Aux_exps],Bases,Ub_map,Lb_map,Ub_map_out,Lb_map_out,Not_bounded,Bases_out):-
	maximization_mode(simple),
		
	Exp=exp(Index_pos,Index_neg,Exp_pos,Exp_neg),
	maplist(tuple,Names_pos,Vars_pos,Index_pos),
	maplist(tuple,Names_neg,Vars_neg,Index_neg),
	maplist(lookup_lm(Ub_map),Names_pos,Expressions_pos),
	maplist(lookup_lm(Lb_map),Names_neg,Expressions_neg),
	
	copy_term((Vars_pos,Exp_pos),(Vars_pos2,Exp_pos2)),
	copy_term((Vars_neg,Exp_neg),(Vars_neg2,Exp_neg2)),
	maplist(min_expression,Expressions_pos,Expressions_pos2),
	maplist(max_expression,Expressions_neg,Expressions_neg2),
	cstr_get_cexpr_from_normalform(Exp_pos2,Exp_pos_final),
	Vars_pos2=Expressions_pos2,
	cstr_get_cexpr_from_normalform(Exp_neg2,Exp_neg_final),
	Vars_neg2=Expressions_neg2,
	cexpr_simplify(Exp_pos_final-Exp_neg_final,[],Expr_simple),
	foldl(add_bound_to_multimap(Expr_simple),Bounded,Ub_map,Ub_map_aux2),
	split_bounded_map(Aux_exps,Bases,Ub_map_aux2,Lb_map,Ub_map_out,Lb_map_out,Not_bounded,Bases_out).	
		
split_bounded_map([bound(ub,Exp,Bounded)|Aux_exps],Bases,Ub_map,Lb_map,Ub_map_out,Lb_map_out,Not_bounded,Bases_out):-
	\+maximization_mode(simple),
%	Bounded=[_],
	exclude(already_bounded(Ub_map),Bounded,Bounded_new),
	(Bounded_new\=[]->
		Exp=exp(Index_pos,Index_neg,Exp_pos,Exp_neg),
		maplist(tuple,Names_pos,Vars_pos,Index_pos),
		maplist(tuple,Names_neg,Vars_neg,Index_neg),
		maplist(lookup_lm(Ub_map),Names_pos,Expressions_pos),
		maplist(lookup_lm(Lb_map),Names_neg,Expressions_neg),
	
		copy_term((Vars_pos,Exp_pos),(Vars_pos2,Exp_pos2)),
		copy_term((Vars_neg,Exp_neg),(Vars_neg2,Exp_neg2)),
		maplist(min_expression,Expressions_pos,Expressions_pos2),
		maplist(max_expression,Expressions_neg,Expressions_neg2),
		cstr_get_cexpr_from_normalform(Exp_pos2,Exp_pos_final),
		Vars_pos2=Expressions_pos2,
		cstr_get_cexpr_from_normalform(Exp_neg2,Exp_neg_final),
		Vars_neg2=Expressions_neg2,
		%Expr_simple=Exp_pos_final-Exp_neg_final,
		cexpr_simplify(Exp_pos_final-Exp_neg_final,[],Expr_simple),
		
		(Expr_simple==0->
			foldl(add_bound_to_multimap(0),Bounded_new,Ub_map,Ub_map_aux2)
			;
			member(Bounded1,Bounded_new),
			delete(Bounded_new,Bounded1,Bounded2),
			foldl(add_bound_to_multimap(Expr_simple),[Bounded1],Ub_map,Ub_map_aux1),
			foldl(add_bound_to_multimap(0),Bounded2,Ub_map_aux1,Ub_map_aux2)
		)
		,
%		(Bounded_new=[_,_,_|_]->
%		remove_zero_constraints(Aux_exps,max,Ub_map_aux2,Bases,Ub_map_aux3,Aux_exps2,Bases2,_Ref_set)
%		;
		Aux_exps=Aux_exps2,Bases2=Bases,Ub_map_aux3=Ub_map_aux2
%		)
	,
		split_bounded_map(Aux_exps2,Bases2,Ub_map_aux3,Lb_map,Ub_map_out,Lb_map_out,Not_bounded,Bases_out)
	;
		split_bounded_map(Aux_exps,Bases,Ub_map,Lb_map,Ub_map_out,Lb_map_out,Not_bounded,Bases_out)
	).	
		
split_bounded_map([bound(lb,Exp,Bounded)|Aux_exps],Bases,Ub_map,Lb_map,Ub_map_out,Lb_map_out,Not_bounded,Bases_out):-
	exclude(already_bounded(Lb_map),Bounded,Bounded_new),
	(Bounded_new=Bounded->
		Exp=exp(Index_pos,Index_neg,Exp_pos,Exp_neg),
		maplist(tuple,Names_pos,Vars_pos,Index_pos),
		maplist(tuple,Names_neg,Vars_neg,Index_neg),
		maplist(lookup_lm(Lb_map),Names_pos,Expressions_pos),
		maplist(lookup_lm(Ub_map),Names_neg,Expressions_neg),
	
	
		copy_term((Vars_pos,Exp_pos),(Vars_pos2,Exp_pos2)),
		copy_term((Vars_neg,Exp_neg),(Vars_neg2,Exp_neg2)),
		maplist(max_expression,Expressions_pos,Expressions_pos2),
		maplist(min_expression,Expressions_neg,Expressions_neg2),
		cstr_get_cexpr_from_normalform(Exp_pos2,Exp_pos_final),
		Vars_pos2=Expressions_pos2,
		cstr_get_cexpr_from_normalform(Exp_neg2,Exp_neg_final),
		Vars_neg2=Expressions_neg2,
		cexpr_simplify(Exp_pos_final-Exp_neg_final,[],Expr_simple),
		(Expr_simple==0->
			foldl(add_bound_to_multimap(0),Bounded_new,Lb_map,Lb_map_aux2)
			;
			member(Bounded1,Bounded_new),
			delete(Bounded_new,Bounded1,Bounded2),
			foldl(add_bound_to_multimap(Expr_simple),[Bounded1],Lb_map,Lb_map_aux1),
			foldl(add_bound_to_multimap(0),Bounded2,Lb_map_aux1,Lb_map_aux2)
		),
		split_bounded_map(Aux_exps,Bases,Ub_map,Lb_map_aux2,Ub_map_out,Lb_map_out,Not_bounded,Bases_out)
	;
		split_bounded_map(Aux_exps,Bases,Ub_map,Lb_map,Ub_map_out,Lb_map_out,Not_bounded,Bases_out)
	).

split_bounded_map([bound(ub,Exp,Bounded)|Aux_exps],Bases,Ub_map,Lb_map,Ub_map_out,Lb_map_out,[bound(ub,Exp,Bounded)|Not_bounded],Bases_out):-
	Exp=exp(Index_pos,Index_neg,_,_),
	maplist(tuple,Names,_,Index_pos),
	maplist(tuple,Names_neg,_,Index_neg),
	(
	\+maplist(lookup_lm(Ub_map),Names,_)
	;
	\+maplist(lookup_lm(Lb_map),Names_neg,_)
	),
	split_bounded_map(Aux_exps,Bases,Ub_map,Lb_map,Ub_map_out,Lb_map_out,Not_bounded,Bases_out).		

split_bounded_map([bound(lb,Exp,Bounded)|Aux_exps],Bases,Ub_map,Lb_map,Ub_map_out,Lb_map_out,[bound(lb,Exp,Bounded)|Not_bounded],Bases_out):-
	Exp=exp(Index_pos,Index_neg,_,_),
	maplist(tuple,Names,_,Index_pos),
	maplist(tuple,Names_neg,_,Index_neg),
	(
	\+maplist(lookup_lm(Lb_map),Names,_)
	;
	\+maplist(lookup_lm(Ub_map),Names_neg,_)
	),
	split_bounded_map(Aux_exps,Bases,Ub_map,Lb_map,Ub_map_out,Lb_map_out,Not_bounded,Bases_out).
	
%split_bounded_map([bound(Op,Exp,Bounded)|Aux_exps],Ub_map,Lb_map,Ub_map_out,Lb_map_out,[bound(lb,Exp,Bounded)|Not_bounded]):-
%	writeln(bound(Op,Exp,Bounded)),fail.
	
min_expression([A],nat(A)):-!.
min_expression(A,min(A2)):-
	maplist(zip_with(nat),A,A2).
max_expression([A],nat(A)):-!.
max_expression(A,max([0|A])).


add_bound_to_multimap(Exp,Var,Map,Map1):-
	lookup_lm(Map,Var,Vals),!,
	insert_sl(Vals,Exp,Vals2),
	(contains_sl(Vals2,0)->
		insert_lm(Map,Var,[0],Map1)
	;
	insert_lm(Map,Var,Vals2,Map1)
	).

	
add_bound_to_multimap(Exp,Var,Map,Map1):-
	insert_lm(Map,Var,[Exp],Map1).
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
	
cstr_shorten_variables_names(cost(Ub_tops,Lb_tops,Aux_exps,Bases,Base),cost(Ub_tops1,Lb_tops1,Aux_exps1,Bases1,Base)):-
		maplist(shorten_top_exp_name,Ub_tops,Ub_tops1),
		maplist(shorten_top_exp_name,Lb_tops,Lb_tops1),
		maplist(shorten_aux_exp_name,Aux_exps,Aux_exps1),
		maplist(shorten_base_name,Bases,Bases1).
		
shorten_base_name((Name,Value),(Short_name,Value)):-
	shorten_name(Name,Short_name).
shorten_aux_exp_name(bound(Op,Expression,Bounded),bound(Op,Expression2,Bounded2)):-
	shorten_aux_exp_name_1(Expression,Expression2),
	maplist(shorten_name,Bounded,Bounded2).
	
shorten_aux_exp_name_1(exp(Index,Index_neg,Exp,Exp_neg),exp(Index2,Index_neg2,Exp,Exp_neg)):-
	maplist(shorten_base_name,Index,Index2),
	maplist(shorten_base_name,Index_neg,Index_neg2).
	
shorten_top_exp_name(bound(Op,Expression,Bounded),bound(Op,Expression,Bounded2)):-
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