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
		cstr_or_compress/2,
		cstr_get_lin_exp_from_tops/3,
		cstr_join_equal_top_expressions/2,
		cstr_remove_useless_constrs_max_min/3,
		cstr_shorten_variables_names/3]).
:- use_module(cofloco_utils,[is_rational/1,sort_with/3,write_sum/2,write_product/2,tuple/3,assign_right_vars/3]).	
:- use_module(cost_expressions,[cexpr_simplify/3,is_linear_exp/1]).	

:- use_module('../IO/params',[get_param/2]).
:- use_module('../IO/output',[print_aux_exp/1]).	
:- use_module('../bound_computation/cost_structure_solver',[cstr_maxminimization/5]).

:- use_module(stdlib(linear_expression),[parse_le/2,write_le/2,negate_le/2]).	
:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4,ut_sort/2,ut_var_member/2]).	
:- use_module(stdlib(multimap),[put_mm/4,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).
:- use_module(stdlib(fraction)).
:- use_module(stdlib(set_list),[difference_sl/3,contains_sl/2,from_list_sl/2,unions_sl/2,union_sl/3,insert_sl/3,intersection_sl/3]).

:-dynamic short_db/3.

%FIXME 
% creates inefficient structures
% when the cost is a constant, the auxiliary expressions are not well propagated
cstr_or_compress([Cost],Cost):-!.

cstr_or_compress(Costs,Cost_final):-
	\+get_param(compute_lbs,[]),!,
	from_list_sl(Costs,Costs_set),
	get_cstr_components(Costs_set,Tops_list,_,Auxs_list,Elems_list,Bases),
	ut_flat_list(Tops_list,Tops_flat),
	ut_flat_list(Auxs_list,Auxs_flat),
	ut_flat_list(Elems_list,Elems_flat),
	max_list(Bases,Base),
	(maplist(is_constant_constraint,Tops_flat)->
	    cstr_maxminimization(cost(Tops_flat,[],Auxs_flat,Elems_flat,Base),max,none,[],New_base),
	    cexpr_simplify(New_base,[],New_base_simpl),
	    (is_rational(New_base_simpl)->
	        Cost_final=cost([],[],[],[],New_base_simpl)
	        ;
	        cstr_name_aux_var(Name),
	        Cost_final=cost([],[],[],[(Name,1)],0)
	        )
	;
	 cstr_join_equal_top_expressions(cost(Tops_flat,[],Auxs_flat,Elems_flat,Base),Cost_final)
	 ).



cstr_or_compress(Costs,Cost_final):-
	from_list_sl(Costs,Costs_set),
	get_cstr_components(Costs_set,Tops_list,Tops_min_list,Auxs_list,Elems_list,Bases),
	maplist(get_aux_expr_from_base,Elems_list,Bases,Pos_extra,Neg_extra),
	ut_flat_list(Pos_extra,Pos_extra_flat),
	ut_flat_list(Neg_extra,Neg_extra_flat),
	maplist(tuple,Pos_extra_ub,Pos_extra_lb,Pos_extra_flat),
	maplist(tuple,Neg_extra_ub,Neg_extra_lb,Neg_extra_flat),
	maplist(get_aux_expr_bounded,Pos_extra_ub,Bounded_pos),
	maplist(get_aux_expr_bounded,Neg_extra_ub,Bounded_neg),
	foldl(append,Bounded_pos,[],Bounded_pos_flat),
	foldl(append,Bounded_neg,[],Bounded_neg_flat),
	get_disjunction_aux(Bounded_pos_flat,Pos_disjunct_auxs,Pos_disjunct_tops),
	get_disjunction_aux(Bounded_neg_flat,Neg_disjunct_auxs,Neg_disjunct_tops),
	(Pos_disjunct_auxs=[bound(_,_,[Bounded_pos_final])|_]->
	    Elems=[(Bounded_pos_final,1)]
	    ;
	    Elems=[]
	 ),
	(Neg_disjunct_auxs=[bound(_,_,[Bounded_neg_final])|_]->
		Elems1=[(Bounded_neg_final,1)|Elems]
	    ;
	    Elems1=Elems
	),
	

	ut_flat_list([Pos_extra_ub,Pos_extra_lb,Neg_extra_ub,Neg_extra_lb],Extra_total),
	partition(is_aux_exp,Extra_total,Aux_extra,Top_extra),
	ut_flat_list([Top_extra,Pos_disjunct_tops,Tops_list,Neg_disjunct_tops,Tops_min_list],Tops_all),
	partition(is_ub_bound,Tops_all,Tops,Tops_min),
	ut_flat_list([Auxs_list,Aux_extra,Pos_disjunct_auxs,Neg_disjunct_auxs],Auxs),
	cstr_join_equal_top_expressions(cost(Tops,Tops_min,Auxs,Elems1,0),Cost_final).


is_constant_constraint(bound(_Op,[]+_Cnt,_Bounded)).	
is_aux_exp(bound(_,exp(_,_,_,_),_)).
is_ub_bound(bound(ub,_,_)).

get_aux_expr_bounded(bound(_,_,Bounded),Bounded).

get_disjunction_aux([],[],[]):-!.

get_disjunction_aux(Vars,[Ub_disjunct_aux,Lb_disjunct_aux],[Ub_disjunct_top,Lb_disjunct_top]):-
	get_summand_multiplied(Vars,Index_pos,Summands,New_vars),
	Internal_exp=exp(Index_pos,[],add(Summands),add([])),
	copy_term(Internal_exp,Internal_exp2),
	cstr_name_aux_var(Aux_var),
	Ub_disjunct_aux=bound(ub,Internal_exp,[Aux_var]),
	Lb_disjunct_aux=bound(lb,Internal_exp2,[Aux_var]),
	Ub_disjunct_top=bound(ub,[]+1,New_vars),
	Lb_disjunct_top=bound(lb,[]+1,New_vars).

get_summand_multiplied([],[],[],[]).
get_summand_multiplied([Name|Names],[(Name,Var1),(Name_new,Var2)|Index_rest],[mult([Var1,Var2])|Summands],[Name_new|Names_new]):-
	cstr_name_aux_var(Name_new),
	get_summand_multiplied(Names,Index_rest,Summands,Names_new).
	

get_cstr_components([],[],[],[],[],[]).
get_cstr_components([cost(Tops,Tops_min,Auxs,Elems,Base)|Rest],[Tops|Tops_rest],[Tops_min|Tops_min_rest],[Auxs|Auxs_rest],[Elems|Elems_res],[Base|Base_rest]):-
	get_cstr_components(Rest,Tops_rest,Tops_min_rest,Auxs_rest,Elems_res,Base_rest).
	

get_aux_expr_from_base([],Base,Pos_aux,Neg_aux):-!,
	(greater_fr(Base,0)->
	    cstr_name_aux_var(Aux_var_pos),
	    Pos_aux=(bound(ub,[]+Base,[Aux_var_pos]),
	             bound(lb,[]+Base,[Aux_var_pos])),
	     Neg_aux=[]

	 ;
	  negate_fr(Base,Base_neg),
	  cstr_name_aux_var(Aux_var_pos),
	    Neg_aux=(bound(ub,[]+Base_neg,[Aux_var_pos]),
	             bound(lb,[]+Base_neg,[Aux_var_pos])),
	     Pos_aux=[]
	  
	).

get_aux_expr_from_base(Elems,Base,Pos_aux,Neg_aux):-
	generate_summands_from_bases(Elems,Index_pos,Index_neg,Summands_pos,Summands_neg),
	(greater_fr(Base,0)->
	    Summands_pos1=[mult([Base])|Summands_pos],
	    Summands_neg1=Summands_neg
	 ;
	  	negate_fr(Base,Base_neg),
	  	Summands_pos1=Summands_pos,
	    Summands_neg1=[mult([Base_neg])|Summands_neg]
	),
	(Summands_pos1\=[]->
	cstr_name_aux_var(Aux_var_pos),
	   Pos_aux=(bound(ub,exp(Index_pos,[],add(Summands_pos1),add([])),[Aux_var_pos]),
	   	        bound(lb,exp(Index_pos,[],add(Summands_pos1),add([])),[Aux_var_pos]))
	   ;
	   Pos_aux=[]
	   ),
	(Summands_neg1\=[]->
	cstr_name_aux_var(Aux_var_neg),
	   Neg_aux=(bound(ub,exp(Index_neg,[],add(Summands_neg1),add([])),[Aux_var_neg]),
	            bound(lb,exp(Index_neg,[],add(Summands_neg1),add([])),[Aux_var_neg]))
	   ;
	   Neg_aux=[]
	   ).
	
generate_summands_from_bases([],[],[],[],[]).
generate_summands_from_bases([(Name,1)|Bases],[(Name,Var)|Index_pos],Index_neg,[mult([Var])|Summands_pos],Summands_neg):-!,
	generate_summands_from_bases(Bases,Index_pos,Index_neg,Summands_pos,Summands_neg).
	
generate_summands_from_bases([(Name,Coeff)|Bases],[(Name,Var)|Index_pos],Index_neg,[mult([Var,Coeff])|Summands_pos],Summands_neg):-
	geq_fr(Coeff,0),!,
	generate_summands_from_bases(Bases,Index_pos,Index_neg,Summands_pos,Summands_neg).
generate_summands_from_bases([(Name,Coeff)|Bases],Index_pos,[(Name,Var)|Index_neg],Summands_pos,[mult([Var,Coeff_neg])|Summands_neg]):-
	negate_fr(Coeff,Coeff_neg),
	generate_summands_from_bases(Bases,Index_pos,Index_neg,Summands_pos,Summands_neg).
		
	
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
	
cstr_propagate_zeroes(cost(Ub_tops,Lb_tops,Aux_exps,Bases,Base),Simplified):-
	partition(negative_top,Ub_tops,Removed_ub_tops,Ub_tops1),
	exclude(negative_top,Lb_tops,Lb_tops1),	
	(Removed_ub_tops\=[]->
	foldl(create_zero_set,Removed_ub_tops,[],Zero_set),
	propagate_zeroes(Aux_exps,Zero_set,Aux_exps2,Zero_set2),
	exclude(pair_contains_first(Zero_set2),Bases,Bases1)
	;
	 Aux_exps2=Aux_exps,
	 Bases1=Bases
	),
	cstr_remove_useless_constrs(cost(Ub_tops1,Lb_tops1,Aux_exps2,Bases1,Base),Simplified).
	
negative_top(bound(_,[]+N,_Bounded)):-
		leq_fr(N,0).
	
create_zero_set(bound(_,_,Bounded),Set,Set1):-
	from_list_sl(Bounded,Bounded_set),
	union_sl(Bounded_set,Set,Set1).



propagate_zeroes([],Set,[],Set).
propagate_zeroes([bound(Op,Exp,Bounded)|Auxs],Set,Auxs_out,Set_out):-
	Exp=exp(Index_pos,Index_neg,Pos,Neg),
	partition(pair_contains_first(Set),Index_pos,Index_zero,Index_pos1),
	Index_zero\=[],!,
	maplist(set_second_to(0),Index_zero),
	simplify_add(Pos,Pos1),
	(Pos1=add([])->
	   Auxs_out=Auxs_out1,
	   from_list_sl(Bounded,Bounded_set),
	   union_sl(Bounded_set,Set,Set1)
	   ;
	   Exp1=exp(Index_pos1,Index_neg,Pos1,Neg),
	   Auxs_out=[bound(Op,Exp1,Bounded)|Auxs_out1],
	   Set1=Set
	),
	propagate_zeroes(Auxs,Set1,Auxs_out1,Set_out).
	
propagate_zeroes([bound(Op,Exp,Bounded)|Auxs],Set,[bound(Op,Exp,Bounded)|Auxs_out],Set_out):-
	propagate_zeroes(Auxs,Set,Auxs_out,Set_out).	  
	 
set_second_to(X,(_,X)).
simplify_add(add(Summands),add(Summands1)):-
    exclude(zero_summand,Summands,Summands1).
   
zero_summand(mult(Factors)):-
	member(F,Factors),
	F==0,!.	
	
cstr_remove_cycles(cost(Ub_tops,Lb_tops,Aux_exps,Bases,Base),Short):-
	get_top_bounded(Ub_tops,[],Ub_Bounded_set),
	get_top_bounded(Lb_tops,[],Lb_Bounded_set),
	remove_not_bounded(Aux_exps,Ub_Bounded_set,Lb_Bounded_set,Aux_exps2),
	cstr_propagate_zeroes(cost(Ub_tops,Lb_tops,Aux_exps2,Bases,Base),Simplified),
	%cstr_remove_useless_constrs(cost(Ub_tops,Lb_tops,Aux_exps2,Bases,Base),Simplified),
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
	  %(Not_bounded\=[]->trace,maplist(print_aux_exp,Not_bounded);true)
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

pair_contains_first(Set,(F,_)):-
	contains_sl(Set,F).	
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