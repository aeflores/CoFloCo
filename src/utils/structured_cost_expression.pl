:- module(structured_cost_expression,[
		partial_strexp_estimate_complexity/3,
		partial_strexp_complexity/2,
		str_cost_exp_complexity/2,
		strexp_to_cost_expression/2,
		strexp_simplify/2,
		strexp_get_multiplied_factors/3,
		get_all_pairs/3
	]).


:- use_module('../utils/cofloco_utils',[
		write_sum/2,
		write_product/2,
		sorted_tuple/3,
		same_var_tuple/1,
		is_rational/1]).	
		
		
:- use_module(stdlib(linear_expression),[parse_le/2,write_le/2,negate_le/2]).	
:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4,ut_sort/2,ut_var_member/2]).	
:- use_module(stdlib(multimap),[put_mm/4,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).
:- use_module(stdlib(fraction)).
:- use_module(stdlib(set_list),[difference_sl/3,contains_sl/2,from_list_sl/2,unions_sl/2,union_sl/3,insert_sl/3,intersection_sl/3]).
:-use_module(library(apply_macros)).
:-use_module(library(lists)).
partial_strexp_complexity(partial(_,_),100).
partial_strexp_complexity(Summand,N):-
	str_cost_exp_complexity(Summand,N).
	
	
partial_strexp_estimate_complexity(partial(Index,Exp),Complexity_map,Complexity):-!,
	copy_term(partial(Index,Exp),partial(Index_c,Exp_c)),
	maplist(substitute_by_dummy_complex_term(Complexity_map),Index_c),
	str_cost_exp_complexity(Exp_c,Complexity).
partial_strexp_estimate_complexity(Exp,_,Complexity):-
	str_cost_exp_complexity(Exp,Complexity).

	
	
str_cost_exp_complexity(add(Summands),N):-
	(Summands=[_|_]->
	maplist(str_cost_exp_complexity,Summands,N_list),
	max_list(N_list,N)
	;
	N=0).
str_cost_exp_complexity(mult(Factors),N1):-
	maplist(str_cost_exp_complexity,Factors,N_list),
	sum_list(N_list,N),
	((member(Neg,Factors),is_rational(Neg),greater_fr(0,Neg))->
		N1 is 0-N
		;
		N1=N
	).
		
str_cost_exp_complexity(max(Factors),N):-
	maplist(str_cost_exp_complexity,Factors,N_list),
	max_list(N_list,N).
str_cost_exp_complexity(min(Factors),N):-
	maplist(str_cost_exp_complexity,Factors,N_list),
	min_list(N_list,N).	
str_cost_exp_complexity(nat(Factor),N):-
	nonvar(Factor),
	Factor=add(_Summands),!,
	str_cost_exp_complexity(Factor,N).
str_cost_exp_complexity(nat(Factor),0):-
	ground(Factor),!.
str_cost_exp_complexity(nat(_Factor),1).
str_cost_exp_complexity(inf,100):-!.
str_cost_exp_complexity(N,0):-
	is_rational(N),!.	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

	
strexp_get_multiplied_factors(nat(add(Summands)),Vars_set,Pairs):-
	maplist(get_summand_multiplied_vars(Vars_set),Summands,Pair_list),
	unions_sl(Pair_list,Pairs).	
strexp_get_multiplied_factors(add(Summands),Vars_set,Pairs):-
	maplist(get_summand_multiplied_vars(Vars_set),Summands,Pair_list),
	unions_sl(Pair_list,Pairs).

get_summand_multiplied_vars(Vars_set,mult(Factors),Pairs_final):-
	from_list_sl(Factors,Factors_set),
	maplist(term_variables,Factors_set,Vars_lists),
	maplist(from_list_sl,Vars_lists,Vars_sets),
	maplist(intersection_sl(Vars_set),Vars_sets,Filtered_vars_sets),
	exclude(=([]),Filtered_vars_sets,Non_empty_vars_sets),
	get_all_pairs(Non_empty_vars_sets,[],Pairs),
	maplist(get_internal_pairs(Vars_set),Factors_set,Pairs_list),
	unions_sl([Pairs|Pairs_list],Pairs_final).

get_internal_pairs(_,Exp,[]):-
	var(Exp),!.	
get_internal_pairs(_,Fraction,[]):-
	is_rational(Fraction),!.
get_internal_pairs(_,inf,[]):-!.	
get_internal_pairs(_,nat(Exp),[]):-
	var(Exp),!.	
get_internal_pairs(_,nat(Exp),[]):-
	nonvar(Exp),Exp\=add(_),!.
	
get_internal_pairs(Vars_set,max(Summands),Pairs):-!,
	maplist(get_internal_pairs(Vars_set),Summands,Pair_list),
	unions_sl(Pair_list,Pairs).	
get_internal_pairs(Vars_set,min(Summands),Pairs):-!,
	maplist(get_internal_pairs(Vars_set),Summands,Pair_list),
	unions_sl(Pair_list,Pairs).		
		
get_internal_pairs(Vars_set,Factor,Pairs):-
	strexp_get_multiplied_factors(Factor,Vars_set,Pairs),!.
get_internal_pairs(_Vars_set,Factor,_Pairs):-
	throw(unexpected_factor(Factor)).
	
get_all_pairs([],Accum_pairs,Accum_pairs).
get_all_pairs([Var_set|Vars_sets],Accum_pairs,All_pairs):-
	maplist(get_all_pairs_1(Vars_sets),Var_set,Sets),
	unions_sl([Accum_pairs|Sets],Accum_pairs1),
	get_all_pairs(Vars_sets,Accum_pairs1,All_pairs).

get_all_pairs_1(Set_list,Elem,Set_pairs):-
	maplist(get_all_pairs_2(Elem),Set_list,Sets_pairs),
	unions_sl(Sets_pairs,Set_pairs).
get_all_pairs_2(Elem,Set,Set_pairs):-
	maplist(sorted_tuple(Elem),Set,Pair_list),
	exclude(same_var_tuple,Pair_list,Pair_list1),
	from_list_sl(Pair_list1,Set_pairs).	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
strexp_to_cost_expression(add(Summands),Exp3):-
	maplist(write_product_deep,Summands,Summands2),
	write_sum(Summands2,Exp3).
strexp_to_cost_expression(nat(Lin_exp),nat(Lin_exp)):-var(Lin_exp),!.

strexp_to_cost_expression(nat(add(Summands)),nat(Exp3)):-!,
	maplist(write_product_deep,Summands,Summands2),
	write_sum(Summands2,Exp3).
	
strexp_to_cost_expression(Else,Else).	
	
write_product_deep(mult(List),Product):-
	maplist(write_factor_deep,List,List_p),
	write_product(List_p,Product).

write_factor_deep(max(Elems),max(Elems_p)):-!,
	maplist(strexp_to_cost_expression,Elems,Elems_p).
write_factor_deep(min(Elems),min(Elems_p)):-!,
	maplist(strexp_to_cost_expression,Elems,Elems_p).	

write_factor_deep(nat(Elem),nat(Exp)):-nonvar(Elem),
	functor(Elem,add,1),!,
	strexp_to_cost_expression(Elem,Exp).
write_factor_deep(add(Elem),Exp):-!,
	strexp_to_cost_expression(add(Elem),Exp).	
write_factor_deep(X,X).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
strexp_simplify(Exp,Exp):-var(Exp),!.
strexp_simplify(Exp,Simple_exp):-
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
strexp_simplify(Exp,Simple_exp):-
	nonvar(Exp),
	Exp=add(Summands),!,
	simplify_summands(Summands,Summands_simple),
	Simple_exp=add(Summands_simple).	
	
strexp_simplify(Exp,Exp).
	

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
	partition(is_rational,Factors,Numbers,Not_numbers),
	ut_sort(Not_numbers,Not_numbers_sorted),
	foldl(multiply_fr,Numbers,1,Amount).


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
	maplist(strexp_simplify,List,List_simplified),
	from_list_sl(List_simplified,Set),
	(Set=[One]->
		Res=One
	;
		Res=min(Set)
	).
simplify_factor_internal(max(List),Res):-!,
	maplist(strexp_simplify,List,List_simplified),
	from_list_sl(List_simplified,Set),
	(Set=[One]->
		Res=One
	;
		Res=max(Set)
	).
simplify_factor_internal(Factor,Factor_simple):-
	strexp_simplify(Factor,Factor_simple),!.
	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

zero_factor_var(mult([Zero])):-nonvar(Zero),Zero==0.	

select_not_var([Factor|Factors],Factor1,Factors):-
	\+var(Factor),
	Factor=Factor1.
select_not_var([Factor|Factors],Factor1,[Factor|Factors1]):-
	select_not_var(Factors,Factor1,Factors1).

substitute_by_dummy_complex_term(Map,(Name,Var)):-
	lookup_lm(Map,Name,(N,_)),
	get_dummy_factors(N,Factors),
	Var=add([mult([1|Factors])]).
get_dummy_factors(0,[]).
get_dummy_factors(N,[nat(_)|Factors]):-
	N>0,
	N1 is N-1,
	get_dummy_factors(N1,Factors).	