/** <module> structured_cost_expression

 This module provides support for structured cost expressions (strexp)
 and partial structured cost expressions (partial_strexp)
 which are used in the cost structure solving process

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
 *strexp: a nested sum of products with max and min operator and linear expressions as basic factors:
       strexp:=add(list(summand)) | nat(add(list(summand))) |  nat(linexp) | inf | -inf
       summand:=mult(list(factor),rational)
       		rational cannot be zero
       factor:= strexp | max(list(strexp)) | min(list(strexp))
       
 * partial_strexp: partial(index,strexp_var) | strexp
   represents an incomplete strexp.  strexp_var can still contain variables instead of strexp.
   The correspondence of the variables and the intermediate variables (itvar) is recorded in the index
 
   
*/
:- module(structured_cost_expression,[
		partial_strexp_estimate_complexity/3,
		partial_strexp_complexity/3,
		strexp_to_cost_expression/2,
		strexp_var_simplify/2,
		strexp_var_get_multiplied_factors/3,
		strexp_simplify_max_min/2,
		strexp_is_zero/1,
		get_all_pairs/3,
		strexp_transform_summand/2
	]).


:- use_module(cofloco_utils,[
		write_sum/2,
		write_product/2,
		get_all_pairs/3,
		zip_with_op/3,
		is_rational/1]).	
:- use_module(cost_expressions,[
		is_linear_exp/1]).			
		
:- use_module(stdlib(linear_expression),[parse_le/2,write_le/2,negate_le/2]).	
:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4,ut_sort/2,ut_var_member/2]).	
:- use_module(stdlib(multimap),[put_mm/4,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).
:- use_module(stdlib(fraction)).
:- use_module(stdlib(set_list),[element_sl/2,remove_sl/3,difference_sl/3,contains_sl/2,from_list_sl/2,unions_sl/2,union_sl/3,insert_sl/3,intersection_sl/3]).
:-use_module(library(apply_macros)).
:-use_module(library(lists)).


%! strexp_is_zero(Strexp:strexp)
% succeeds if Strexp is zero. It expects a simplified strexp
strexp_is_zero(add([])):-!.
strexp_is_zero(nat(Add)):-
	nonvar(Add),
	Add==add([]),!.

%! check that the expression is well formed according to the definition
strexp_check_well_formed(inf).
strexp_check_well_formed(-inf).

strexp_check_well_formed(nat(Lin_exp)):-
	is_linear_exp(Lin_exp),!.

strexp_check_well_formed(nat(add(Summands))):-
	maplist(summand_check_well_formed,Summands).
strexp_check_well_formed(add(Summands)):-	
	maplist(summand_check_well_formed,Summands).
	

summand_check_well_formed(mult(Factors,Coeff)):-
	ground(Coeff),
	Coeff\=0,
	maplist(factor_check_well_formed,Factors).

factor_check_well_formed(max(Strexprs)):-
	maplist(strexp_check_well_formed,Strexprs).
factor_check_well_formed(min(Strexprs)):-
	maplist(strexp_check_well_formed,Strexprs).
factor_check_well_formed(Strexpr):-
	strexp_check_well_formed(Strexpr).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% obtain complexity of strexp and partial_strexp

%! partial_strexp_complexity(Strexp:partial_strexp,N:int)
% obtain the complexity of a partial_strexp. If the partial_strexp has 
% undefined variables, the complexity is maximal or minimal depending on
% whether we want to over-approximate or under-approximate
partial_strexp_complexity(partial(_,_),ub,100).
partial_strexp_complexity(partial(_,_),lb,0).
partial_strexp_complexity(Strexp,_,N):-
	strexp_complexity(Strexp,N).
	
%! partial_strexp_estimate_complexity(PStrexp:partial_strexp,N:int)
% Estimate the complexity of a PStrexp by substituting any undefined variable in PStrexp
% by a dummy expression with the estimated complexity.
% the estimated complexity of each variable is given by Complexity_map
partial_strexp_estimate_complexity(partial(Index,Exp),Complexity_map,Complexity):-!,
	copy_term(partial(Index,Exp),partial(Index_c,Exp_c)),
	maplist(substitute_by_dummy_complex_term(Complexity_map),Index_c),
	strexp_complexity(Exp_c,Complexity).
partial_strexp_estimate_complexity(Exp,_,Complexity):-
	strexp_complexity(Exp,Complexity).

%! strexp_complexity(Strexp:strexp,N:int)
% compute the asymptotic complexity of a strexp
strexp_complexity(inf,100):-!.
strexp_complexity(-inf,100):-!.

strexp_complexity(nat(Linexp),N):-
	is_linear_exp(Linexp),!,
	(ground(Linexp)-> 
	   N=0
	   ;
	   N=1).

strexp_complexity(nat(add(Summands)),N):-
	(Summands=[_|_]->
	maplist(strexp_summand_complexity,Summands,N_list),
	max_list(N_list,N)
	;
	N=0).	
	
strexp_complexity(add(Summands),N):-
	(Summands=[_|_]->
	maplist(strexp_summand_complexity,Summands,N_list),
	max_list(N_list,N)
	;
	N=0).
strexp_summand_complexity(mult(Factors,Coeff),N1):-
	maplist(strexp_factor_complexity,Factors,N_list),
	sum_list([0|N_list],N),
	(greater_fr(0,Coeff)->
		N1 is 0-N
		;
		N1=N
	).
		
strexp_factor_complexity(max(Factors),N):-
	maplist(strexp_complexity,Factors,N_list),
	max_list(N_list,N).
strexp_factor_complexity(min(Factors),N):-
	maplist(strexp_complexity,Factors,N_list),
	min_list(N_list,N).	
		
strexp_factor_complexity(Factor,N):-
	strexp_complexity(Factor,N).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! 	strexp_var_get_multiplied_factors(+Strexp:strexp_var,+Vars_set:list_set(var),-Pairs:list((var,var))
% given a strexp_var, obtain the pairs of variables that appear multiplied
strexp_var_get_multiplied_factors(nat(add(Summands)),Vars_set,Pairs):-
	maplist(get_summand_multiplied_vars(Vars_set),Summands,Pair_list),
	unions_sl(Pair_list,Pairs).	
strexp_var_get_multiplied_factors(add(Summands),Vars_set,Pairs):-
	maplist(get_summand_multiplied_vars(Vars_set),Summands,Pair_list),
	unions_sl(Pair_list,Pairs).

get_summand_multiplied_vars(Vars_set,mult(Factors,_Coeff),Pairs_final):-
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
	strexp_var_get_multiplied_factors(Factor,Vars_set,Pairs),!.
get_internal_pairs(_Vars_set,Factor,_Pairs):-
	throw(unexpected_factor(Factor)).
	

	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

%! strexp_to_cost_expression(+Strexp:strexp,-Exp:cost_expression)
% transform a strexp into a cost_expression that can be printed
strexp_to_cost_expression(add(Summands),Exp3):-
	maplist(write_product_deep,Summands,Summands2),!,
	write_sum(Summands2,Exp3).
strexp_to_cost_expression(nat(Lin_exp),nat(Lin_exp)):-var(Lin_exp),!.

strexp_to_cost_expression(nat(add(Summands)),nat(Exp3)):-!,
	maplist(write_product_deep,Summands,Summands2),
	write_sum(Summands2,Exp3).
	
strexp_to_cost_expression(Else,Else).	
	
write_product_deep(mult(List,Coeff),Product):-
	maplist(write_factor_deep,List,List_p),
	write_product([Coeff|List_p],Product).

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% predicates to obtain combine the sign of strexp and summands
% a sign can be 'pos' or 'unknown'
strexp_get_sign(add(Summands),Sign):-
	maplist(get_summand_sign,Summands,Signs),
	foldl(sign_or,Signs,pos,Sign).
	
strexp_get_sign(nat(_),pos).

sign_or(unknown,_,unknown).
sign_or(pos,unknown,unknown).
sign_or(pos,pos,pos).

get_summand_sign(mult(_,X),pos):-
	geq_fr(X,0),!.
get_summand_sign(_X,unknown).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	


%! strexp_var_simplify(Strexp:strexp_var,Strexp_simple:strexp_var)
% Simplify a strexp that might contain variables
%  * attempt to express Strexp as a sum of products
%  * group all summands with the same symbolic expression
%  * simplify expressions of the form max([Strexp1,Strexp2..Strexpn]) and min([Strexp1,Strexp2..Strexpn])
strexp_var_simplify(inf,inf):-!.
strexp_var_simplify(-inf,-inf):-!.
strexp_var_simplify(0,add([])):-!.


strexp_var_simplify(add(Summands),add(Summands_simple)):-!,
    strexp_var_simplify_summands(Summands,_Sign,Summands_simple).

strexp_var_simplify(nat(Sum),Res):-
	nonvar(Sum),
	Sum=add(Summands),!,
    strexp_var_simplify_summands(Summands,Sign,Summands_simple),
    (Sign=pos->
    	Res=add(Summands_simple)
    	;
    	Res=nat(add(Summands_simple))
    ).

strexp_var_simplify(nat(Lin_exp),nat(Lin_exp)):-
	is_linear_exp(Lin_exp),!.
	
strexp_var_simplify(Else,Else):-
	throw(found_bad_formed_strexp(Else)).
		

strexp_var_simplify_summands(Summands,Sign,Summands_sorted):-
	maplist(strexp_var_simplify_summand,Summands,Summands_simple),
	ut_flat_list(Summands_simple,Summands_simple_flat),
	foldl(compress_summands,Summands_simple_flat,[],Summands_compressed),
	from_list_sl(Summands_compressed,Summands_sorted),
	strexp_get_sign(add(Summands_compressed),Sign).

%! compress_summands(Summand:summand,Compressed:list(summand),Compressed1:list(summand))
% add the Summand to the list of summands Compressed and return Compressed1 
compress_summands(mult(Content,Coeff),Compressed,Compressed1):-
	add_content(Compressed,Content,Coeff,Compressed1).

add_content(Compressed,_Content,0,Compressed):-!.
add_content([],Content2,Coeff2,[mult(Content2,Coeff2)]).

add_content([mult(Content1,Coeff1)|Rest],Content2,Coeff2,Compressed):-
	Content1==Content2,!,
	sum_fr(Coeff1,Coeff2,Coeff3),
	(Coeff3=0->
		Compressed=Rest
	;
		Compressed=[mult(Content1,Coeff3)|Rest]
	).
add_content([mult(Content1,Coeff1)|Rest],Content2,Coeff2,[mult(Content1,Coeff1)|Compressed]):-
	add_content(Rest,Content2,Coeff2,Compressed).	
	
strexp_var_simplify_summand(mult(Factors,Coeff),Summands):-
	maplist(strexp_var_simplify_factor,Factors,Factors_simple),
	strexp_apply_distributibity(mult(Factors_simple,Coeff),Summands).

strexp_apply_distributibity(mult(Factors,Coeff),Summands_flat):-
	select_not_var(Factors,add(Summands),Factors1),!,
	maplist(multiply_by_factors(Factors1,Coeff),Summands,Summands1),
	
	maplist(strexp_apply_distributibity,Summands1,Summands2),
	ut_flat_list(Summands2,Summands_flat).

strexp_apply_distributibity(mult(Factors,Coeff),mult(Factors,Coeff)).

multiply_by_factors(Factors1,Coeff,mult(Summand,Coeff2),mult(Factors_sorted,Coeff3)):-
	multiply_fr(Coeff,Coeff2,Coeff3),
	append(Factors1,Summand,Factors2),
	ut_sort(Factors2,Factors_sorted).
	
strexp_var_simplify_factor(Var,Var):-var(Var),!.

strexp_var_simplify_factor(min(List),min(Set)):-!,
	maplist(strexp_var_simplify_factor,List,List_simplified),
	from_list_sl(List_simplified,Set).
%	strexp_simplify_max_min(min(Set),Res).

strexp_var_simplify_factor(max(List),max(Set)):-!,
	maplist(strexp_var_simplify_factor,List,List_simplified),
	from_list_sl(List_simplified,Set).
%	strexp_simplify_max_min(max(Set),Res).

strexp_var_simplify_factor(Factor,Factor_simple):-
	strexp_var_simplify(Factor,Factor_simple),!.


%FIMXE make this predicate Var compatible
	
%! strexp_simplify_max_min(Expr:op(list(strexp_var)),Strexp:strexp_var)
% where op is 'max' or 'min'
% simplify an expression max([Strexp1,Strexp2..Strexpn]) and min([Strexp1,Strexp2..Strexpn])
% by extracting common summands of several internal expressions
%
% for example: max(3*nat(x)+2*nat(y),2*nat(y))= 2nat(x)+ max(nat(x)+2*nat(y),0)
% and simplify trivial max/min expressions
% 2nat(x)+ max(nat(x)+2*nat(y),0)=2nat(x)+ nat(x)+2*nat(y)=3*nat(x)+2*nat(y)
strexp_simplify_max_min(Expr,add(Common_summands_compressed)):-
	Expr=..[Max_min,Strexp_list],
	assertion(maplist(strexp_check_well_formed,Strexp_list)),
	strexp_extract_common_summands(Strexp_list,Max_min,Common_summands),
	foldl(compress_summands,Common_summands,[],Common_summands_compressed).
			
%! strexp_extract_common_summands(Strexp_list:list(strexp_var),Max_min:flag,Common_summands:list(summand))
% Given a list of strexp that we want to obtain the maximum or minimum accroding ot Max_min,
% extract common summands and simplify the expressions
%
% if no summand can be extracted, we create a summand that contains
% max(Strexp_list) or min(Strexp_list)
strexp_extract_common_summands(Strexp_list,Max_min,Common_summands):-
	% get a summand that appears in multiple elements of the list
	get_best_summand_candidate(Strexp_list,Summand),!,
	foldl(extract_summand(Summand),Strexp_list,([],[]),(Strexp_with,Strexp_without)),
	% if the summand was not contained in all the elements of Strexp_list
	(Strexp_without\=[]->
	    % we create a summand max/min(summand+Summands_with,Summands_without)
	    % where Summands_with and Summands_without are the result of extracting the common
	    % summands to the strexp that used to contain summand and the ones that did not
		strexp_extract_common_summands(Strexp_with,Max_min,Summands_with),
		strexp_extract_common_summands(Strexp_without,Max_min,Summands_without),
		% add summands with the same symbolic expression
		foldl(compress_summands,[Summand|Summands_with],[],Summands_with_compressed),
		foldl(compress_summands,Summands_without,[],Summands_without_compressed),
		% simplify this resulting expression again
		strexp_extract_common_summands([add(Summands_with_compressed),add(Summands_without_compressed)],Max_min,Common_summands)
	;
	% if the summand was contained in all Strexp, we have Summand+Summands_with
		strexp_extract_common_summands(Strexp_with,Max_min,Summands_with),
		Common_summands=[Summand|Summands_with]
	).

%base case (we cannot extract more common summands)	
strexp_extract_common_summands(Strexp_list,Max_min,Res):-
	strexp_simplify_easy_maxmin(Strexp_list,Max_min,Strexp_list1),
	create_simple_maxmin_summand(Strexp_list1,Max_min,Res).

% if the max min expression contains a zero we can simplify according to 
% whether it is max or min
strexp_simplify_easy_maxmin(Strexp_list,Max_min,Strexp_list1):-
	partition(strexp_is_zero,Strexp_list,[_|_],Non_zero),
	maplist(strexp_get_sign,Non_zero,Signs),
	foldl(sign_or,Signs,pos,pos),
	(Max_min=max->
		Strexp_list1=Non_zero
		;
		Strexp_list1=[]
	).
strexp_simplify_easy_maxmin(Strexp_list,_Max_min,Strexp_list).	

%! create_simple_maxmin_summand(Strexp_list:list(strexp_var),Max_min:flag,Res:term)
% given a list of strexp Strexp_list, create a summand with max/min(Strexp_list)
create_simple_maxmin_summand(Strexp_list,Max_min,Res):-
	(Strexp_list=[]->
	   Res=[]
	   ;
	   (Strexp_list=[One]->
	   		(One=add([Summand])->
	   			Res=[Summand]
	   			;
	   	    	Res=[mult([One],1)]
	   	    	)
	   ;
	   		Expr=..[Max_min,Strexp_list],
	        Res=[mult([Expr],1)]
	   )
	 ).
	


%! extract_summand(Summand:summand,Strexp:strexp_var,Sm_with_Sm_without:(list(strexp),list(strexp)),Sm_with_Sm_without1:(list(strexp),list(strexp)))
%  extract Summand from Strexp  and add the result to the first list of Sm_with_Sm_without
% if Summand is not in Strexp, add Strexp to the second list of Sm_with_Sm_without
% if a Strexp is a variable, we cannot extract any summands
extract_summand(_Summand,Var,(Sm_with,Sm_without),(Sm_with,[Var|Sm_without])):-var(Var),!.
% we don't extract summands from strexp wrapped in nats
extract_summand(_Summand,nat(add(Summands)),(Sm_with,Sm_without),(Sm_with,[nat(add(Summands))|Sm_without])).

extract_summand(Summand,add(Summands),(Sm_with,Sm_without),([add(Summands1)|Sm_with],Sm_without)):-
	remove_summand(Summands,Summand,Summands1),!.
extract_summand(_Summand,add(Summands),(Sm_with,Sm_without),(Sm_with,[add(Summands)|Sm_without])).


remove_summand([mult(X,Coeff)|Summands],mult(X2,Coeff2),Res):-
	X2==X,!,
	subtract_fr(Coeff,Coeff2,Coeff3),
	(leq_fr(Coeff3,0)->
	 	Res=Summands
	;
		Res=[mult(X,Coeff3)|Summands]
	).
remove_summand([mult(X,Coeff)|Summands],mult(X2,Coeff2),[mult(X,Coeff)|Res]):-
	remove_summand(Summands,mult(X2,Coeff2),Res).
	
%! get_best_summand_candidate(+Strexp_list:list(strexp_var),-Summand:summand) is semidet
% get the summand that appears in most strexp of Strexp_list with the minimum coefficient
% it has to appear more than once or the predicate fails
% we only select constant summands if they appear in every strexp of Strexp_list
get_best_summand_candidate(Strexp_list,mult(Selected_summand,Coeff)):-
	exclude(var,Strexp_list,Strexp_list_without_vars),
	maplist(zip_with_op(_),Summands_list,Strexp_list_without_vars),
	length(Strexp_list,N_total),
	ut_flat_list(Summands_list,All_summands),
	foldl(count_summand_occurrences,All_summands,[],Summands_count),
	exclude(constant_not_total(N_total),Summands_count,Summands_count_non_cnt),
	Summands_count_non_cnt=[Pair1|Summands_count1],
	foldl(get_highest_occurrence_summand,Summands_count1,Pair1,(Selected_summand,(Coeff,N))),
	N > 1,!.

constant_not_total(N_total,([],(_,N))):-
	N < N_total.
		
count_summand_occurrences(mult(X,Coeff),S_map,S_map1):-
	lookup_lm(S_map,X,(Coeff2,N)),!,
	N1 is N+1,
	min_fr(Coeff,Coeff2,Coeff3),
	insert_lm(S_map,X,(Coeff3,N1),S_map1).
count_summand_occurrences(mult(X,Coeff),S_map,S_map1):-
	insert_lm(S_map,X,(Coeff,1),S_map1).	

get_highest_occurrence_summand((_Summand,(_Coeff,N)),(Summand2,(Coeff2,N2)),(Summand2,(Coeff2,N2))):-
	N2 >= N,!.
get_highest_occurrence_summand((Summand,(Coeff,N)),(_Summand2,_),(Summand,(Coeff,N))).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% auxiliary predicates
strexp_transform_summand(mult(Factors),mult(Not_numbers_sorted,Amount)):-
	partition(is_rational,Factors,Numbers,Not_numbers),
	ut_sort(Not_numbers,Not_numbers_sorted),
	foldl(multiply_fr,Numbers,1,Amount).

zero_factor_var(mult([Zero])):-nonvar(Zero),Zero==0.	

select_not_var([Factor|Factors],Factor1,Factors):-
	\+var(Factor),
	Factor=Factor1.
select_not_var([Factor|Factors],Factor1,[Factor|Factors1]):-
	select_not_var(Factors,Factor1,Factors1).

substitute_by_dummy_complex_term(Map,(Name,Var)):-
	lookup_lm(Map,Name,(N,_)),
	get_dummy_factors(N,Factors),
	Var=add([mult(Factors,1)]).
get_dummy_factors(0,[]).
get_dummy_factors(N,[nat(_)|Factors]):-
	N>0,
	N1 is N-1,
	get_dummy_factors(N1,Factors).	