


:- module(conditional_upper_bounds,[compute_conditional_upper_bounds/1]).


:- use_module('../utils/cost_expressions',[cexpr_simplify/3]).
:- use_module('../utils/cofloco_utils',[normalize_constraint/2,
						constraint_to_coeffs_rep/2,
						bagof_no_fail/3,
						zip_with_op/4,
						assign_right_vars/3,
						sort_with/3]).
:- use_module('../IO/params',[get_param/2]).						
:- use_module('../db',[closed_upper_bound/4,add_conditional_upper_bound/3]).
:- use_module('../refinement/invariants',[backward_invariant/4]).

:- use_module(stdlib(set_list)).
:- use_module(stdlib(numeric_abstract_domains)).
:- use_module(stdlib(utils)).
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).

compute_conditional_upper_bounds(Head):-
	findall((Head,execution_pattern(Cost,Condition)),
		(
		closed_upper_bound(Head,Chain,_,Cost),
		backward_invariant(Head,(Chain,_),_,Condition)
		)
		,Ex_pats),
	assign_right_vars(Ex_pats,Head,Ex_pats1),
	assign_id_number(Ex_pats1,1,Ex_pats2),
    maplist(form_sets,Ex_pats2,Ex_pats3),
    maplist(get_execution_pattern_original_conds,Ex_pats3,Conditions),
	unions_sl(Conditions,Conditions_set),
	remove_redundant(Conditions_set,Conditions_set2),
	make_exclusive_classification(Conditions_set2,Ex_pats3,[],List_pairs),
	from_pair_list_mm(List_pairs,Multimap),
	maplist(simplify_ubs,Multimap,Multimap_simplified),
	(get_param(debug,[])->
	foldl(append_ub_cond,Multimap_simplified,[],All_paths),
	check_2t2_incompatibility(All_paths)
	;
	true),
	maplist(save_conditional_upper_bound(Head),Multimap_simplified).
	
	
assign_id_number([],_,[]).
assign_id_number([execution_pattern(Cost,Condition)|Ex_patterns],Id,[execution_pattern(Id,Cost,Condition)|Ex_patterns1]):-
	Id1 is Id+1,
	assign_id_number(Ex_patterns,Id1,Ex_patterns1).
	
form_sets(execution_pattern(Id,Cost,Condition),execution_pattern(Id,Cost,Condition_set,Condition_set)):-
    nad_normalize(Condition,Condition_min),
	from_list_sl(Condition_min,Condition_set).
		
save_conditional_upper_bound(Head,(Cost,Precondition)):-
	add_conditional_upper_bound(Head,Cost,Precondition).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


make_exclusive_classification(Conditions_set,Ex_pats,Accum,Classified_list):-
	remove_redundant(Conditions_set,Conditions_set2),
	classify_patterns(Conditions_set2,Ex_pats,[],Possible_roots),
	sort_with(Possible_roots,smaller_heuristic,Ordered_roots),
	make_exclusive_classification_1(Ordered_roots,Ex_pats,Accum,Classified_list).
	
make_exclusive_classification_1(_,[],Accum,Accum):-!.

make_exclusive_classification_1(_,[execution_pattern(_,Ub_simple,_,Conds)],Accum,[(Ub_simple,Minimal_conds)|Accum]):-!,
	nad_normalize(Conds,Minimal_conds).
	
make_exclusive_classification_1(_,Ex_pats,Accum,[(Ub_simple,Minimal_conds)|Accum]):-
	maplist(get_execution_pattern_cost,Ex_pats,Extracted_Ubs),
	from_list_sl(Extracted_Ubs,[Ub_simple]),!,
	maplist(get_execution_pattern_conds,Ex_pats,Conds),
	nad_list_lub(Conds,Joined_conds),
	nad_normalize(Joined_conds,Minimal_conds).

	
make_exclusive_classification_1([],Ex_pats,Accum,[(Ub_simple,Minimal_conds)|Accum]):-!,
	maplist(get_execution_pattern_conds,Ex_pats,Conds),
	maplist(get_execution_pattern_cost,Ex_pats,Extracted_Ubs),
	unions_sl(Conds,Joined_conds),
	nad_normalize(Joined_conds,Minimal_conds),
	(Extracted_Ubs=[Ub_simple]->
	   true
	;
	 Ub=max(Extracted_Ubs),
	 cexpr_simplify(Ub,Minimal_conds,Ub_simple)
	).


make_exclusive_classification_1([root(Cond,Yes,No,None,_,_)|Ordered_roots],Ex_pats,Accum,Classified_list):-
	negate_condition(Cond,NegCond),
	union_sl(Yes,None,YesNone),
	union_sl(No,None,NoNone),
	filter_selected_execution_patterns(YesNone,Ex_pats,Ordered_roots,Cond,YesNone_pats,Ordered_rootsYes),
	make_exclusive_classification_1(Ordered_rootsYes,YesNone_pats,Accum,Accum1),
	
	(NegCond=or(Neg1,Neg2)->
	   filter_selected_execution_patterns(NoNone,Ex_pats,Ordered_roots,Neg1,NoNone_pats1,Ordered_rootsNo1),
	   make_exclusive_classification_1(Ordered_rootsNo1,NoNone_pats1,Accum1,Accum2),
	   
	   filter_selected_execution_patterns(NoNone,Ex_pats,Ordered_roots,Neg2,NoNone_pats2,Ordered_rootsNo2),
	   make_exclusive_classification_1(Ordered_rootsNo2,NoNone_pats2,Accum2,Classified_list)
	;
	   filter_selected_execution_patterns(NoNone,Ex_pats,Ordered_roots,NegCond,NoNone_pats1,Ordered_rootsNo1),
	   make_exclusive_classification_1(Ordered_rootsNo1,NoNone_pats1,Accum1,Classified_list)
	).

filter_selected_execution_patterns(Ex_pat_ids,Execution_patterns,Ordered_roots,New_condition,Execution_patterns_Filtered,Ordered_roots_new):-
	include(execution_pattern_contained_in(Ex_pat_ids),Execution_patterns,Execution_patterns_1),
	maplist(add_condition_and_remove(New_condition),Execution_patterns_1,Execution_patterns_2),
	include(consistent_ub,Execution_patterns_2,Execution_patterns_Filtered),
	  
	maplist(get_execution_pattern_id,Execution_patterns_Filtered,Ex_pat_ids1),
	from_list_sl(Ex_pat_ids1,Ex_pat_ids_new),
	maplist(get_execution_pattern_original_conds,Execution_patterns_Filtered,Conditions),
	unions_sl(Conditions,Conditions_set),
	filter_and_sort_roots(Ordered_roots,Ex_pat_ids_new,Conditions_set,Ordered_roots_new).
	
execution_pattern_contained_in(Set,execution_pattern(Id,_,_,_)):-
	contains_sl(Set,Id).

filter_and_sort_roots(Roots,Ex_pats_ids,Conditions,Sorted_roots):-
	include(root_condition(Conditions),Roots,Roots1),
	maplist(update_sets(Ex_pats_ids),Roots1,Roots2),
	sort_with(Roots2,smaller_heuristic,Sorted_roots).
	
root_condition(Conditions,root(Cond,_Yes,_No,_None,_N1,_N2)):-
	contains_sl(Conditions,Cond).
	
update_sets(Ex_pats_ids,root(Cond,Yes,No,None,_,_),root(Cond,Yes2,No2,None2,NClassified,PClassified)):-
	intersection_sl(Yes,Ex_pats_ids,Yes2),
	intersection_sl(No,Ex_pats_ids,No2),
	intersection_sl(None,Ex_pats_ids,None2),
	length(Yes2,Nyes),
	length(No2,NNo),
	NClassified is Nyes+NNo,
	PClassified is Nyes*NNo.



add_condition_and_remove(Cond,execution_pattern(Id,Cost,Original_cons,All_cons),execution_pattern(Id,Cost,Original_cons1,All_cons1)):-
	insert_sl(All_cons,Cond,All_cons1),
	remove_sl(Original_cons,Cond,Original_cons1).
	
remove_redundant([],[]).

remove_redundant([E=C|Other],[E=C|Result]):-
	normalize_constraint(E>=C+1,Normalized_cons1),
	normalize_constraint(E+1=<C,Normalized_cons2),
	remove_sl(Other,Normalized_cons1,Other1),
	remove_sl(Other1,Normalized_cons2,Other2),
	remove_redundant(Other2,Result).	
	

remove_redundant([E>=C|Other],[E>=C|Result]):-
	normalize_constraint(E+1=<C,Normalized_cons1),
	remove_sl(Other,Normalized_cons1,Other1),
	remove_redundant(Other1,Result).	
remove_redundant([E=<C|Other],[E=<C|Result]):-
	normalize_constraint(E>=C+1,Normalized_cons1),
	remove_sl(Other,Normalized_cons1,Other1),
	remove_redundant(Other1,Result).		


consistent_ub(execution_pattern(_,_,_,All_cons)):-
	nad_consistent_constraints(All_cons).
	
negate_condition(X>=Y,Neg):-
	normalize_constraint(X+1=<Y,Neg).
negate_condition(X=<Y,Neg):-
	normalize_constraint(X>=Y+1,Neg).
negate_condition(X=Y,or(Neg1,Neg2)):-
	normalize_constraint(X>=Y+1,Neg1),
	normalize_constraint(X+1=<Y,Neg2).

get_execution_pattern_id(execution_pattern(Id,_,_,_),Id).
get_execution_pattern_cost(execution_pattern(_,Cost,_,_),Cost).
get_execution_pattern_original_conds(execution_pattern(_,_,Conditions,_),Conditions).
get_execution_pattern_conds(execution_pattern(_,_,_,Conditions),Conditions).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5

classify_patterns([],_,Accum,Accum).
classify_patterns([Cond|More],Patterns,Accum,Roots):-
	classify_patterns_1(Patterns,Cond,Yes,No,None),
	from_list_sl(Yes,Yes_set),
	from_list_sl(No,No_set),
	from_list_sl(None,None_set),
	length(Yes,Nyes),
	length(No,NNo),
	NClassified is Nyes+NNo,
	PClassified is Nyes*NNo,
	classify_patterns(More,Patterns,[root(Cond,Yes_set,No_set,None_set,NClassified,PClassified)|Accum],Roots).

classify_patterns_1([],_,[],[],[]).

classify_patterns_1([execution_pattern(Id,_Cost,_Original_conds,Conditions)|More],Cond,[Id|Yes],No,None):-
	contains_sl(Conditions,Cond),!,
	classify_patterns_1(More,Cond,Yes,No,None).

classify_patterns_1([execution_pattern(Id,_Cost,_Original_conds,Conditions)|More],Cond,[Id|Yes],No,None):-
	term_variables((Conditions,Cond),Vars),
	nad_entails(Vars,Conditions,[Cond]),!,
	classify_patterns_1(More,Cond,Yes,No,None).

classify_patterns_1([execution_pattern(Id,_Cost,_Original_conds,Conditions)|More],Cond,Yes,No,[Id|None]):-
	nad_consistent_constraints([Cond|Conditions]),!,
	classify_patterns_1(More,Cond,Yes,No,None).

classify_patterns_1([execution_pattern(Id,_Cost,_Original_conds,_Conditions)|More],Cond,Yes,[Id|No],None):-
	classify_patterns_1(More,Cond,Yes,No,None).


smaller_heuristic(root(_,_,_,_,_N1,N11),root(_,_,_,_,_N2,N22)):-
	N11<N22,!.
smaller_heuristic(root(_,_,_,_,N1,N11),root(_,_,_,_,N2,N22)):-
	N11=N22,N1<N2.
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
append_ub_cond((_,Paths),Paths1,Paths2):-
	append(Paths,Paths1,Paths2).
	
check_2t2_incompatibility([]).
check_2t2_incompatibility([Cs|More]):-
	maplist(incompatible(Cs),More),
	check_2t2_incompatibility(More).

incompatible(Cs,Cs1):-
	append(Cs,Cs1,Cs_all),
	\+nad_consistent_constraints(Cs_all).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

simplify_ubs(Ub_list,Ubs_list_simplified):-
	Ub_list=Ubs_list_simplified.
	


	
compose_program([],[],_Head,_N,Predicate_list,Predicate_list).
compose_program([Exp|More],[PrecList|MorePrec],Head,N,Accum,Pattern_list_out):-
	compose_program1(PrecList,Exp,Head,N,1,Prattern_list),
	append(Prattern_list,Accum,Accum2),
	N1 is N+1,
	compose_program(More,MorePrec,Head,N1,Accum2,Pattern_list_out).

compose_program1([],_,_,_,_,[]).
compose_program1([Prec|PrecList],Exp,Head,N,NSec,[Pattern|Pattern_list]):-
	Pattern=execution_pattern(Head,N:NSec,Prec,Exp),
	NSec1 is NSec+1,
	compose_program1(PrecList,Exp,Head,N,NSec1,Pattern_list).