/** <module> conditional_bounds

This module computes conditional upper and lower bounds using the upper and lower bounds of all the chains.
The conditions to execute different chains do not have to be mutually exclusive.
Given an input value, there might be several feasible chains and to obtain an upper/lower bound
we should consider the maximum/minimum of all of them.

On the other hand, the set of conditional bounds computed in this module are mutually exclusive.
That is, if we have an input, at most one conditional  bound's precondition can be satisfied
and the bound of that conditional  bound is valid.

In order to compute conditional bounds, we partition the input space using the
constraints that appear in the chain bounds. We split the input space until no more
distinctions can be made. Finally, we try to simplify the conditions of each conditional
upper bound.


The specific "data types" used in this module are the following:
	* execution_pattern: execution_pattern(int,cost_expression,list_set(linear_constraint),list_set(linear_constraint))
	  An execution pattern has the form execution_pattern(Id,Cost_expression,Original_conds,Conds)
	   * Id:an integer id
	   * Cost_expression: the cost expression for each execution pattern
	   * Original_conds:a set of constraints to be used to partition
	   * Conds: a set of constraints that define its (possibly refined) precondition
	  initially Original_conds and Conds are the same. In the process of partitioning
	  we will add constraints to Conds and remove from Original_conds.
	* classifier: classifier(Cond,Yes,No,None,S_classified,P_classified):classifier(linear_constraint,list_set(int),list_set(int),list_set(int),int,int)
	  a classifier is a linear constraint annotated with the following:
	    * Yes: is a set of execution patterns ids that are implied by the condition
	    * No: is a set of execution patterns ids that  are incompatible with the condition
	    * None: is a set of execution patterns ids that neither implied, nor incompatible  with the condition
	    * S_classified: is length(Yes)+length(No)
	    * P_classified: is length(Yes)*length(No)
	  classifiers are used to decide in which order to partition the input space so the number of partitions is minimal
 
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



:- module(conditional_bounds,[compute_conditional_bounds/1]).

:- use_module('../db',[
		  external_call_pattern/5,
		  closed_upper_bound/4,
		  closed_lower_bound/4,
		  add_conditional_bound/3]).

:-use_module('../refinement/invariants',[backward_invariant/4]).
:- use_module('../utils/cofloco_utils',[normalize_constraint/2,
						constraint_to_coeffs_rep/2,
						tuple/3,
						sort_with/3,
						assign_right_vars/3]).
:- use_module('../utils/cost_expressions',[cexpr_simplify/3]).
:- use_module('../utils/polyhedra_optimizations',[group_relevant_vars/4]).	
:- use_module('../IO/params',[get_param/2]).					
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).	
:- use_module(stdlib(set_list)).
:- use_module(stdlib(numeric_abstract_domains),[nad_consistent_constraints/1,nad_entails/3,nad_normalize/2,nad_list_lub/2]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
%! compute_conditional_bounds(+Head:term) is det
% computed the set of conditional bound of Head and store them in the database db.pl
%
%  * Take every chain closed upper bound and its related precondition (backward invariant).
%  * Partition the chain upper/lower bounds (execution pattern) according to the input space using the constraints
%    that appear in the preconditions.
%  * Try to simplify the preconditions of the inferred conditional bounds
%  * If we are debugging, check that all conditional bounds are in fact mutually exclusive
compute_conditional_bounds(Head):-
	findall((Head,execution_pattern((Cost,Lb_Cost),Condition)),
		(
		backward_invariant(Head,(Chain,_),_,Condition),
		cond_get_closed_upper_bound(Head,Chain,Cost),
		cond_get_closed_lower_bound(Head,Chain,Lb_Cost)
		)
		,Ex_pats),
	assign_right_vars(Ex_pats,Head,Ex_pats1),
    compress_execution_patterns(Ex_pats1,List_pairs),
    maplist(simplify_cost_of_pair,List_pairs,List_pairs1),
	% group the partitions according to the cost expression
	from_pair_list_mm(List_pairs1,Multimap),
	maplist(simplify_conditional_bound_precondition,Multimap,Multimap_simplified),
	% if debugging, check that the conditional upper bounds are mutually exclusive
	(get_param(debug,[])->
	foldl(append_ub_cond,Multimap_simplified,[],All_paths),
	check_2t2_incompatibility(All_paths)
	;
	true),
	maplist(save_conditional_bound(Head),Multimap_simplified).


cond_get_closed_upper_bound(Head,Chain,Cost):-
	get_param(compute_ubs,[]),!,
	closed_upper_bound(Head,Chain,_,Cost).
cond_get_closed_upper_bound(_Head,_Chain,inf).
	
cond_get_closed_lower_bound(Head,Chain,Cost):-
	get_param(compute_lbs,[]),!,
	closed_lower_bound(Head,Chain,_,Cost).	
cond_get_closed_lower_bound(_Head,_Chain,0).	
	
simplify_cost_of_pair(([Cost],Prec),(Cost,Prec)):-!.
simplify_cost_of_pair((Cost_list,Prec),((Ub_simple,Lb_simple),Prec)):-
	 maplist(tuple,Ub_list,Lb_list,Cost_list),
     Ub=max(Ub_list),
     Lb=min(Lb_list),
	 cexpr_simplify(Ub,Prec,Ub_simple),
	 cexpr_simplify(Lb,Prec,Lb_simple).


save_conditional_bound(Head,(UB_LB,Precondition)):-
	add_conditional_bound(Head,UB_LB,Precondition).
	


	
compress_execution_patterns(Execution_patterns,New_execution_patterns):-
	create_initial_execution_patterns(Execution_patterns,1,Ex_pats2),
	%use the Original_conds to partition the input space
    maplist(get_execution_pattern_original_conds,Ex_pats2,Conditions),
	unions_sl(Conditions,Conditions_set),
	% partition the input space
	make_exclusive_classification(Conditions_set,Ex_pats2,New_execution_patterns).

	


%! create_initial_execution_patterns(+Ex_patterns:list(execution_pattern(cost_expression,polyhedron)),+Id:int,-Ex_patterns1:list(execution_pattern)) is det
% Create the inital set of execution patterns:
% assign unique integer identifier to each execution pattern in Ex_patterns
% and transform the precondition into a minimal polyhedron with its constraints sorted
create_initial_execution_patterns([],_,[]).
create_initial_execution_patterns([execution_pattern(Cost,Condition)|Ex_patterns],Id,[execution_pattern(Id,Cost,Condition_set,Condition_set)|Ex_patterns1]):-
	Id1 is Id+1,
	nad_normalize(Condition,Condition_min),
	from_list_sl(Condition_min,Condition_set),
	create_initial_execution_patterns(Ex_patterns,Id1,Ex_patterns1).

		
%! make_exclusive_classification(+Conditions_set:list_set(linear_expression),+Ex_pats:list(execution_pattern),-Classified_list:list(partition_element)) is det
% partition the execution patterns Ex_pats according to the conditions Conditions_set to the limit
% and generate a list of partition elements which are pairs (cost_expression,polyhedron) such that all polyhedra
% in the generated list are mutually exclusive.
make_exclusive_classification(Conditions_set,Ex_pats,Classified_list):-
	remove_redundant(Conditions_set,Conditions_set2),
	% generate the initial classifiers. (see classifiers in module header)
	maplist(generate_initial_classifier(Ex_pats),Conditions_set2,Possible_classifiers),
	% we sort the classifiers according to their effectiveness in discriminating execution patterns
	sort_with(Possible_classifiers,smaller_heuristic,Sorted_classifiers),
	make_exclusive_classification_1(Sorted_classifiers,Ex_pats,[],Classified_list).
	
%! make_exclusive_classification_1(+Sorted_classifiers:sorted_list(classifier),+Ex_pats:list(execution_pattern),+Accum:list(partition_element),-Classified_list:list(partition_element)) is det
% partition the execution patterns Ex_pats according to the classifiers Sorted_classifiers

% if there are no execution pattern in the current partition, do nothing	
make_exclusive_classification_1(_,[],Accum,Accum):-!.

% if there is a single execution pattern, generate a partition element with its cost and conditions
make_exclusive_classification_1(_,[execution_pattern(_,Ub_simple,_,Conds)],Accum,[([Ub_simple],Minimal_conds)|Accum]):-!,
	nad_normalize(Conds,Minimal_conds).
% if there are several execution patterns but all have the same cost we can take upper bound of their 
% preconditions and generate a partition element	
make_exclusive_classification_1(_,Ex_pats,Accum,[([Ub_simple],Minimal_conds)|Accum]):-
	maplist(get_execution_pattern_cost,Ex_pats,Extracted_Ubs),
	from_list_sl(Extracted_Ubs,[Ub_simple]),!,
	maplist(get_execution_pattern_conds,Ex_pats,Conds),
	nad_list_lub(Conds,Joined_conds),
	nad_normalize(Joined_conds,Minimal_conds).

% in the worst case, if we have several execution patterns but no classifiers to discriminate them
% we create a partition element with the cost of all of them	
make_exclusive_classification_1([],Ex_pats,Accum,[(Extracted_Ubs,Minimal_conds)|Accum]):-!,
	maplist(get_execution_pattern_conds,Ex_pats,Conds),
	maplist(get_execution_pattern_cost,Ex_pats,Extracted_Ubs),
	unions_sl(Conds,Joined_conds),
	nad_normalize(Joined_conds,Minimal_conds).


	
% use the first classifier
make_exclusive_classification_1([classifier(Cond,Yes,No,None,_,_)|Sorted_classifiers],Ex_pats,Accum,Classified_list):-
	negate_condition(Cond,NegCond),
	%the patterns that are feasible if the condition is true
	union_sl(Yes,None,YesNone), 
	%the patterns that are feasible if the condition is false
	union_sl(No,None,NoNone),
    % update the classifiers so they only contain the element of YeNone or NoNone
	filter_selected_execution_patterns(YesNone,Ex_pats,Sorted_classifiers,Cond,YesNone_pats,Sorted_classifiersYes),
	make_exclusive_classification_1(Sorted_classifiersYes,YesNone_pats,Accum,Accum1),
	% if Cond is an equality, the negation is a disjuntion
	(NegCond=or(Neg1,Neg2)->
	   filter_selected_execution_patterns(NoNone,Ex_pats,Sorted_classifiers,Neg1,NoNone_pats1,Sorted_classifiersNo1),
	   make_exclusive_classification_1(Sorted_classifiersNo1,NoNone_pats1,Accum1,Accum2),
	   
	   filter_selected_execution_patterns(NoNone,Ex_pats,Sorted_classifiers,Neg2,NoNone_pats2,Sorted_classifiersNo2),
	   make_exclusive_classification_1(Sorted_classifiersNo2,NoNone_pats2,Accum2,Classified_list)
	;
	   filter_selected_execution_patterns(NoNone,Ex_pats,Sorted_classifiers,NegCond,NoNone_pats1,Sorted_classifiersNo1),
	   make_exclusive_classification_1(Sorted_classifiersNo1,NoNone_pats1,Accum1,Classified_list)
	).


add_and_normalize(Ub,Conds,Accum,[([Ub],Minimal_conds)|Accum]):-
	nad_normalize(Conds,Minimal_conds).
%! filter_selected_execution_patterns(+Ex_pat_ids:list_set(int),+Execution_patterns:list(execution_pattern),+Sorted_classifiers:sorted_list(classifier),+New_condition:linear_constraint,-Execution_patterns_Filtered:list(execution_pattern),-Sorted_classifiers_new:sorted_list(classifier)) is det
% * get the execution patterns of Ex_pat_ids
% * add the new condition to there Conds set and remove it from the Original_conds set (if it is there)
% * remove the execution patterns that become unfeasible with the new constraint
% * get the ids of the remaining
% * get the Original_conds of the remaining
% * update and sort the classifiers with the remaining ids and the remaining Original_conds
filter_selected_execution_patterns(Ex_pat_ids,Execution_patterns,Sorted_classifiers,New_condition,Execution_patterns_Filtered,Sorted_classifiers_new):-
	include(execution_pattern_contained_in(Ex_pat_ids),Execution_patterns,Execution_patterns_1),
	maplist(add_condition_and_remove(New_condition),Execution_patterns_1,Execution_patterns_2),
	include(consistent_ub,Execution_patterns_2,Execution_patterns_Filtered),
	  
	maplist(get_execution_pattern_id,Execution_patterns_Filtered,Ex_pat_ids1),
	from_list_sl(Ex_pat_ids1,Ex_pat_ids_new),
	maplist(get_execution_pattern_original_conds,Execution_patterns_Filtered,Conditions),
	unions_sl(Conditions,Conditions_set),
	remove_redundant(Conditions_set,Conditions_set2),
	filter_and_sort_classifiers(Sorted_classifiers,Ex_pat_ids_new,Conditions_set2,Sorted_classifiers_new).
	
execution_pattern_contained_in(Set,execution_pattern(Id,_,_,_)):-
	contains_sl(Set,Id).

add_condition_and_remove(Cond,execution_pattern(Id,Cost,Original_cons,All_cons),execution_pattern(Id,Cost,Original_cons1,All_cons1)):-
	insert_sl(All_cons,Cond,All_cons1),
	remove_sl(Original_cons,Cond,Original_cons1).
	
consistent_ub(execution_pattern(_,_,_,All_cons)):-
	nad_consistent_constraints(All_cons).

	
%! remove_redundant(+Constraints:list_set(linear_constraints),-Constraints1:list_set(linear_constraints))
% remove constraints whose negative is already present in the set
remove_redundant([],[]).

remove_redundant([E=C|Other],[E=C|Result]):-!,
	negate_condition(E=C,or(Neg1,Neg2)),
	remove_sl(Other,Neg1,Other1),
	remove_sl(Other1,Neg2,Other2),
	remove_redundant(Other2,Result).	
	
remove_redundant([Cond|Other],[Cond|Result]):-
	negate_condition(Cond,Neg),
	remove_sl(Other,Neg,Other1),
	remove_redundant(Other1,Result).	


%! negate_condition(+C1:linear_constraint,-C2:linear_constraint_or) is det
%  generate the negation of C1.
%  If C1 is an equality A=B, generate the construction or(A>B,A<B)
negate_condition(X>=Y,Neg):-
	normalize_constraint(X+1=<Y,Neg).
negate_condition(X=<Y,Neg):-
	normalize_constraint(X>=Y+1,Neg).
negate_condition(X=Y,or(Neg1,Neg2)):-
	normalize_constraint(X>=Y+1,Neg1),
	normalize_constraint(X+1=<Y,Neg2).

% obtain different parts of an execution pattern
get_execution_pattern_id(execution_pattern(Id,_,_,_),Id).
get_execution_pattern_cost(execution_pattern(_,Cost,_,_),Cost).
get_execution_pattern_original_conds(execution_pattern(_,_,Conditions,_),Conditions).
get_execution_pattern_conds(execution_pattern(_,_,_,Conditions),Conditions).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Classifiers


%! generate_initial_classifier(+Patterns:list(execution_pattern),+Cond:linear_constraint,-Classifier:classifier) is det
% create a classifier of Cond by checking for each execution pattern whether it
% should belong to Yes, No or None
generate_initial_classifier(Patterns,Cond,classifier(Cond,Yes_set,No_set,None_set,NClassified,PClassified)):-
	classify_patterns(Patterns,Cond,Yes,No,None),
	from_list_sl(Yes,Yes_set),
	from_list_sl(No,No_set),
	from_list_sl(None,None_set),
	length(Yes,Nyes),
	length(No,NNo),
	NClassified is Nyes+NNo,
	PClassified is Nyes*NNo.
	
classify_patterns([],_,[],[],[]).

% if the pattern contains the constraint, Yes
classify_patterns([execution_pattern(Id,_Cost,_Original_conds,Conditions)|More],Cond,[Id|Yes],No,None):-
	contains_sl(Conditions,Cond),!,
	classify_patterns(More,Cond,Yes,No,None).
% if the pattern is entailed by the constraint, Yes
classify_patterns([execution_pattern(Id,_Cost,_Original_conds,Conditions)|More],Cond,[Id|Yes],No,None):-
	term_variables((Conditions,Cond),Vars),
	nad_entails(Vars,Conditions,[Cond]),!,
	classify_patterns(More,Cond,Yes,No,None).
% if the pattern is consistent with the constraint, None
classify_patterns([execution_pattern(Id,_Cost,_Original_conds,Conditions)|More],Cond,Yes,No,[Id|None]):-
	nad_consistent_constraints([Cond|Conditions]),!,
	classify_patterns(More,Cond,Yes,No,None).
% otherwise, No
classify_patterns([execution_pattern(Id,_Cost,_Original_conds,_Conditions)|More],Cond,Yes,[Id|No],None):-
	classify_patterns(More,Cond,Yes,No,None).


%! filter_and_sort_classifiers(+Classifiers:list(classifier),+Ex_pats_ids:list_set,+Conditions:list_set(linear_constraint),-Sorted_classifiers:sorted_list(classifier)) is det
% * keep the classifiers whose condition is in Conditions
% * update the classifiers' annotations witht the execution patterns ids of Ex_pats_ids
% * re-sort the new classifiers
filter_and_sort_classifiers(Classifiers,Ex_pats_ids,Conditions,Sorted_classifiers):-
	include(classifier_condition(Conditions),Classifiers,Classifiers1),
	maplist(update_classifier(Ex_pats_ids),Classifiers1,Classifiers2),
	sort_with(Classifiers2,smaller_heuristic,Sorted_classifiers).
	
classifier_condition(Conditions,classifier(Cond,_Yes,_No,_None,_N1,_N2)):-
	contains_sl(Conditions,Cond).

%! 	update_classifier(+Ex_pats_ids:list_set(int),+Classifier:classifier,-Classifier:classifier) is det
% remove from the annotations all the ids that are not in Ex_pats_ids.
% Update S_Classified and P_Classified
update_classifier(Ex_pats_ids,classifier(Cond,Yes,No,None,_,_),classifier(Cond,Yes2,No2,None2,S_Classified,P_Classified)):-
	intersection_sl(Yes,Ex_pats_ids,Yes2),
	intersection_sl(No,Ex_pats_ids,No2),
	intersection_sl(None,Ex_pats_ids,None2),
	length(Yes2,Nyes),
	length(No2,NNo),
	S_Classified is Nyes+NNo,
	P_Classified is Nyes*NNo.
	
%! smaller_heuristic(+Classifier1:classifier,+Classifier2:classifier) is semidet
% order to be used with sort_with/3
smaller_heuristic(classifier(_,_,_,_,_N1,N11),classifier(_,_,_,_,_N2,N22)):-
	N11<N22,!.
smaller_heuristic(classifier(_,_,_,_,N1,N11),classifier(_,_,_,_,N2,N22)):-
	N11=N22,N1<N2.
	

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% simplify conditional  bounds

%! simplify_conditional_bound_precondition(+Cond_ub:(cost_expression,list(polyhedron)),-Cond_ub1:(cost_expression,list(polyhedron))) is det
% given a conditional  bound defined by a cost and a disjunction of preconditions
% try to compress some of those preconditions into simpler ones
simplify_conditional_bound_precondition((Cost,List_preconditions),(Cost,List_preconditions1)):-
	maplist(length,List_preconditions,Lengths),
	% make all the constraints have standard representation so they can be sintactically compared
	maplist(maplist(normalize_constraint),List_preconditions,List_normalized_preconditions),
	% sort the linear constraints inside each precondition
	maplist(from_list_sl,List_normalized_preconditions,List_preconditions_set),
	% associate the preconditions with their length
	% we can only compress preconditions of similar length
	maplist(tuple,Lengths,List_preconditions_set,Pairs),
	find_all_similarities(Pairs,[],List_preconditions1).

%! find_all_similarities(+Precondition_pairs:list((int,list_set(linear_constraint))),+Accum:list((int,list_set(linear_constraint))),-Simplified_preconditions:list(list_set(linear_constraint))) is det
% Try all the possibilities of compressing preconditions.
% for efficiency use a kind of set-of-support (SOS) strategy. 
%  * If we tried a precondition with every other and failed, we move it to the Accum
%    so we don't try again. 
%  * If we succeed in compressing one precondition, the result is put in Precondition_pairs.
%  * We finish when Precondition_pairs is empty
find_all_similarities([],Accum,Simplified_preconditions):-
	maplist(tuple,_Lengths,Simplified_preconditions,Accum).

find_all_similarities([Precondition_pair|Preconditions_pairs],Accum,Simplified_preconditions):-
	(find_similar(Preconditions_pairs,Precondition_pair,Joined,Preconditions_pairs1)->
	     find_all_similarities([Joined|Preconditions_pairs1],Accum,Simplified_preconditions)
	;
	 (find_similar(Accum,Precondition_pair,Joined,Accum1)-> 
		find_all_similarities([Joined|Preconditions_pairs],Accum1,Simplified_preconditions)
	 ;
	    find_all_similarities(Preconditions_pairs,[Precondition_pair|Accum],Simplified_preconditions)
	    )
	    ).
%! find_similar(+Preconditions:list((int,list_set(linear_constraint))),+N_Precondition:(int,list_set(linear_constraint)),-Compressed:(int,list_set(linear_constraint)),-Preconditions1:list((int,list_set(linear_constraint)))) is semidet
% succeeds if it finds a precondition in Preconditions that can be compressed with N_Precondition
% it returns the compressed precondition and the rest Preconditions1
find_similar([(N1,Prec1)|Preconditions],(N,Precondition),Compressed,Preconditions):-
	%try to compress preconditions of similar length
	Diff is abs(N1-N),
	Diff=<1,
	difference_sl(Prec1,Precondition,Constraints1),
	difference_sl(Precondition,Prec1,Constraints2),
	% such that the different constraints are at most 2
	length(Constraints1,Diff_1),
	length(Constraints2,Diff_2),
	Diff_1=<2,Diff_2=<2,
	% and they are either complementary or contiguous
	contiguous_linear_constraint(Constraints1,Constraints2,Joined_constraints),!,
	difference_sl(Precondition,Constraints2,Precondition1),
	union_sl(Joined_constraints,Precondition1,Joined),
	length(Joined,N_joined),
	Compressed=(N_joined,Joined).
	
find_similar([Prec1|Preconditions],Precondition,Joined,[Prec1|Preconditions1]):-
	find_similar(Preconditions,Precondition,Joined,Preconditions1).
	
%! contiguous_linear_constraint(+Conds:list(linear_constraint),+Conds2:list(linear_constraint),-Joined:list(linear_constraint)) is semidet
% check if the Conds and Conds2 are complementary (Cond or Cond2)= true
% or contiguous  (Cond or Cond2)= Joined
	
% case complementary constraints X>=Y or X<Y = true	
contiguous_linear_constraint([Cond],[Cond2],[]):-
	negate_condition(Cond,CondNeg),
	CondNeg==Cond2,!.
%case contiguous with equality: X=Y or X>Y = X>=Y
contiguous_linear_constraint([X=Y],[A >= B],[Joined]):-
	negate_condition(X=Y,or(Cond1Neg1,Cond1Neg2)),
	(
	Cond1Neg1==(A >= B)
	;
	Cond1Neg2==(A >= B)
	),
	 normalize_constraint( A+1 >= B,Joined),!.
%case contiguous with equality, the other possibility
contiguous_linear_constraint([A >= B],[X=Y],Joined):-
	contiguous_linear_constraint([X=Y],[A >= B],Joined).
% contiguous to interval: (A>c1 and A=<c2)  or A=c1 = (A>=c1 and A=<c2)
% and similar
contiguous_linear_constraint([A >= B,A1 >= B1],[Cond2],Joined):-
	normalize_constraint(A+A1 >= B+B1, 0 >= Negative),
	Negative < 0,
	(
	contiguous_linear_constraint([A >= B],[Cond2],Joined0),
	 Joined=[A1 >= B1|Joined0]
	 ;
	 contiguous_linear_constraint([A1 >= B1],[Cond2],Joined0),
	 Joined=[A >= B|Joined0]
	),!.
	
contiguous_linear_constraint([C1],[C2,C3],Joined):-
	contiguous_linear_constraint([C2,C3],[C1],Joined).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% for debugging

append_ub_cond((_,Paths),Paths1,Paths2):-
	append(Paths,Paths1,Paths2).
	
%! check_2t2_incompatibility(Css:list(polyhedron)) is semidet
% succeeds if every polyhedron in Css is incompatible with any other
check_2t2_incompatibility([]).
check_2t2_incompatibility([Cs|More]):-
	maplist(incompatible(Cs),More),
	check_2t2_incompatibility(More).

incompatible(Cs,Cs1):-
	append(Cs,Cs1,Cs_all),
	\+nad_consistent_constraints(Cs_all).		

