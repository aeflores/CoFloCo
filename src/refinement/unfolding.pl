/** <module> unfolding

This module allows to propagate the refinement from the outmost SCC to the innermost SCC and backwards.
 
  * reinforce_equations_with_forward_invs/2: adds the information inferred from the forward invariants to the cost equations' definition
  of a SCC. At the same time, it computes the scc_forward_invariant of the  SCCs that are called from the target SCC.
  This operation advances the refinement counter RefCnt.
  * unfold_calls/2: for a given SCC_i, substitute the calls to subsequent SCCs by calls to the refined chains.
  For example, we have a cost equation C(X)=c+D(Y)+C(X') with constraints phi. If the SCC D has 3 chains, we substitute D(Y)
  by calls to each chain D_1(Y),D_2(Y) and D_3(Y).
  We generate three refined equations C(X)=c+D_1(Y)+C(X'), C(X)=c+D_2(Y)+C(X'), C(X)=c+D_3(Y)+C(X') with phi_1, phi_2 and phi_3 where
  phi_i is phi reinforced with the backward invariant of the chain D_1.
  If phi_i is unfeasible, we do not store the refined cost equation.
  
  A possible optimization is to generate new equations according to the different backward invariants instead of the chains.
  That is, if D_2 and D_3 have the same backward invariant, we can generate a single equation instead of two.
  This is applied if -compress_chains is activated
  
  This operation advances the refinement counter RefCnt.
  * remove_terminating_non_terminating_chains/2 remove chains that are non-terminating but their last phase has been proven terminating
  
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

:- module(unfolding,[
	cr_specialize/3,
	cr_compute_external_execution_patterns/4,
	
	external_pattern_set_cost/3,
	external_pattern_cost/2,
	
	external_patterns_head/2,
	external_patterns_get_external_pattern/3,
	external_patterns_apply_to_each/3]).

:- use_module(chains,[
	chain_get_pattern/2,
	chain_get_property/3]).
	
:- use_module(invariants,[back_invs_get/3]).
		 					 
:- use_module('../IO/output',[
		print_chain_simple/1,
		print_warning/2,
		print_or_log/2,
		print_or_log_nl/0]).
		
:- use_module('../IO/params',[get_param/2]).	

:- use_module('../utils/crs',[
	ce_add_property/4,
	cr_empty/2,
	cr_get_ceList_with_id/2,
	cr_head/2,
	cr_add_eq/5,
	crs_range/2,
	crs_get_cr_external_patterns/3]).
	
:- use_module('../utils/cofloco_utils',[merge_implied_summaries/3]).

:- use_module('../utils/polyhedra_optimizations',[
	nad_consistent_constraints_group_aux/1,
	slice_relevant_constraints_and_vars/5,
	group_relevant_vars/4,
	nad_is_bottom/1,
	nad_normalize_polyhedron/2]).

:- use_module(stdlib(utils),[ut_split_at_pos/4]).
:- use_module(stdlib(numeric_abstract_domains),[
	nad_consistent_constraints/1,
	nad_lub/6,
	nad_normalize/2,
	nad_entails/3,
	nad_list_lub/2,
	nad_glb/3,
	nad_project/3]).
	
:- use_module(stdlib(set_list),[
	from_list_sl/2,
	unions_sl/2,
	union_sl/3,
	is_subset_sl/2]).
	
:- use_module(stdlib(list_map),[from_pairs_lm/2]).	
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).


:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(terms)).
:-use_module(library(lambda)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%external_patterns(list(external_pattern))
% external_pattern:= external_pattern(Term_flag,Polyhedron)

%! unfold_calls(Head:term,RefCnt:int) is det
% unfold each cost equation. 
cr_specialize(CR,CRS,CR2):-
	cr_head(CR,Head),
	cr_empty(Head,CR_empty),
	cr_get_ceList_with_id(CR,CEs_with_ids),
	crs_range(CRS,range(_,Next)),
	foldl(specialize_ce(CRS),CEs_with_ids,(CR_empty,Next),(CR2,_)).

specialize_ce(CRS,(Id,CE),(CR_accum,Count),(CR,Count2)):-
	ce_add_property(CE,refined,refined(Id),eq_ref(Head,Cost,Base_calls,_Rec_calls,Total_calls,Cs,Info)),
	maplist(crs_get_cr_external_patterns_instance(CRS),Base_calls,External_patterns),
	findall(Eq,
		specialize_ce_aux(Total_calls,External_patterns,terminating,
		eq(Head,Cost,[],Cs,Info),Eq),
		Eqs),
	foldl(\Eq_l^Pair1^Pair2^
		(
		Pair1=(CR_l,C1),
		Pair2=(CR2_l,C2),
		cr_add_eq(CR_l,C1,Eq_l,CR2_l,C2)	
		),Eqs,(CR_accum,Count),(CR,Count2)).
		
crs_get_cr_external_patterns_instance(CRS,Head,external_patterns(Head,Patts)):-
	crs_get_cr_external_patterns(CRS,Head,Ext_patt),
	copy_term(Ext_patt,external_patterns(Head,Patts)).
	
%! unfold_calls_aux(+Total_calls:list(term),+Base_calls:list(term),+Head:term,+RefCnt:int,+Cost:cost_expression,+R_Calls:list(term),+New_B_Calls:list(term),+New_T_Calls:list(term),+Cs:polyhedron,+Term_flag:flag,+Id:int) is failure
% Unfold calls before the recursive call (if there is one).
% Each call is substituted in a non-deterministic manner by a call to a specific chain.
% the predicate always fail in the end and uses backtracking 
% to generate all the specialized equations with the calls to all the chains.
% 
% If we are assuming that the calls are executed sequentially and we have a call to a chain that is not terminating,
% we remove all the subsequent calls
%
% * Total_calls and Base_calls are call yet to unfold.
% * Cost is the cost of the cost equation that is being unfolded.
% * R_Calls are the recursive calls of the cost equation that is being unfolded.
% * New_T_Calls and New_B_Calls are the unfolded calls.
% * Flag can be 'terminating' or 'non_terminating'
specialize_ce_aux([],[],Term_flag,eq(Head,Cost,Total_calls_rev,Cs,Info),Eq_new_annotated):-
	%get the calls in the right order
	nad_normalize_polyhedron(Cs,Cs_normalized),
	\+nad_is_bottom(Cs_normalized),
	
	reverse(Total_calls_rev,Total_calls),
	partition(is_refined_call,Total_calls,NR_calls,R_calls),
	Eq_new=eq_ref(Head,Cost,NR_calls,R_calls,Total_calls,Cs_normalized,Info),
	ce_add_property(Eq_new,termination,Term_flag,Eq_new_annotated).
	
specialize_ce_aux([R_call|More],External_patterns,Term_flag,eq(Head,Cost,Total_calls_rev,Cs,Info),Eq_new):-
	unifiable(R_call,Head,_),
	specialize_ce_aux(More,External_patterns,Term_flag,eq(Head,Cost,[R_call|Total_calls_rev],Cs,Info),Eq_new).

specialize_ce_aux([Base_call|More],[external_patterns(Base_call,Pattern_map)|MoreB],Term_flag,
	eq(Head,Cost,Calls_accum,Cs,Info),Eq_new):-
	%here is the choice	
	member((Id,Ex_patt),Pattern_map),
	external_pattern_summary(Ex_patt,Cs_patt),
	external_pattern_termflag(Ex_patt,Term_flag_patt),
	nad_glb(Cs_patt,Cs,Cs1),
	Base_call=..[_|Relevant_vars],
	slice_relevant_constraints_and_vars(Relevant_vars,[],Cs,_,Relevant_Cs),
	nad_consistent_constraints_group_aux(Relevant_Cs),

	or_terminating_flag(Term_flag,Term_flag_patt,Term_flag2),
	%if the calls are sequential and one does not terminate, we can eliminate further calls
	(Term_flag2=non_terminating->
		specialize_ce_aux([],[],Term_flag2,	
		eq(Head,Cost,[Id:Base_call|Calls_accum],Cs1,Info),Eq_new)
	;
		specialize_ce_aux(More,MoreB,Term_flag2,	
		eq(Head,Cost,[Id:Base_call|Calls_accum],Cs1,Info),Eq_new)
	).
	
is_refined_call(_Pattern:_Call).	

or_terminating_flag(terminating,terminating,terminating):-!.
or_terminating_flag(_,_,non_terminating):-!.
   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%! compress_chains_execution_patterns(Head:term,RefCnt:int) is det 
% obtain all the backward invariants and chains of Head and join all the chains
% that have the same invariant.
% Save those compressed invariants as external execution patterns that will be used in the unfolding
% of the callers.
%
% Compress terminating and non-terminating chains separately

external_pattern_summary(external_pattern(Properties),Summary):-
	once(member(summary(Summary),Properties)).
external_pattern_termflag(external_pattern(Properties),Term_flag):-
	once(member(termination(Term_flag),Properties)).

external_pattern_cost(external_pattern(Properties),Cost):-
	once(member(cost(Cost),Properties)).	

external_pattern_set_cost(external_pattern(Properties),Cost,external_pattern([cost(Cost)|Properties])).

	
external_patterns_head(external_patterns(Head,_),Head).
external_patterns_get_external_pattern(external_patterns(_,Map),Id,External_pattern):-
	lookup_lm(Map,Id,External_pattern).

external_patterns_apply_to_each(Pred,external_patterns(Head,List),external_patterns(Head,List2)):-
	maplist(Pred,List,List2).
	
cr_compute_external_execution_patterns(Chains,Backward_invs,Compress_param,External_patterns):-	
	Chains=chains(_,Chain_list_annotated),
	maplist(chain_get_pattern,Chain_list_annotated,Chain_list),
	maplist(\Chain^Term_flag^chain_get_property(Chain,termination,Term_flag),Chain_list_annotated,Termination_flags),
	maplist(Head+\Chain_l^Inv_l^back_invs_get(Backward_invs,Chain_l,inv(Head,_,Inv_l)),Chain_list,Chain_summaries),
	cr_compute_external_execution_patterns_1(Compress_param,Head,Chain_list,Chain_summaries,Termination_flags,External_patterns_list),
	from_pairs_lm(External_patterns_list,External_patterns_map),
	External_patterns=external_patterns(Head,External_patterns_map).

cr_compute_external_execution_patterns_1(0,_Head,Chain_list,Chain_summaries,Termination_flags,External_patterns_list):-
		maplist(
		\Summary_l^Term_flag_l^Chain_l^External_pattern_l^(
		External_pattern_l=([Chain_l],external_pattern([termination(Term_flag_l),summary(Summary_l)]))
		
		),Chain_summaries,Termination_flags,Chain_list,External_patterns_list).
		
cr_compute_external_execution_patterns_1(1,_Head,Chain_list,Chain_summaries,Termination_flags,External_patterns_list):-
	maplist(
	\Summary_l^Term_flag_l^Chain_l^External_pattern_l^(
		External_pattern_l=(external_pattern([termination(Term_flag_l),summary(Summary_l)]),Chain_l)
		
		),Chain_summaries,Termination_flags,Chain_list,External_patterns_rev_list),
	% syntactic merging
	from_pair_list_mm(External_patterns_rev_list,Grouped_external_patterns_rev),
	maplist(\Pattern_rev_l^Pattern_l^(
		Pattern_rev_l=(A,B),
		Pattern_l=(B,A)
		),Grouped_external_patterns_rev,External_patterns_list).
	
cr_compute_external_execution_patterns_1(2,Head,Chain_list,Chain_summaries,Termination_flags,External_patterns_list):-
	maplist(
	\Summary_l^Term_flag_l^Chain_l^External_pattern_l^(
		External_pattern_l=((Term_flag_l,Summary_l),Chain_l)
		
		),Chain_summaries,Termination_flags,Chain_list,External_patterns_rev_list),
	% group the partitions according to the chains
	from_pair_list_mm(External_patterns_rev_list,Grouped_external_patterns_rev),
	%split terminating and non-terminating
	partition(\Elem^(Elem=((terminating,_),_)),Grouped_external_patterns_rev,Term_ext_pat,Non_term_ext_pat),
	%merge using implied summaries
	merge_external_pattern_group(Head,Term_ext_pat,Term_ext_pat_merged),
	merge_external_pattern_group(Head,Non_term_ext_pat,Non_term_ext_pat_merged),
	append(Non_term_ext_pat_merged,Term_ext_pat_merged,External_patterns_list).

merge_external_pattern_group(Head,Ext_pat,Ext_pat_merged):-
	maplist(
	Term_flag_l+\External_pattern_l^External_pattern_simple^(
		External_pattern_l=((Term_flag_l,Summary_l),Chains_l),
		External_pattern_simple=(Summary_l,Chains_l)
		
		),Ext_pat,Ext_pat_simple),
	Head=..[_|Vars],
	merge_implied_summaries(Vars,Ext_pat_simple,Ext_pat_simple_merged),
	maplist(
	Term_flag_l+\External_pattern_simple^External_pattern_l^(
		External_pattern_simple=(Summary_l,Chains_l),
		External_pattern_l=(Chains_l,external_pattern([termination(Term_flag_l),summary(Summary_l)]))
		),Ext_pat_simple_merged,Ext_pat_merged).
			

/*
	(reset_scc(Head,Important_vars,Flag)-> 
	   merge_patterns(Head,Important_vars,Flag,Multimap_simplified,Multimap_simplified_2)
	   ;
	  Multimap_simplified_2=Multimap_simplified
	   ),
	findall((Head,(Condition,Chain)),
		(
		backward_invariant(Head,(Chain,RefCnt),_,Condition),
		non_terminating_chain(Head,RefCnt,Chain)
		)
		,Ex_pats_non_terminating),
	
	assign_right_vars(Ex_pats_non_terminating,Head,Ex_pats_non_terminating1),
	
	% group the partitions according to the chains
	from_pair_list_mm(Ex_pats_non_terminating1,Multimap_simplified_non_terminating),
	(reset_scc(Head,Important_vars,Flag)-> 
	   merge_patterns(Head,Important_vars,Flag,Multimap_simplified_non_terminating,Multimap_simplified_non_terminating_2)
	   ;
	  Multimap_simplified_non_terminating_2=Multimap_simplified_non_terminating
	   ),
	
	foldl(save_external_execution_patterns(Head,RefCnt,terminating),Multimap_simplified_2,1,Id_N1),
	foldl(save_external_execution_patterns(Head,RefCnt,non_terminating),Multimap_simplified_non_terminating_2,Id_N1,_).

save_external_execution_patterns(Head,RefCnt,Terminating,(Precondition,Chains),N,N1):-
	add_external_call_pattern(Head,(N,RefCnt),Terminating,Chains,Precondition),
	N1 is N+1.



merge_patterns(Head,Important_vars,strong,Multimap,Multimap_simplified2):-
	Head=..[_|Vars],
	foldl(accum_all_constraints_from_multimap,Multimap,[],All_css),
	from_list_sl(Important_vars,Important_vars_set),
	slice_relevant_constraints_and_vars(Important_vars_set,Vars,All_css,Selected_vars,_),
	maplist(tuple,Invs,_Chains_lists,Multimap),
	maplist(reduce_precondition_to_vars(Selected_vars),Invs,Reduced_invs),
	maplist(tuple,Reduced_invs,Multimap,Multimap_two_levels),	
	from_pair_list_mm(Multimap_two_levels,Multimap_two_levels_compressed),
	maplist(merge_patterns_aux,Multimap_two_levels_compressed,Multimap_simplified2).
	
merge_patterns(_Head,Important_vars,weak,Multimap,Multimap_simplified2):-
	from_list_sl(Important_vars,Important_vars_set),
	maplist(tuple,Invs,_Chains_lists,Multimap),
	maplist(reduce_precondition_to_vars(Important_vars_set),Invs,Reduced_invs),
	maplist(tuple,Reduced_invs,Multimap,Multimap_two_levels),	
	from_pair_list_mm(Multimap_two_levels,Multimap_two_levels_compressed),
	maplist(merge_patterns_aux,Multimap_two_levels_compressed,Multimap_simplified2).	
	
merge_patterns_aux((_,Multimap),(Inv,Chains)):-
	maplist(tuple,Invs,Chains_lists,Multimap),
	nad_list_lub(Invs,Inv),
	unions_sl(Chains_lists,Chains).

accum_all_constraints_from_multimap((Inv,_),Set,Set1):-
	from_list_sl(Inv,Inv_set),
	union_sl(Inv_set,Set,Set1).
		
reduce_precondition_to_vars([],_,[]):-!.
reduce_precondition_to_vars(Vars,Inv,Inv_simplified):-
	nad_project(Vars,Inv,Inv_projected),
	nad_normalize_polyhedron(Inv_projected,Inv_simplified).
	
*/	