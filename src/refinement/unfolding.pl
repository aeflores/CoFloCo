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
			   cr_compute_external_execution_patterns/3]).

:- use_module(chains,[chain/3]).
:- use_module(invariants,[backward_invariant/4,
			 scc_forward_invariant/3,
			 forward_invariant/4
			 ]).
		 		
:- use_module('../db',[eq_ph/8,
		  loop_ph/6,
		  add_eq_ph/2,
		  add_external_call_pattern/5,
		  external_call_pattern/5,
		  reset_scc/3,
		  upper_bound/4,
		  non_terminating_chain/3]).
:-use_module('../termination_checker',[termination_argument/4]).
		 
			 
:- use_module('../IO/output',[
		print_chain_simple/1,
		print_warning/2,
		print_or_log/2,
		print_or_log_nl/0]).
:- use_module('../IO/params',[get_param/2]).	

:- use_module('../utils/crs',[
	cr_empty/2,
	cr_get_ceList_with_id/2,
	cr_head/2,
	cr_add_eq/5,
	crs_range/2]).
	
:- use_module('../utils/cofloco_utils',[
	bagof_no_fail/3,
	assign_right_vars/3,
	tuple/3,
	merge_implied_summaries/3]).
:- use_module('../utils/polyhedra_optimizations',[
	nad_consistent_constraints_group_aux/1,
	slice_relevant_constraints_and_vars/5,
	group_relevant_vars/4,
	nad_is_bottom/1,
	nad_normalize_polyhedron/2]).

:- use_module(stdlib(utils),[ut_split_at_pos/4]).
:- use_module(stdlib(numeric_abstract_domains),[nad_consistent_constraints/1,nad_lub/6,
			            nad_normalize/2,
			            nad_entails/3,
						nad_list_lub/2,
						nad_glb/3,
						nad_project/3]).
:- use_module(stdlib(set_list),[from_list_sl/2,unions_sl/2,union_sl/3,is_subset_sl/2]).
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).


:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(terms)).
:-use_module(library(lambda)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! unfold_calls(Head:term,RefCnt:int) is det
% unfold each cost equation. 
cr_specialize(CR,CRS,CR2):-
	cr_head(CR,Head),
	cr_empty(Head,CR_empty),
	cr_get_ceList_with_id(CR,CEs_with_ids),
	crs_range(CRS,range(_,Next)),
	foldl(specialize_ce(CRS),CEs_with_ids,(CR_empty,Next),(CR2,_)).

specialize_ce(CRS,(Id,eq_ref(Head,Cost,Base_calls,_Rec_calls,Total_calls,Cs,Info)),(CR_accum,Count),(CR,Count2)):-
	maplist(crs_get_cr_external_patterns_instance(CRS),Base_calls,External_patterns),
	findall(Eq,
		specialize_ce_aux(Total_calls,External_patterns,terminating,
		eq(Head,Cost,[],Cs,[refined(Id)|Info]),Eq),
		Eqs),
	foldl(\Eq_l^Pair1^Pair2^
		(
		Pair1=(CR_l,C1),
		Pair2=(CR2_l,C2),
		cr_add_eq(CR_l,C1,Eq_l,CR2_l,C2)	
		),Eqs,(CR_accum,Count),(CR,Count2)).
		
crs_get_external_patterns_instance(CRS,Head,external_patterns(Head,Patts)):-
	crs_get_external_patterns(CRS,Head,Ext_patt),
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
specialize_ce_aux([],[],Term_flag,eq(Head,Cost,Total_calls_rev,Cs,Info),Eq_new):-
	%get the calls in the right order
	nad_normalize_polyhedron(Cs,Cs_normalized),
	\+nad_is_bottom(Cs_normalized),
	
	reverse(Total_calls_rev,Total_calls),
	partition(is_refined_call,Total_calls,NR_calls,R_calls),
	Eq_new=eq_ref(Head,Cost,NR_calls,R_calls,Total_calls,Cs_normalized,[Term_flag|Info]).
	
specialize_ce_aux([R_call|More],External_patterns,Term_flag,eq(Head,Cost,Total_calls_rev,Cs,Info),Eq_new):-
	unifiable(R_call,Head,_),
	specialize_ce_aux(More,External_patterns,Term_flag,eq(Head,Cost,[R_call|Total_calls_rev],Cs,Info),Eq_new).

specialize_ce_aux([Base_call|More],[external_patterns(Base_call,Pattern_map)|MoreB],Term_flag,
	eq(Head,Cost,Calls_accum,Cs,Info),Eq_new):-
	%here is the choice	
	member((Id,external_pattern(Term_flag_patt,Cs_patt)),Pattern_map),

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

cr_compute_external_execution_patterns(CR,Compress_param,External_patterns):-
	findall((Head,(Condition,Chain)),
		(
		backward_invariant(Head,(Chain,RefCnt),_,Condition),
		\+non_terminating_chain(Head,RefCnt,Chain)
		)
		,Ex_pats),
	
	assign_right_vars(Ex_pats,Head,Ex_pats1),
	% group the partitions according to the chains
	from_pair_list_mm(Ex_pats1,Multimap_simplified_aux),
	%join chains more agressively
	((get_param(compress_chains,[N]),N > 1)->
	term_variables(Head,Vars),
	merge_implied_summaries(Vars,Multimap_simplified_aux,Multimap_simplified)
	;
	Multimap_simplified_aux=Multimap_simplified
	),
%TODO: experiments of how to compress chains
%	length(Multimap_simplified,N),
%	Head=..[_|Vars],
%	append(_,[Last],Vars),
%	(N>3-> 
%	   merge_patterns(Head,[],weak,Multimap_simplified,Multimap_simplified_2)
%	   ;
%	  merge_patterns(Head,[Last],strong,Multimap_simplified,Multimap_simplified_2)
%	  ),
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
	
	