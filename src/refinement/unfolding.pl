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

:- module(unfolding,[reinforce_equations_with_forward_invs/2,
			   unfold_calls/2,
			   remove_terminating_non_terminating_chains/2,
			   compress_chains_execution_patterns/2]).

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
		 
			 
:- use_module('../IO/output',[print_chain_simple/1,print_warning/2]).
:- use_module('../IO/params',[get_param/2]).	
:- use_module('../utils/cofloco_utils',[
	bagof_no_fail/3,
	assign_right_vars/3,
	tuple/3,
	merge_implied_summaries/3]).
:- use_module('../utils/polyhedra_optimizations',[
	nad_consistent_constraints_group_aux/1,
	slice_relevant_constraints_and_vars/5,
	group_relevant_vars/4,
	nad_normalize_polyhedron/2]).

:- use_module(stdlib(utils),[ut_split_at_pos/4]).
:- use_module(stdlib(numeric_abstract_domains),[nad_consistent_constraints/1,nad_lub/6,
			            nad_normalize/2,
			            nad_entails/3,
						nad_list_lub/2,nad_glb/3,nad_project/3]).
:- use_module(stdlib(set_list),[from_list_sl/2,unions_sl/2,union_sl/3,is_subset_sl/2]).
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).


:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(terms)).
%! reinforce_equations_with_forward_invs(Head:term,RefCnt:int) is det
%  adds the information inferred from the forward invariants to the cost equations' definition
%  of a SCC. At the same time, it computes the scc_forward_invariant of the  SCCs that are called from the target SCC.
%  This operation advances the refinement counter RefCnt.
reinforce_equations_with_forward_invs(Head,RefCnt):-
	loop_ph(Head,(Id_loop,RefCnt),_,_,Eqs,_),
	bagof_no_fail(Inv,E1^E2^Lg^Id_loop^(
			   forward_invariant(Head,([Id_loop|E1],RefCnt),E2,Inv);
			   (forward_invariant(Head,([Lg|E1],RefCnt),E2,Inv),member(Id_loop,Lg))
	       ),Invs),
	nad_list_lub(Invs,Eq_inv),	
	maplist(reinforce_equation(Head,RefCnt,Eq_inv),Eqs),
	fail.
reinforce_equations_with_forward_invs(_Head,_RefCnt).

reinforce_equation(Head,RefCnt,Eq_inv,Eq_id):-
	RefCnt_1 is RefCnt+1,
	eq_ph(Head,(Eq_id,RefCnt),E_Exp,NR_Calls,R_Calls,Calls,P_Size,Term_flag),
	nad_glb(Eq_inv,P_Size,P_Size_new),
	assertz(db:eq_ph(Head,(Eq_id,RefCnt_1),E_Exp,NR_Calls,R_Calls,Calls,P_Size_new,Term_flag)),
	reinforce_calls(NR_Calls,RefCnt,P_Size_new).

%! reinforce_calls(Calls:list(term),RefCnt:int,Cs:polyhedron) is det
% for each call term in the list, add the projected Cs to the corresponding SCC forward invariant
reinforce_calls([],_,_Cs).
reinforce_calls([Head|More],RefCnt,Cs):-
	Head=..[_|Vars],
	nad_project(Vars,Cs,Inv),
	reinforce_scc_forward_inv(Head,RefCnt,Inv),
	reinforce_calls(More,RefCnt,Cs).

%! reinforce_scc_forward_inv(Head:term,RefCnt:int,Cs:polyhedron) is det
% if the is already a SCC forward invariant, we relax it with the new conditions Cs.
% if there is none, we initialize it with the given conditions Cs.
%/*
reinforce_scc_forward_inv(Head,RefCnt,Inv):-
	retract(invariants:scc_forward_invariant(Head,RefCnt,Inv_2)),!,
		Head=..[_|Vars],
	nad_lub(Vars,Inv,Vars,Inv_2,Vars,New_Inv),
	assertz(invariants:scc_forward_invariant(Head,RefCnt,New_Inv)).
reinforce_scc_forward_inv(Head,RefCnt,Inv):-
	assertz(invariants:scc_forward_invariant(Head,RefCnt,Inv)).
%*/
/*	
reinforce_scc_forward_inv(Head,RefCnt,Inv):-
	retract(scc_forward_invariant(Head,RefCnt,Inv_2)),!,
	Head=..[_|Vars],
	nad_lub(Vars,Inv,Vars,Inv_2,Vars,New_Inv),
	assertz(scc_forward_invariant(Head,RefCnt,[])).
reinforce_scc_forward_inv(Head,RefCnt,Inv):-
	assertz(scc_forward_invariant(Head,RefCnt,[])).
*/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! unfold_calls(Head:term,RefCnt:int) is det
% unfold each cost equation. 
unfold_calls(Head,RefCnt):-
	New_RefCnt is RefCnt+1,
	eq_ph(Head,(Id,RefCnt),Cost,Base_Calls,Rec_Calls,Total_Calls,Cs,Term_flag),
	unfold_calls_aux(Total_Calls,Base_Calls,Head,New_RefCnt,Cost,Rec_Calls,[],[],Cs,Term_flag,Id),
	fail.
unfold_calls(_,_).


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
unfold_calls_aux([],[],Head,New_RefCnt,Cost,R_Calls,New_B_Calls,New_T_Calls,Cs,Term_flag,Id):-
	%get the calls in the right order
	reverse(New_B_Calls,New_B_Calls2),
	reverse(New_T_Calls,New_T_Calls2),
	nad_normalize_polyhedron(Cs,Cs_normalized),
	Cs_normalized\==[0=1],
	add_eq_ph(eq_ph(Head,New_RefCnt,Cost,New_B_Calls2,R_Calls,New_T_Calls2,Cs_normalized,Term_flag),Id),
	fail.


unfold_calls_aux([R_Call|More],B_Calls,Head,RefCnt,Cost,Rec_Calls,New_B_Calls,New_T_Calls,Cs,Term_flag,Id):-
	unifiable(R_Call,Head,_),
	unfold_calls_aux(More,B_Calls,Head,RefCnt,Cost,Rec_Calls,New_B_Calls,[R_Call|New_T_Calls],Cs,Term_flag,Id).

unfold_calls_aux([Base_Call|More],[Base_Call|MoreB],Head,RefCnt,Cost,R_Calls,New_B_Calls,New_T_Calls,Cs,Term_flag,Id):-
	\+unifiable(Base_Call,Head,_),
	%if the chains have been compressed there is a external_call_pattern and we check those instead of 
	% the backward invariants
	(external_call_pattern(Base_Call,_,_,_,_)->
	   external_call_pattern(Base_Call,(External_pattern_id,RefCnt),Terminating,_,Head_Pattern),
	   Id_call=external_pattern(External_pattern_id)
	   ;  
	   backward_invariant(Base_Call,(Chain,RefCnt),_Hash_inv,Head_Pattern),
	   Id_call=chain(Chain),
	   (non_terminating_chain(Base_Call,RefCnt,Chain)->
	      Terminating=non_terminating
	      ;
	      Terminating=terminating
	      )
	),
	(Head_Pattern=[]->
	    Total_Cons=Cs
	    ;
	append(Head_Pattern,Cs,Total_Cons),
	term_variables(Head_Pattern,Relevant_vars_ini),
	slice_relevant_constraints_and_vars(Relevant_vars_ini,[],Total_Cons,_,Relevant_Cons),
	nad_consistent_constraints_group_aux(Relevant_Cons)
	),
	or_terminating_flag(Term_flag,Terminating,Term_flag2),
	%if the calls are sequential and one does not terminate, we can eliminate further calls
	((get_param(assume_sequential,[]),Terminating=non_terminating)->
	     unfold_calls_aux([],[],Head,RefCnt,Cost,[],[(Base_Call,Id_call)|New_B_Calls],
			    [(Base_Call,Id_call)|New_T_Calls],Total_Cons,Term_flag2,Id)
	   ;
	     unfold_calls_aux(More,MoreB,Head,RefCnt,Cost,R_Calls,[(Base_Call,Id_call)|New_B_Calls],
			    [(Base_Call,Id_call)|New_T_Calls],Total_Cons,Term_flag2,Id)
	).

	
or_terminating_flag(terminating,terminating,terminating):-!.
or_terminating_flag(_,_,non_terminating):-!.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%! remove_terminating_non_terminating_chains(Head:term,RefCnt:int) is det
% we try to discard the non-terminating chains
% if there are not terminating chains we print a warning
remove_terminating_non_terminating_chains(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	\+non_terminating_chain(Head,RefCnt,Chain),!,%Check if there are terminating chains
	remove_terminating_non_terminating_chains_1(Head,RefCnt).
remove_terminating_non_terminating_chains(Head,RefCnt):-
	print_warning('Warning: no base case found for predicate~n',Head),
	remove_terminating_non_terminating_chains_1(Head,RefCnt).
	

remove_terminating_non_terminating_chains_1(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	remove_terminating_non_terminating_2([],Head,Chain,New_chain),
	New_chain\=Chain,
	retract(chains:chain(Head,RefCnt,Chain)),
	(New_chain\=none->
	   assertz(chains:chain(Head,RefCnt,New_chain))
	   ;
	   true
	 ),
	numbervars(Head,0,_),
	(get_param(debug,[])->
	 format('Discarded unfeasible chain ',[]),
	 print_chain_simple(Chain),
	 format('(Non-terminating chain proved terminating)~n',[]),
	 (New_chain\=none->
	   format('Remaining chain: ',[]),
	   print_chain_simple(New_chain),nl
	   ;
	   true
	   )
	 ;
	 true),
	fail.
remove_terminating_non_terminating_chains_1(_,_).

remove_terminating_non_terminating_2(_Prev_chain,_Head,Chain,Chain):-
	reverse(Chain,[Last_phase|_Chain_rev]),
	number(Last_phase),!.

remove_terminating_non_terminating_2(Prev_chain,Head,Chain,New_chain):-
	reverse(Chain,[Last_phase|Chain_rev]),
	Last_phase=[_|_],!,
	append([Last_phase|Chain_rev],Prev_chain,Complete_prev_chain),
	(termination_argument(Head,Complete_prev_chain,yes,_Term_arg)->
	     New_chain=none
	;
	     New_chain=Chain
	).
remove_terminating_non_terminating_2(Prev_chain,Head,Chain,New_chain):-
	  reverse(Chain,[Last_phase|Chain_rev]),
	  Last_phase=multiple(Mult_phase,Tails),!,
	  append([Mult_phase|Chain_rev],Prev_chain,Complete_prev_chain),
	  (termination_argument(Head,Complete_prev_chain,yes,_Term_arg)->
	     delete(Tails,[],Tails2)
	   ; 
	     Tails2=Tails
	  ),
	  maplist(remove_terminating_non_terminating_2(Complete_prev_chain,Head),Tails2,New_tails),
	  exclude(is_none,New_tails,New_tails_excluded),
	  (New_tails_excluded=[]->
	      New_chain=none
	      ;
	      reverse([multiple(Mult_phase,New_tails_excluded)|Chain_rev],New_chain)
	  ).
	      
	     
is_none(none).	    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%! compress_chains_execution_patterns(Head:term,RefCnt:int) is det 
% obtain all the backward invariants and chains of Head and join all the chains
% that have the same invariant.
% Save those compressed invariants as external execution patterns that will be used in the unfolding
% of the callers.
%
% Compress terminating and non-terminating chains separately
compress_chains_execution_patterns(Head,RefCnt):-	
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
	
	