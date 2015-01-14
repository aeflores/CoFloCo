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
			   remove_terminating_non_terminating_chains/2]).

:- use_module(chains,[chain/3]).
:- use_module(invariants,[backward_invariant/4,
			 scc_forward_invariant/3,
			 forward_invariant/4
			 ]).
			 		
:- use_module('../db',[eq_ph/7,
		  loop_ph/4,
		  add_eq_ph/3,
		  add_upper_bound/3,	
		  upper_bound/4,
		  non_terminating_stub/2,
		  non_terminating_chain/2]).
:-use_module('../termination_checker',[termination_argument/4]).
				 

			 
:- use_module('../IO/output',[print_chain/2]).
:- use_module('../IO/params',[get_param/2]).	
:- use_module('../utils/cofloco_utils',[bagof_no_fail/3]).
:- use_module('../utils/polyhedra_optimizations',[
	nad_consistent_constraints_group_aux/1,
	slice_relevant_constraints_and_vars/5]).

:- use_module(stdlib(numeric_abstract_domains),[nad_consistent_constraints/1,nad_lub/6,
						nad_list_lub/2,nad_glb/3,nad_project/3]).
:- use_module(stdlib(set_list),[from_list_sl/2]).

%! reinforce_equations_with_forward_invs(Head:term,RefCnt:int) is det
%  adds the information inferred from the forward invariants to the cost equations' definition
%  of a SCC. At the same time, it computes the scc_forward_invariant of the  SCCs that are called from the target SCC.
%  This operation advances the refinement counter RefCnt.
  
reinforce_equations_with_forward_invs(Head,RefCnt):-
	reinforce_base_cases(Head,RefCnt),
	reinforce_loops(Head,RefCnt).

%! reinforce_base_cases(Head:term,RefCnt:int) is det
% reinforce the cost equations that have no recursive calls.
% It adds the upper bound (convex hull) of all the reaching forward invariants to the cost equations conditions
% It also add those conditions to the calls to other SCCs
reinforce_base_cases(Head,RefCnt):-
	eq_ph(Head,(Id,RefCnt),E_Exp,NR_Calls,[],Calls,P_Size),
	bagof(Inv,
			   E1^E2^E3^forward_invariant(Head,([Id|E1],E2),E3,Inv)
	       ,Invs),
	nad_list_lub(Invs,Eq_inv),
	nad_glb(Eq_inv,P_Size,P_Size_new),
	RefCnt_1 is RefCnt+1,
	assertz(eq_ph(Head,(Id,RefCnt_1),E_Exp,NR_Calls,[],Calls,P_Size_new)),
	reinforce_calls(NR_Calls,RefCnt,P_Size_new),
	fail.
reinforce_base_cases(_Head,_RefCnt).

%! reinforce_loops(Head:term,RefCnt:int) is det
% reinforce the cost equations that have recursive calls.
% It adds the upper bound (convex hull) of all the reaching forward invariants to the cost equations conditions
% It also add those conditions to the calls to other SCCs
reinforce_loops(Head,RefCnt):-
	loop_ph(Head,(Id_loop,RefCnt),_,_),
	eq_ph(Head,(Id_loop,RefCnt),E_Exp,NR_Calls,R_Calls,Calls,P_Size),

	bagof_no_fail(Inv,E1^E2^Lg^Id_loop^(
			   forward_invariant(Head,([Id_loop|E1],RefCnt),E2,Inv);
			   (forward_invariant(Head,([Lg|E1],RefCnt),E2,Inv),member(Id_loop,Lg))
	       ),Invs),
	nad_list_lub(Invs,Eq_inv),
	nad_glb(Eq_inv,P_Size,P_Size_new),
	RefCnt_1 is RefCnt+1,
	assertz(eq_ph(Head,(Id_loop,RefCnt_1),E_Exp,NR_Calls,R_Calls,Calls,P_Size_new)),
	reinforce_calls(NR_Calls,RefCnt,P_Size_new),
	fail.
reinforce_loops(_Head,_RefCnt).

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
reinforce_scc_forward_inv(Head,RefCnt,Inv):-
	retract(scc_forward_invariant(Head,RefCnt,Inv_2)),!,
	Head=..[_|Vars],
	nad_lub(Vars,Inv,Vars,Inv_2,Vars,New_Inv),
	assertz(scc_forward_invariant(Head,RefCnt,New_Inv)).
reinforce_scc_forward_inv(Head,RefCnt,Inv):-
	assertz(scc_forward_invariant(Head,RefCnt,Inv)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! unfold_calls(Head:term,RefCnt:int) is det
% unfold each cost equation. 
unfold_calls(Head,RefCnt):-
	New_RefCnt is RefCnt+1,
	eq_ph(Head,(Id,RefCnt),Cost,Base_Calls,Rec_Calls,Total_Calls,Cs),
	(non_terminating_stub(Head,Id)->
	   Term_flag=non_terminating
	;
	   Term_flag=terminating
	),
	unfold_calls_aux_b(Total_Calls,Base_Calls,Head,New_RefCnt,Cost,Rec_Calls,[],[],Cs,Term_flag,Id),
	fail.
unfold_calls(_,_).

%! unfold_calls_aux_b(+Total_calls:list(term),+Base_calls:list(term),+Head:term,+RefCnt:int,+Cost:cost_expression,+R_Calls:list(term),+New_B_Calls:list(term),+New_T_Calls:list(term),+Cs:polyhedron,+Term_flag:flag,+Id:int) is failure
% Unfold calls before the recursive call (if there is one).
% Each call is substituted in a non-deterministic manner by a call to a specific chain.
% the predicate always fail in the end and uses backtracking 
% to generate all the specialized equations with the calls to all the chains.
% 
% When we find the recursive call, we call unfold_calls_aux_a/10 that deals with the calls after the recursive calls.
% If we are assuming that the calls are executed sequentially and we have a call to a chain that is not terminating,
% we remove all the subsequent calls
%
% * Total_calls and Base_calls are call yet to unfold.
% * Cost is the cost of the cost equation that is being unfolded.
% * R_Calls are the recursive calls of the cost equation that is being unfolded.
% * New_T_Calls and New_B_Calls are the unfolded calls.
% * Flag can be 'terminating' or 'non_terminating'
unfold_calls_aux_b([],[],Head,New_RefCnt,Cost,R_Calls,New_B_Calls,New_T_Calls,Cs,Term_flag,Id):-
	%get the calls in the right order
	reverse(New_B_Calls,New_B_Calls2),
	reverse(New_T_Calls,New_T_Calls2),
	add_eq_ph(eq_ph(Head,New_RefCnt,Cost,New_B_Calls2,R_Calls,New_T_Calls2,Cs),Term_flag,Id),
	fail.


unfold_calls_aux_b([R_Call|More],B_Calls,Head,RefCnt,Cost,Rec_Calls,New_B_Calls,New_T_Calls,Cs,Term_flag,Id):-
	unifiable(R_Call,Head,_),
	unfold_calls_aux_a(More,B_Calls,Head,RefCnt,Cost,Rec_Calls,New_B_Calls,[R_Call|New_T_Calls],Cs,Term_flag,Id).

unfold_calls_aux_b([Base_Call|More],[Base_Call|MoreB],Head,RefCnt,Cost,R_Calls,New_B_Calls,New_T_Calls,Cs,Term_flag,Id):-
	\+unifiable(Base_Call,Head,_),
	backward_invariant(Base_Call,(Chain,RefCnt),_Hash_inv,Head_Pattern),
	append(Head_Pattern,Cs,Total_Cons),
	term_variables(Head_Pattern,Relevant_vars_ini),
	slice_relevant_constraints_and_vars(Relevant_vars_ini,[],Total_Cons,_,Relevant_Cons),
	nad_consistent_constraints_group_aux(Relevant_Cons),
	%if the calls are sequential and one does not terminate, we can eliminate further calls
	(non_terminating_chain(Base_Call,Chain) ->
	   (get_param(assume_sequential,[])->
	         unfold_calls_aux_b([],[],Head,RefCnt,Cost,[],[(Base_Call,Chain)|New_B_Calls],
			    [(Base_Call,Chain)|New_T_Calls],Total_Cons,non_terminating,Id)
	   ;
	         unfold_calls_aux_b(More,MoreB,Head,RefCnt,Cost,R_Calls,[(Base_Call,Chain)|New_B_Calls],
			    [(Base_Call,Chain)|New_T_Calls],Total_Cons,non_terminating,Id)
	    
	    )
	;
	   unfold_calls_aux_b(More,MoreB,Head,RefCnt,Cost,R_Calls,[(Base_Call,Chain)|New_B_Calls],
			    [(Base_Call,Chain)|New_T_Calls],Total_Cons,Term_flag,Id)
	).
%! unfold_calls_aux_a(+Total_calls:list(term),+Base_calls:list(term),+Head:term,+RefCnt:int,+Cost:cost_expression,+R_Calls:list(term),+New_B_Calls:list(term),+New_T_Calls:list(term),+Cs:polyhedron,+Term_flag:flag,+Id:int) is failure
% Unfold calls after the recursive call.
% Each call is substituted in a non-deterministic manner by a call to a specific chain.
% the predicate always fail in the end and uses backtracking 
% to generate all the specialized equations with the calls to all the chains.
% 
%
% * Total_calls and Base_calls are call yet to unfold.
% * Cost is the cost of the cost equation that is being unfolded.
% * R_Calls are the recursive calls of the cost equation that is being unfolded.
% * New_T_Calls and New_B_Calls are the unfolded calls.
% * Flag can be 'terminating' or 'non_terminating'
unfold_calls_aux_a([],[],Head,New_RefCnt,Cost,R_Calls,New_B_Calls,New_T_Calls,Cs,Term_flag,Id):-
	reverse(New_B_Calls,New_B_Calls2),
	reverse(New_T_Calls,New_T_Calls2),
	add_eq_ph(eq_ph(Head,New_RefCnt,Cost,New_B_Calls2,R_Calls,New_T_Calls2,Cs),Term_flag,Id),
	fail.

unfold_calls_aux_a([Base_Call|More],[Base_Call|MoreB],Head,RefCnt,Cost,R_Calls,New_B_Calls,New_T_Calls,Cs,Term_flag,Id):-
	backward_invariant(Base_Call,(Chain,RefCnt),_Hash_inv,Head_Pattern),
	append(Head_Pattern,Cs,Total_Cons),
	term_variables(Head_Pattern,Relevant_vars_ini),
	slice_relevant_constraints_and_vars(Relevant_vars_ini,[],Total_Cons,_,Relevant_Cons),
	nad_consistent_constraints_group_aux(Relevant_Cons),
	unfold_calls_aux_b(More,MoreB,Head,RefCnt,Cost,R_Calls,[(Base_Call,Chain)|New_B_Calls],
			    [(Base_Call,Chain)|New_T_Calls],Total_Cons,Term_flag,Id),
	fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%! remove_terminating_non_terminating_chains(Head:term,RefCnt:int) is det
% we try to discard the non-terminating chains
% if there are not terminating chains we print a warning
remove_terminating_non_terminating_chains(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	\+non_terminating_chain(Head,Chain),!,%Check if there are terminating chains
	remove_terminating_non_terminating_chains_1(Head,RefCnt).
remove_terminating_non_terminating_chains(Head,RefCnt):-
	format('Warning: no base case found for predicate~n',Head),
	remove_terminating_non_terminating_chains_1(Head,RefCnt).
	

remove_terminating_non_terminating_chains_1(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	non_terminating_chain(Head,Chain),
	Chain=[Base|_],
	eq_ph(Head,(Base,RefCnt),_,[],[],[],_),%it is really a stub, not a non-terminating call
	termination_argument(Head,Chain,yes,_Term_arg),

	retract(chain(Head,RefCnt,Chain)),
	numbervars(Head,0,_),
	(get_param(debug,[])->
	 format('Discarded unfeasible chain ',[]),
	 print_chain(Head,Chain),
	 format('(Non-terminating chain proved terminating)~n',[])
	 ;
	 true),
	fail.
remove_terminating_non_terminating_chains_1(_,_).
