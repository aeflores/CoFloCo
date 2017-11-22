/** <module> invariants

This module computes different kinds of invariants for the chains:


  * backward_invariant/4: An invariant that relates the variables of the head of a cost equation and is computed
    backwards, form the base case of the chain to the first phase. This invariant reflects the input-output relation
    and the necessary conditions for a chain to be called
  * forward_invariant/4: An invariant that relates the variables of the head of a cost equation and is computed
    forwards, form the first phase up  to the base case. This invariant propagates any precodition we might have
    and also information from the first phases to later phases
  * scc_forward_invariant/3: This invariant reflects the preconditions of a SCC.
    It is inferred in base of all the calls to such SCC.
    In the future we could consider multiple invariants scc_forward_invariant/3, one for each call to the SCC
    to increase precission
  * phase_transitive_closure/5:  The transitive closure of a phase
  
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

:- module(invariants,[
			  compute_backward_invariants/3,
			%  compute_phase_transitive_invariants/2,
		      compute_forward_invariants/4,
		      
		      back_invs_get/3,
		      fwd_invs_get/3,
		      loop_invs_get/3,
		      ce_invs_get/3,
		      
		      fwd_invs_get_infeasible_prefixes/2,
		      back_invs_get_infeasible/2,
		      
		      fwd_invs_get_loop_invariants/2,
		      back_invs_get_loop_invariants/2,
		      loop_invs_to_CE_invs/3
		     ]).


:- use_module(chains,[chain/3,get_reversed_chains/3]).
:- use_module(loops,[
	loop_get_CEs/2,
	loops_get_head/2,
	loops_get_list/3,
	loops_get_list_fresh/3,
	loops_get_loop/3,
	loops_get_loop_fresh/3,
	loops_split_multiple_loops/2]).

:- use_module('../IO/params',[get_param/2]).
:- use_module('../utils/cofloco_utils',[assign_right_vars/3,zip_with_op2/4,zip_with_op2/4,ground_copy/2]).
:- use_module('../utils/polyhedra_optimizations',[nad_project_group/3,
					nad_consistent_constraints_group_aux/1,
					nad_is_bottom/1,
					group_relevant_vars/4,
					nad_normalize_polyhedron/2]).
:- use_module('../utils/polyhedra_optimizations').	
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map)).

:- use_module(stdlib(counters),[counter_increase/3]).
:- use_module(stdlib(numeric_abstract_domains),[
	nad_glb/3,
	nad_list_glb/2,
	nad_project/3, 
	nad_entails/3, 
	nad_lub/6,
	nad_list_lub/2, 
	nad_widen/5,
	nad_normalize/2,
	nad_false/1,nad_consistent_constraints/1]).
:- use_module(stdlib(utils),[ut_append/3,ut_flat_list/2, ut_member/2, ut_list_to_dlist/2,ut_split_at_pos/4]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).

:- use_module(stdlib(polyhedra_ppl)).
:- use_module(stdlib(numvars_util),[to_numbervars_nu/4]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(terms)).
:-use_module(library(lambda)).


fwd_invs_empty(fwd_inv(Head,Cs),fwd_invs(Head,[([],(Cs,Cs))])).

fwd_invs_get(fwd_invs(Head,Map),Prefix,Inv_fresh):-
	lookup_lm(Map,Prefix,(Cs_star,Cs_plus)),
	copy_term(inv(Head,Cs_star,Cs_plus),Inv_fresh).
	

fwd_invs_add(fwd_invs(Head,Map),Prefix,inv(Head,Cs_star,Cs_plus),fwd_invs(Head,Map2)):-
	insert_lm(Map,Prefix,(Cs_star,Cs_plus),Map2).	


fwd_invs_get_infeasible_prefixes(fwd_invs(_Head,Map),Prefixes):-
	include(\Pair^(
					Pair=(_Key,(_,Cs_plus)),
					nad_is_bottom(Cs_plus)
					),Map,Unfeasible),
	keys_lm(Unfeasible,Prefixes).
	


back_invs_get_infeasible(back_invs(_Head,Map),Chains):-
	include(\Pair^(
					Pair=(_Key,(_,Cs_plus)),
					nad_is_bottom(Cs_plus)
					),Map,Unfeasible),
	keys_lm(Unfeasible,Chains).

back_invs_empty(Head,back_invs(Head,[([],([],[]))])).

back_invs_get_head(back_invs(Head,_),Head).

back_invs_get(back_invs(Head,Map),Chain,Inv_fresh):-
	lookup_lm(Map,Chain,(Cs_star,Cs_plus)),
	copy_term(inv(Head,Cs_star,Cs_plus),Inv_fresh).

back_invs_add(back_invs(Head,Map),Chain,inv(Head,Cs_star,Cs_plus),back_invs(Head,Map2)):-
	insert_lm(Map,Chain,(Cs_star,Cs_plus),Map2).	

inv_is_bottom(inv(_Head,_Cs_star,Cs_plus)):-
	nad_is_bottom(Cs_plus).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
loop_invs_empty(Head,loop_invs(Head,[])).

loop_invs_get(loop_invs(Head,Map),Loop,Inv_fresh):-
	lookup_lm(Map,Loop,Cs),
	copy_term(inv(Head,Cs),Inv_fresh).


fwd_invs_get_loop_invariants(fwd_invs(Head,Map),Loop_fwd_invs):-
	loop_invs_empty(Head,Empty_loop_invs),
	foldl(loop_fwd_invs_accum(Head),Map,Empty_loop_invs,Loop_fwd_invs).
	
back_invs_get_loop_invariants(back_invs(Head,Map),Loop_back_invs):-
	loop_invs_empty(Head,Empty_loop_invs),
	foldl(loop_fwd_invs_accum(Head),Map,Empty_loop_invs,Loop_back_invs).
		
loop_fwd_invs_accum(_Head,([],_),Loop_fwd_invs,Loop_fwd_invs):-!.

loop_fwd_invs_accum(Head,([Phase|_],(Cs_star,_)),Loop_invs,Loop_invs2):-
	(number(Phase)->
		loop_fwd_invs_accum_1(Head,Cs_star,Phase,Loop_invs,Loop_invs2)
		;
		foldl(loop_fwd_invs_accum_1(Head,Cs_star),Phase,Loop_invs,Loop_invs2)
	).
loop_fwd_invs_accum_1(Head,Cs,Loop,loop_invs(Head,Map),loop_invs(Head,Map2)):-
	Head=..[_Name|Vars],
	(lookup_lm(Map,Loop,Cs2)->
		nad_lub(Vars,Cs,Vars,Cs2,Vars,Cs3),
		insert_lm(Map,Loop,Cs3,Map2)
		;
		insert_lm(Map,Loop,Cs,Map2)
	).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
ce_invs_empty(Head,ce_invs(Head,[])).

ce_invs_get(ce_invs(Head,Map),CE,Inv_fresh):-
	lookup_lm(Map,CE,Cs),
	copy_term(inv(Head,Cs),Inv_fresh).
	
loop_invs_to_CE_invs(loop_invs(Head,Loop_invs_map),Loops,CE_invs):-
	ce_invs_empty(Head,CE_invs_empty),
	foldl(add_CE_invs(Head,Loops),Loop_invs_map,CE_invs_empty,CE_invs).

add_CE_invs(Head,Loops,(Loop_id,Cs),CE_invs,CE_invs2):-
	loops_get_loop(Loops,Loop_id,Loop),
	loop_get_CEs(Loop,Eqs),
	foldl(add_CE_invs_1(Head,Cs),Eqs,CE_invs,CE_invs2).
	
add_CE_invs_1(Head,Cs,Eq_id,ce_invs(Head,Map),ce_invs(Head,Map2)):-
	insert_lm(Map,Eq_id,Cs,Map2).
	
%! widening_frequency(-N:int) is det
% how often widening is performed
widening_frequency(1).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_backward_invariants(+Head:term,+RefCnt:int) is det
% for each chain, try to compute the backward invariant.
% if it fails it is because it is not feasible and we can discard the chain
% otherwise we store the invariant

compute_backward_invariants(Loops,chains(_,Chains),Backward_invs):-
	loops_get_head(Loops,Head),
	back_invs_empty(Head,Empty_backward_inv),
	foldl(\Chain_l^compute_backward_invariant(Chain_l,Loops,_),Chains,Empty_backward_inv,Backward_invs).	
    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5


%! compute_backward_invariant(+Chain:chain,+Prev_chain:chain,+Head:term,+RefCnt:int,-Entry_pattern:polyhedron) is semidet
% compute the backward invariant of the chain prefix Chain knowing that the rest of the chain is Prev_chain.
% if at any point the invariant is unfeasible (bottom) the predicate fails to indicate that the chain can be removed.

% the case where the invariant is already computed
compute_backward_invariant(Chain,_Loops,Inv,Back_invs,Back_invs):-
	back_invs_get(Back_invs,Chain,Inv),!.

compute_backward_invariant([multiple(Ph,Tails)],Loops,Inv,Back_invs_accum,Back_invs):-!,
	foldl(\Chain_l^Inv_l^compute_backward_invariant(Chain_l,Loops,Inv_l),Tails,Invs,Back_invs_accum,Back_invs1),
	join_invs(Invs,Inv_0),
	(member([],Tails)->
		Divergent=divergent
		;
		Divergent=non_divergent
	),
	compute_backward_invariant_phase(Ph,Divergent,multiple,Loops,Inv_0,Inv),
	back_invs_add(Back_invs1,[multiple(Ph,Tails)],Inv,Back_invs).
	
compute_backward_invariant([Ph|Chain],Loops,Inv,Back_invs_accum,Back_invs):-
	compute_backward_invariant(Chain,Loops,Inv_0,Back_invs_accum,Back_invs_accum2),
	((Ph=[_|_],Chain=[])->
		Divergent=divergent
		;
		Divergent=non_divergent
	),
	compute_backward_invariant_phase(Ph,Divergent,simple,Loops,Inv_0,Inv),
	back_invs_add(Back_invs_accum2,[Ph|Chain],Inv,Back_invs).

join_invs(Invs,inv(Head,Inv_star,Inv_plus)):-
	Invs=[inv(Head,_,_)|_],
	maplist(join_vars_inv(Head),Invs,Invs_star,Invs_plus),
	nad_list_lub(Invs_star,Inv_star),
	nad_list_lub(Invs_plus,Inv_plus).

join_vars_inv(Head,inv(Head,Inv_star,Inv_plus),Inv_star,Inv_plus).
% the base case of the chain, the backward invariant is the cost equation definition
% and the corresponding forward invariant


compute_backward_invariant_phase(_,_,_,_,inv(Head,Inv_star,Inv_plus),inv(Head,Inv_plus,Inv_plus)):-
	inv_is_bottom(inv(Head,Inv_star,Inv_plus)),!.
	
compute_backward_invariant_phase(Base_case,_,_,Loops,_Inv_0,Inv):-
	number(Base_case),
	loops_get_loop_fresh(Loops,Base_case,loop(Head,[],Cs_loop,_)),!,
	Inv=inv(Head,[],Cs_loop).

compute_backward_invariant_phase(Phase,divergent,_,Loops,inv(Head,[],[]),inv(Head,[],Inv_plus)):-!,
	(	number(Phase),
		loops_get_loop_fresh(Loops,Phase,Loop),
		Loops_phase=[Loop]
	;
		loops_get_list_fresh(Loops,Phase,Loops_phase)
	),
	backward_invariant_once(inv(Head,[]),Loops_phase,inv(Head_out,Inv_plus)),
	Head_out=Head.

compute_backward_invariant_phase(Phase,non_divergent,_,Loops,inv(Head,_,Initial_inv),inv(Head_out,Initial_inv,Inv_plus)):-
	number(Phase),!,
	loops_get_loop_fresh(Loops,Phase,Loop),
	backward_invariant_once(inv(Head,Initial_inv),[Loop],inv(Head_out,Inv_plus)),
	Head_out=Head.
	

compute_backward_invariant_phase(Phase,non_divergent,_Simple_multiple,Loops,inv(Head,_,Initial_inv),inv(Head,Inv_star,Inv_plus)):-
	loops_get_list_fresh(Loops,Phase,Loops_phase),
	%(Simple_multiple=simple->
		backward_invariant_fixpoint(after,inv(Head,Initial_inv),Loops_phase,inv(Head_out1,Inv_plus),inv(Head_out2,Inv_star))
	%;
	%		backward_invariant_fixpoint(after,inv(Head,Initial_inv),Loops_phase,inv(Head_out1,Inv_plus),inv(Head_out2,Inv_star))
	%)
	,
	Head_out1=Head,
	Head_out2=Head.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	



%! compute_forward_invariants(Entry_Call:term,RefCnt:int) is det
% for each chain, if none of the suffixes is clearly unfeasible (because we computed it before)
% we try to compute the forward invariant.
% if we fail to compute it, then we remove the chain.
% if we don't fail, we do nothing and the chain is not removed.


	
compute_forward_invariants(Initial_inv,Loops,chains(_,Chains),Forward_invs):-
	fwd_invs_empty(Initial_inv,Empty_forward_inv),
	fwd_invs_get(Empty_forward_inv,[],Initial_inv_internal),
	foldl(\Chain_l^compute_forward_invariant(Chain_l,Loops,[],Initial_inv_internal),Chains,Empty_forward_inv,Forward_invs).

%! compute_forward_invariant(+Chain:chain,+RefCnt:int,?Entry_Call:term,-Inv:inv(term,term,polyhedron)) is det
% given a chain fragment [P1,P2...PN], computes a invariant about the variables at any point during P1.
% This invariant is stored, but the invariant returned is a different one.
% The returned invariant is valid at any point after at least ONE iteration of P1 has been performed.
compute_forward_invariant([],_Loops,_Prefix,_Inv,Fwd_invs,Fwd_invs).


compute_forward_invariant([multiple(Phase,Tails)],Loops,Prefix,Inv,Fwd_invs_accum,Fwd_invs):-!,
	compute_forward_invariant_phase(Phase,Loops,Inv,Inv_new),
	fwd_invs_add(Fwd_invs_accum,[Phase|Prefix],Inv_new,Fwd_invs_accum2),
	(inv_is_bottom(Inv_new)->
		 Fwd_invs=Fwd_invs_accum
		 ;
		foldl(\Chain_l^compute_forward_invariant(Chain_l,Loops,[Phase|Prefix],Inv_new),Tails,Fwd_invs_accum2,Fwd_invs)
	).
	
compute_forward_invariant([Phase|Chain],Loops,Prefix,_Inv,Fwd_invs_accum,Fwd_invs):-
	% This is the case when the forward invariant has already been computed
	fwd_invs_get(Fwd_invs_accum,[Phase|Prefix],Inv2),!,
	(inv_is_bottom(Inv2)->
		 Fwd_invs=Fwd_invs_accum
		 ;
		compute_forward_invariant(Chain,Loops,[Phase|Prefix],Inv2,Fwd_invs_accum,Fwd_invs)
	).

compute_forward_invariant([Phase|Chain],Loops,Prefix,Inv,Fwd_invs_accum,Fwd_invs):-
	compute_forward_invariant_phase(Phase,Loops,Inv,Inv_new),
	fwd_invs_add(Fwd_invs_accum,[Phase|Prefix],Inv_new,Fwd_invs_accum2),
	(inv_is_bottom(Inv_new)->
		 Fwd_invs=Fwd_invs_accum2
		 ;
		compute_forward_invariant(Chain,Loops,[Phase|Prefix],Inv_new,Fwd_invs_accum2,Fwd_invs)
	).


%non-iterative phase
% start from the returned invariant of the suffix chain, store that invariant
% and apply the loops once to obtain the return invariant

compute_forward_invariant_phase(Phase,Loops,inv(Head,_,Inv_initial),inv(Head,Inv_initial,Inv)):-
	number(Phase),!,
	loops_get_loop(Loops,Phase,Loop),
	loops_split_multiple_loops([Loop],Loops_splitted), 
	
	(Loops_splitted=[]->
		%base case
		Loop=loop(Head,[],Cs,_),
		nad_glb(Cs,Inv_initial,Cs2),
		(nad_consistent_constraints(Cs2)->
			Inv=[]
			;
			Inv=[1=0]
		)
	; 
		forward_invariant_once(inv(Head,Inv_initial),Loops_splitted,inv(Head2,Inv)),
		Head2=Head
	).


% start from the returned invariant of the suffix chain, 
% apply the loops once to obtain the return invariant
compute_forward_invariant_phase(Phase,Loops,inv(Head,_,Inv_initial),inv(Head,Inv_star,Inv_plus)):-
	loops_get_list_fresh(Loops,Phase,Loops_phase),
	loops_split_multiple_loops(Loops_phase,Loops_splitted),    
    forward_invariant_fixpoint(inv(Head,Inv_initial),Loops_splitted, inv(Head2, Inv_star)),
    forward_invariant_once(inv(Head2,Inv_star),Loops_splitted,inv(Head3,Inv_plus)),
    Head2=Head,
    Head3=Head .

% Apply the loops forwards or backwards once
forward_invariant_once(Initial_inv,Loops_splitted,inv(Head,Inv_out)):-
	apply_loops_forward(Loops_splitted,Initial_inv,Head,Cs_list),
	nad_list_lub(Cs_list,Inv_out).
	       
apply_loops_forward([],_,_,[]).

apply_loops_forward([linear_loop(Head_loop,Call_loop,Cs_loop)|Loops],inv(Head_inv,Inv),Call,[Cs|Cs_list]):-
       copy_term(linear_loop(Head_loop,Call_loop,Cs_loop),linear_loop(Head_inv,Call,Cs_aux)),
       nad_glb(Inv,Cs_aux,Cs_context),
       Call=..[_|Vars],
       nad_project_group(Vars,Cs_context,Cs),
       apply_loops_forward(Loops,inv(Head_inv,Inv),Call,Cs_list).
       
backward_invariant_once(Initial_inv,Loops,inv(Head,Inv_out)):-
	apply_loops_backward(Loops,Initial_inv,Head,Cs_list),
	nad_list_lub(Cs_list,Inv_out).
	

apply_loops_backward([],_,_,[]).

apply_loops_backward([loop(Head_loop,Calls_loop,Cs_loop,_)|Loops],inv(Call_inv,Inv),Head,[Cs_final|Cs_list]):-
       foldl(get_call_inv,Calls_loop,(Call_inv,Inv,[]),(_,_,Total_inv)),
       nad_glb(Total_inv,Cs_loop,Cs_context),
       Head_loop=..[_|Vars],
       nad_project_group(Vars,Cs_context,Cs),
       copy_term((Head_loop,Cs),(Head,Cs_final)),
       apply_loops_backward(Loops,inv(Call_inv,Inv),Head,Cs_list).

get_call_inv(Call,(Head,Inv_0,Inv),(Head,Inv_0,Total_inv)):-
	copy_term((Head,Inv_0),(Call,Inv2)),
	nad_glb(Inv,Inv2,Total_inv).
	

       
      	   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_loops_transitive_closures(Entry:term,RefCnt:int) is det
% Complete transitive closure of each phase.
compute_loops_transitive_closures(Entry,RefCnt):-
	phase_loop(Phase,RefCnt,Entry,_,_),
	compute_phase_transitive_closure(Phase,RefCnt),
	compute_phase_transitive_star_closure(Phase,RefCnt),
	fail.
compute_loops_transitive_closures(_,_).

compute_phase_transitive_closure(Phase,RefCnt):-
	phase_loop(Phase,RefCnt,Head,Call,Inv_0),
    findall((Head_loop,Calls_loop,Cs_loop),
	    (
	    member(Loop,Phase),
	    loop_ph(Head_loop,(Loop,RefCnt),Calls_loop,Cs_loop,_,_)
	 ),Loops),
	 loops_split_multiple_loops(Loops,Loops_splitted),    
     transitive_closure_invariant_fixpoint(inv(Head,Call,Inv_0),Loops_splitted,inv(Entry_out,Call_out, Trans_closure)),
     add_phase_transitive_closure(Phase,RefCnt,Entry_out,Call_out,Trans_closure).

compute_phase_transitive_star_closure(Phase,RefCnt):-
	phase_transitive_closure(Phase,RefCnt,Head,Call,Inv),
	Head=..[_|Vars_head],
	Call=..[_|Vars_Call],
	phase_loop(Phase,RefCnt,Head,Call,Inv_0),
	nad_project(Vars_head,Inv_0,Inv_0_head),
	maplist(zip_with_op2('='),Vars_head,Vars_Call,Equalities),
	append(Equalities,Inv_0_head,No_iterations_inv),
	nad_list_lub([No_iterations_inv,Inv],Inv_star),
	add_phase_transitive_star_closure(Phase,RefCnt,Head,Call,Inv_star).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Low level fixpoint computations


%Flag is 'before' or 'after', it indicates whether one iteration is assumed at the beginning of the fixpoint or after
backward_invariant_fixpoint(Flag,inv(Head,Inv_0),Loops,inv(Head,Inv_out),inv(Head,Inv_star_out)):-
    low_level_backward_invariant_fixpoint(Flag,inv(Head,Inv_0),Loops,Inv_out,Inv_star_out).
    
forward_invariant_fixpoint(inv(Head,Inv_0),Loops,inv(Head,Inv_out)):-
	low_level_forward_invariant_fixpoint(inv(Head,Inv_0),Loops,Inv_out).

transitive_closure_invariant_fixpoint(inv(Entry,Head,Inv_0),Loops,inv(Entry,Head,Inv_out)):-
   low_level_transitive_closure_invariant_fixpoint(inv(Entry,Head,Inv_0),Loops,Inv_out).

    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%transform the initial invariant and the loops into PPL polyhedra
%we use these polyhedra directly to avoid the overhead cost of translating back and forth

% For each loop we generate a tuple Loop_handle:(Extra_dim,Pre_maps,Post_map,Handle)
% * Extra_dim:int  number extra dimensions that the invariant has to have to be able to combine it with this loop	
% * Pre_maps:list(list(var-var)) list of maps (partial functions) that allow us to transform the invariant into the adequate dimensions
%            -we obtain a transformed invariant for each map and join them together with the loop to apply it
%            -Forward and transitive invariants have only one Pre_map
%            -All functions are total
% * Post_map:list(var-var) a map (partial function) used to transform and eliminate the invariants resulting from applying the loops
%             this function is usually partial
% * Handle:int identifier of the polyhedron object

% we know that the phase is applied at least one time, we can assume this application at the beginning
% or at the end. I believe applyig it at the beginning is problably better for precision
% but it is not correct for multiple recursion. 
% hence, we have the two versions: 
% before: for linear recursion
% after: for multiple recursion
 low_level_backward_invariant_fixpoint(before,inv(Head_inv,Inv),Loops,Inv_plus_out,Inv_star_out):-!,
	to_numbervars_nu( (Head_inv,Inv) , _Vars, (_Head_ground,Inv_0_ground), Dim),
	to_ppl_dim(c, Dim, Inv_0_ground, Inv_0_handle), 
	maplist(get_back_loop_handle,Loops,Loop_handles),
	low_level_apply_loops(Loop_handles,Inv_0_handle,Inv_1_handle),
	%compute the backward invariant
	low_level_invariant_fixpoint(0,Inv_1_handle,Loop_handles,Inv_plus),
	%compute the upper bound of the invariant and the initial invariant
	ppl_Polyhedron_upper_bound_assign(Inv_0_handle,Inv_plus),
	maplist(delete_loop_handle,Loop_handles),
	% obtain the constrants of the resulting polyhedron
	Head_inv=..[_|Vars],
	length(Vars,Dim),
	from_ppl(c , Inv_0_handle, Dim, Vars, Inv_star_out), 
	from_ppl(c , Inv_plus, Dim, Vars, Inv_plus_out), 
	ppl_delete_Polyhedron(Inv_0_handle),
	ppl_delete_Polyhedron(Inv_plus).
	
	
 low_level_backward_invariant_fixpoint(after,inv(Head_inv,Inv),Loops,Inv_plus_out,Inv_star_out):-!,
	to_numbervars_nu( (Head_inv,Inv) , _Vars, (_Head_ground,Inv_0_ground), Dim),
	to_ppl_dim(c, Dim, Inv_0_ground, Inv_0_handle), 
	maplist(get_back_loop_handle,Loops,Loop_handles),
	%compute the backward invariant
	low_level_invariant_fixpoint(0,Inv_0_handle,Loop_handles,Inv_star),
	% apply the minimum iteration afterwards
	low_level_apply_loops(Loop_handles,Inv_star,Inv_plus),
	%compute the upper bound of the invariant and the initial invariant
	maplist(delete_loop_handle,Loop_handles),
	% obtain the constrants of the resulting polyhedron
	Head_inv=..[_|Vars],
	length(Vars,Dim),
	from_ppl(c , Inv_star, Dim, Vars, Inv_star_out), 
	from_ppl(c , Inv_plus, Dim, Vars, Inv_plus_out), 
	ppl_delete_Polyhedron(Inv_star),
	ppl_delete_Polyhedron(Inv_plus).	  


low_level_forward_invariant_fixpoint(inv(Head_inv,Inv),Loops,Inv_out):-
	to_numbervars_nu( (Head_inv,Inv) , _Vars, (_Head_ground,Inv_0_ground), Dim),
	to_ppl_dim(c, Dim, Inv_0_ground, Inv_0_handle), 
	maplist(get_forward_loop_handle,Loops,Loop_handles),
	% call the fixpoint predicate
	low_level_invariant_fixpoint(0,Inv_0_handle,Loop_handles,Inv_final_handle),
	maplist(delete_loop_handle,Loop_handles),
	% obtain the constrants of the resulting polyhedron
	Head_inv=..[_F|Vars],
	from_ppl(c , Inv_final_handle,_, Vars, Inv_out), 
	ppl_delete_Polyhedron(Inv_final_handle).
		
low_level_transitive_closure_invariant_fixpoint(inv(Entry_inv,Head_inv,Inv),Loops,Inv_out):-
	Loops=[Loop1|_More_loops],
	copy_term(Loop1,(Head_inv,Call,_)),
	%Here we do it a little bit differently, the loops' polyhedron have 3 times the variables of the head 
	%Entry,Head and Call so we don't have to transform them every time
	%the first variables (Entry) have no information 
	to_numbervars_nu( (Entry_inv,Head_inv,Call,Inv) , _Vars, (Entry_ground,Head_ground,Call_ground,Inv_0_ground), _Dim),
	Entry_inv=..[F|Vars1],
	Head_inv=..[F|Vars2],
	append(Vars1,Vars2,Vars),
	length(Vars,Dim_inv),
	to_ppl_dim(c, Dim_inv, Inv_0_ground, Inv_0_handle), 
	maplist(get_transitive_loop_handle(Entry_ground,Head_ground,Call_ground),Loops,Loop_handles),
	% call the fixpoint predicate
	low_level_invariant_fixpoint(0,Inv_0_handle,Loop_handles,Inv_final_handle),
	maplist(delete_loop_handle,Loop_handles),
	% obtain the constrants of the resulting polyhedron

	from_ppl(c , Inv_final_handle, _, Vars, Inv_out), 
	ppl_delete_Polyhedron(Inv_final_handle).   



%! low_level_invariant_fixpoint(+Count:int,+Inv:ppl_polyhedron,+Loops:list(loop_handle),-Inv_out:ppl_polyhedron) is det
% This predicate implements a fixpoint computation that apply the loops Loops to Inv iteratively until a fixpoint is reached.
low_level_invariant_fixpoint(Count,Inv,Loops,Inv_out):-
	widening_frequency(Widening_freq),
	low_level_apply_loops(Loops,Inv,NewInv),
	ppl_new_C_Polyhedron_from_C_Polyhedron(Inv,Inv_lub),
	ppl_Polyhedron_upper_bound_assign(Inv_lub,NewInv),


	(ppl_Polyhedron_contains_Polyhedron(Inv, Inv_lub)->
	  ppl_delete_Polyhedron(Inv_lub),
	  ppl_delete_Polyhedron(NewInv),
	  Inv_out=Inv
	;
	 (Count>=Widening_freq ->
	   ppl_Polyhedron_H79_widening_assign(Inv_lub,Inv),
	   ppl_delete_Polyhedron(Inv),
	   ppl_delete_Polyhedron(NewInv),
	   Next_inv=Inv_lub,
	   Count1=0
	 ;
	  Next_inv=Inv_lub,
	  ppl_delete_Polyhedron(NewInv),
	  ppl_delete_Polyhedron(Inv),
	  Count1 is Count+1
	 ),
	 low_level_invariant_fixpoint(Count1,Next_inv,Loops,Inv_out)
	).
	

%! low_level_apply_loops(+Loops:list(loop_handle),+Inv:ppl_polyhedron,-Inv_aux:ppl_polyhedron) is det
% apply a set of loops Loops to the initial invariant Inv and compute the upper bound of their application
% at the end of the predicate only one new ppl_polyhedron is left with the resulting new invariant
low_level_apply_loops(Loops,Inv,Inv_out):-
	maplist(low_level_apply_loop(Inv),Loops,[New_inv|New_invs]),
	foldl(compress_and_delete,New_invs,New_inv,Inv_out).


low_level_apply_loop(Inv,(Extra_dim,Pre_map,Post_map,Loop_handle),Inv_out):-
	ppl_new_C_Polyhedron_from_C_Polyhedron(Inv,Inv_extended),
	ppl_Polyhedron_add_space_dimensions_and_embed(Inv_extended,Extra_dim),
	apply_pre_maps(Pre_map,Inv_extended,Mapped_inv),
	ppl_Polyhedron_intersection_assign(Mapped_inv,Loop_handle),
	apply_post_map(Mapped_inv,Post_map,Inv_out).
	
compress_and_delete(Inv2,Inv,Inv):-
	ppl_Polyhedron_upper_bound_assign(Inv,Inv2),
	ppl_delete_Polyhedron(Inv2).

apply_pre_maps([Map],Inv_extended,Inv_extended):-!,
	ppl_Polyhedron_map_space_dimensions(Inv_extended,Map).

apply_pre_maps([Map|Maps],Inv_extended,Mapped_inv):-
	ppl_new_C_Polyhedron_from_C_Polyhedron(Inv_extended,Inv_extended_cp),
	ppl_Polyhedron_map_space_dimensions(Inv_extended_cp,Map),
	apply_pre_maps(Maps,Inv_extended,Mapped_inv),
	ppl_Polyhedron_intersection_assign(Mapped_inv,Inv_extended_cp),
	ppl_delete_Polyhedron(Inv_extended_cp).
	
apply_post_map(Inv,Map,Inv):-
	ppl_Polyhedron_map_space_dimensions(Inv,Map).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%these predicates take care of creating the loop_handle for the different kind of invariants
	
get_back_loop_handle(loop(Head,Calls,Inv,_),(Extra_dim,Pre_maps,Post_map,Handle)):-
	Calls=[_|_],!,
	ground_copy((Head,Calls,Inv),(Head_gr,Calls_gr,Inv_gr)),
	Head_gr=..[_|Head_vars],
	term_variables(Calls,Call_vars),
	length(Head_vars,N),
	length(Call_vars,Extra_dim),
	foldl(make_complete_map_to_call(Head_gr,Calls_gr),Calls_gr,[],Pre_maps),
	identity_function(Head_vars,Post_map),
	Dim is N+Extra_dim,
	to_ppl_dim(c, Dim, Inv_gr, Handle).	

	
get_forward_loop_handle(linear_loop(Head,Call,Inv),(Extra_dim,[Pre_map],Post_map,Handle)):-
	ground_copy((Head,Call,Inv),(Head_gr,Call_gr,Inv_gr)),
	Head_gr=..[_|Head_vars],
	Call_gr=..[_|Call_vars],
	append(Head_vars,Call_vars,Total_vars),
	length(Head_vars,Extra_dim),
	identity_function(Total_vars,Pre_map),
	make_map_to_call(Call_gr,Head_gr,[],[Post_map]),
	Dim is Extra_dim*2,
	to_ppl_dim(c, Dim, Inv_gr, Handle).		
	
get_transitive_loop_handle(Entry_gr,Head_gr,Call_gr,(Head,Call,Inv),(Extra_dim,[Pre_map],Post_map,Handle)):-
	ground_copy((Head,Call,Inv),(Head_gr,Call_gr,Inv_gr)),
	Head_gr=..[_|Head_vars],
	length(Head_vars,Extra_dim),
	Entry_gr=..[_|Entry_vars],
	Call_gr=..[_|Call_vars],
	ut_flat_list([Entry_vars,Head_vars,Call_vars],All_vars),
	identity_function(All_vars,Pre_map),
	identity_function(Entry_vars,Post_map1),
	make_map_to_call(Call_gr,Head_gr,[],[Post_map2]),
	append(Post_map1,Post_map2,Post_map),
	Dim is Extra_dim*3,
	to_ppl_dim(c, Dim, Inv_gr, Handle).	

delete_loop_handle((_,_,_,Handle)):-
	ppl_delete_Polyhedron(Handle).
	
make_map_to_call(Term,Term2,Maps,[Map|Maps]):-
	Term=..[_|Vars],
	Term2=..[_|Vars2],
	maplist(zip_with_op2('-'),Vars,Vars2,Map).
make_complete_map_to_call(Head,Calls,Call,Maps,[Map|Maps]):-
	Head=..[_|Vars],
	Call=..[_|Vars2],
	maplist(zip_with_op2('-'),Vars,Vars2,Map1),
	maplist(zip_with_op2('-'),Vars2,Vars,Map2),
	append(Map1,Map2,Map3),
	foldl(make_complete_map_to_call_1(Call),Calls,Map3,Map).
make_complete_map_to_call_1(Call,Call,Map,Map):-!.
make_complete_map_to_call_1(_Call,Call2,Map,Map2):-
	Call2=..[_|Vars2],
	identity_function(Vars2,Map1),
	append(Map1,Map,Map2).

identity_function(Vars,Identity):-	
	maplist(zip_with_op2('-'),Vars,Vars,Identity).