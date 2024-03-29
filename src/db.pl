/** <module> db

This module acts as a database that stores:

  * the set of cost equations in different stages of refinement
  * the external call patterns, that summarize the possible call patterns to a refined SCC
  * the loops (which are fragments of cost equations)
  * the generated closed-form bounds

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

:- module(db,[
       init_db/0,
       init_timers/0,
	   add_loop_ph/6,
	   add_phase_loop/5,
	   add_eq_ph/2,
	   add_ground_equation_header/2,
		  
	   eq_refined/2,
	   input_eq/5,	 
	   entry_eq/2,   
	   ground_equation_header/1,
	   reset_scc/3,
	   save_input_output_vars/3,
	   get_input_output_vars/3,
	   get_input_output_arities/3,
	   eq_ph/8,
       loop_ph/6,
	   phase_loop/5,
	   non_terminating_chain/3,	   

	   external_call_pattern/5,
	   add_external_call_pattern/5,
	   
	   upper_bound/4,
	   add_upper_bound/3,
	   external_upper_bound/3,
	   add_external_upper_bound/3,
	   closed_upper_bound/3,
	   closed_lower_bound/3,
	   closed_upper_bound_print/3,
	   closed_lower_bound_print/3,
	   add_closed_upper_bound/3,
	   add_closed_lower_bound/3,
	   single_closed_upper_bound/2,
	   add_single_closed_upper_bound/2,
	   conditional_upper_bound/3,	
	   conditional_lower_bound/3,
	   conditional_bound/3,  
	   add_conditional_bound/3,
	  
       cofloco_aux_entry_name/1
       
]).
:- use_module('IO/params',[get_param/2]).
:- use_module('IO/output',[print_warning/2]).
:- use_module('utils/cofloco_utils',[assign_right_vars/3]).
:- use_module('utils/structured_cost_expression',[strexp_simplify_max_min/2,strexp_to_cost_expression/2]).
:- use_module('utils/cost_expressions',[cexpr_simplify/3]).
:- use_module('refinement/chains',[chain/3]).
:- use_module('refinement/invariants',[backward_invariant/4]).

:- use_module(stdlib(utils),[ut_var_member/2]).
:- use_module(stdlib(counters),[counter_initialize/2,counter_increase/3,counter_get_value/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_entails/3,nad_glb/3,nad_list_lub/2,nad_lub/6,nad_project/3]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_get_info/3,
				 profiling_stop_timer/2,profiling_stop_timer_acum/2]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(terms)).
%! input_eq(?Head:term,?Id:int,-Cost:cost_expression,-Calls:list(term),-Cs:polyhedron)
% stores a cost equation before the pre-processing
:- dynamic input_eq/5. 

%! entry_eq(?Head:term,-Cs:polyhedron)
% @arg Head is the entry point of the program
% @arg Cs is a precondition on the input variables
:- dynamic entry_eq/2. 

%! ground_equation_header(Head:term)
% A ground version of the cost equation header that records the original names of the variables in the input file.
% it is used to print the results according to those names
:- dynamic ground_equation_header/1. 

%! reset_scc(Head:term,Vars:list(var),Type:flag)
% specify that the scc whose header is Head has to be compressed keeping
% only the information related to Vars
% Type can be 'weak' or 'strong' 
:-dynamic reset_scc/3.

%! input_output_vars(Head:term,Vars:list(var),Vars:list(var))
% specify which variables are input and which output
:-dynamic input_output_vars/3.

/**  eq_ph(?Head:term,?Id_RefCnt:(int,equation_id),-Cost:cost_expression,-Non_rec_Calls:list(term),-Rec_Calls:list(term),-Calls:list(term),-Cs:polyhedron,Term_flag:flag)

 stores a cost equation after the preprocessing. 
 The calls are separated into non-recursive and recursive. Calls has all the calls together in the original order
 
 @arg Id_RefCnt represent the 'RefCnt' and the 'id' of the cost equation
 the refinement takes place in phases. 'RefCnt' indicates to which refinement phase the cost equation belongs
 
 Term_flag can be 'terminating' or 'non_terminating'

*/
:- dynamic  eq_ph/8.

%! eq_refined(Original:equation_id,Refined:equation_id)
% record the fact that Refined is a refined version of Original
% this is recorded in order to trace the behavior back to the original representation.
:- dynamic eq_refined/2.

%! loop_ph(?Head:term,?Id_RefCnt:(int,equation_id),-Rec_Calls:list(term),-Cs:polyhedron,Ids:list(equation_id),Term_flag:flag)
% for each recursive equation loop_ph/4 stores the relation between the head and the recursive calls (abstracting the cost and the other calls away)
% Ids is the list of cost equations that correspond to the loop.
%Term_flag can be 'terminating' or 'non_terminating'
:- dynamic  loop_ph/6.

%! phase_loop(?Phase:phase,?RefCnt:int,-Head:term,-Call:term,-Cs:polyhedron)
% a summary of all the loops of a phase (Phase) of the cost equation Head
:- dynamic  phase_loop/5.

%! external_call_pattern(Head:term,Id_RefCnt:(int,int),Terminating:flag,Components:list(Chain),Inv:polyhedron)
% a call pattern of Head defined by Inv that comprises possible calls to the
% chains in Components
:- dynamic external_call_pattern/5.

%! upper_bound(?Head:term,?Chain:chain,-Hash:int,-Cost_structure:cost_structure)
% an cost structure that represents an upper bound of the chain Chain that belongs to the SCC Head.  
% Hash is the hash of part of the cost structure and can be used to compress similar cost structures
:- dynamic upper_bound/4.

%! external_upper_bound(?Head:term,?Precondition_id:int,-Cost_structure:cost_structure)
% an cost structure that represents an upper bound of a call to Head with the precondition
% Precondition_id. 
% Hash is the hash of part of the cost structure and can be used to compress similar cost structures
:- dynamic external_upper_bound/3.

%! closed_upper_bound(?Head:term,?Chain:chain,-Max_strexp:max(list(strexp)))
% an max(list(strexp))  that represents an upper bound of the chain Chain that belongs to the SCC Head.  
:- dynamic closed_upper_bound/3.

%! closed_lower_bound(?Head:term,?Chain:chain,-Min_strexp:min(list(strexp)))
% an min(list(strexp))  that represents an lower bound of the chain Chain that belongs to the SCC Head.  
:- dynamic closed_lower_bound/3.

%! single_closed_upper_bound(?Head:term,-Cost_expression:cost_expression)
% an cost expression that represents an upper bound of the SCC Head.  
:- dynamic single_closed_upper_bound/2.

%! conditional_upper_bound(?Head:term,-Cost_expression:cost_expression,-Preconditions:list(polyhedra))
% Cost_expression is a valid upper bound for any execution of Head that satisfies one of the preconditions in Preconditions
% for all possible chains.
%
% conditional upper bound's preconditions are mutually exclusive among each other and with any other conditional upper bound
:- dynamic conditional_bound/3.

%! non_terminating_chain(?Head:term,RefCnt:int,?Chain:chain)
% It indicates that the chain Chain is non-terminating
% a chain whose last element is iterative is non-terminating
:-dynamic non_terminating_chain/3.



%! init_db is det
% erase the database and initialize counters
init_db:-
	retractall(input_eq(_,_,_,_,_)),
	retractall(entry_eq(_,_)),
	retractall(ground_eq_header(_)),
	
	retractall(reset_scc(_,_,_)),
	retractall(input_output_vars(_,_,_)),
	retractall(eq_ph(_,_,_,_,_,_,_,_)),
	retractall(eq_refined(_,_)),
	retractall(loop_ph(_,_,_,_,_,_)),
	
	retractall(phase_loop(_,_,_,_,_)),
	retractall(external_call_pattern(_,_,_,_,_)),
	retractall(upper_bound(_,_,_,_)),
	retractall(external_upper_bound(_,_,_)),
	retractall(closed_upper_bound(_,_,_)),
	retractall(closed_lower_bound(_,_,_)),
	retractall(single_closed_upper_bound(_,_)),
	retractall(conditional_bound(_,_,_)),
	retractall(non_terminating_stub(_,_)),
	retractall(non_terminating_chain(_,_,_)),
	assert((non_terminating_chain(Head,RefCnt,Chain):-
	            non_terminating_chain_1(Head,RefCnt,Chain),
	            asserta(non_terminating_chain(Head,RefCnt,Chain))
	            ) ),
	counter_initialize(input_eqs,0),
	counter_initialize(aux_vars,0),
	counter_initialize(short_terms,0),
	counter_initialize(ubs,0),
	counter_initialize(eq_ph,0),
	counter_initialize(loop_ph,0),
	counter_initialize(costs,0),
	counter_initialize(compressed_phases1,0),
	counter_initialize(compressed_invs,0),
	counter_initialize(compressed_chains,0).
	
%! init_timers is det
% initialize timers
init_timers:-
	profiling_start_timer(comp_sccs),profiling_stop_timer_acum(comp_sccs,_),
	profiling_start_timer(pe),profiling_stop_timer_acum(pe,_),
	profiling_start_timer(inv),profiling_stop_timer_acum(inv,_),
	profiling_start_timer(unfold),profiling_stop_timer_acum(unfold,_),
	profiling_start_timer(ubs),profiling_stop_timer_acum(ubs,_),
	profiling_start_timer(loop_phases),profiling_stop_timer_acum(loop_phases,_),
	profiling_start_timer(chain_solver),profiling_stop_timer_acum(chain_solver,_),
	profiling_start_timer(equation_cost),profiling_stop_timer_acum(equation_cost,_),
	profiling_start_timer(flatten_loops),profiling_stop_timer_acum(flatten_loops,_),
	profiling_start_timer(compress_or),profiling_stop_timer_acum(compress_or,_),
	profiling_start_timer(solver),profiling_stop_timer_acum(solver,_),
	profiling_start_timer(black_cost),profiling_stop_timer_acum(black_cost,_),
	profiling_start_timer(termination),profiling_stop_timer_acum(termination,_).

%! cofloco_aux_entry_name(-Name:atom) is det
% returns the name of the auxiliary entry point
cofloco_aux_entry_name('$cofloco_aux_entry$').



save_input_output_vars(Head,IVars,OVars):-
  	input_output_vars(Head,IVars2,OVars2),!,
  	((IVars2==IVars,OVars==OVars2)->
  		true
  	;
  		numbervars(Head,0,_),
  		print_warning('Warning: Incoherent annotation ~p and ~p ~n',[input_output_vars(Head,IVars,OVars),input_output_vars(Head,IVars2,OVars2)])
  	).
  	
save_input_output_vars(Head,IVars,OVars):-
  	assertz(input_output_vars(Head,IVars,OVars)).

get_input_output_vars(Head,Ivars,Ovars):-
	input_output_vars(Head,Ivars,Ovars),!.
get_input_output_vars(Head,Ivars,[]):-
	Head=..[_|Ivars].

get_input_output_arities(F/A,Ia,Oa):-
	functor(Head,F,A),
	get_input_output_vars(Head,Ivars,Ovars),
	length(Ivars,Ia),
	length(Ovars,Oa).	
	
non_terminating_chain_1(Head,RefCnt,Chain):-
	chain(Head,RefCnt,Chain),
	reverse(Chain,Chain_rev),
	non_terminating_chain_2(Head,Chain_rev).
	
non_terminating_chain_2(Head,[X|_Chain]):-
	number(X),
	loop_ph(Head,(X,_),_Call,_Cs,_Ids,non_terminating),!.

non_terminating_chain_2(_Head,[X|_Chain]):-
	X=[_|_],!.

non_terminating_chain_2(Head,[multiple(_Phase,Tails)|_Chain]):-
	maplist(reverse,Tails,Tails_rev),
	member(Tail_rev,Tails_rev),
	(
	Tail_rev=[]
	  ;
	non_terminating_chain_2(Head,Tail_rev)
	).
	

%! add_ground_equation_header(+Non_ground:term,+Ground:term) is det
% store the ground term Ground if there is no ground_eq_header that can be unified with Non_ground.
% that is, we store on ground_eq_header per cost equation header
add_ground_equation_header(Non_ground,_Ground):-
	copy_term(Non_ground,Non_ground2),
	ground_equation_header(Non_ground2),!.
	
add_ground_equation_header(_Non_ground,Ground):-
	assertz(ground_equation_header(Ground)).

%! add_eq_ph(+Cost_equation:cost_equation,Previous_eqs:list(equation_id)) is det
% stores the cost equation Cost_equation in the database
% Previous_eqs are the cost equation ids that originated this new cost equation

%the cost equation already exists
%/*
add_eq_ph(eq_ph(Head,0,E_Exp,NR_Calls,R_Calls,Calls,P_Size,Term_flag),Previous_eqs) :-
	eq_ph(Head,(Id,0),E_Exp,NR_Calls,R_Calls,Calls,P_Size2,Term_flag),
	term_variables((P_Size,P_Size2),All_vars),
	(P_Size==P_Size2
	;
	 nad_entails(All_vars,P_Size,P_Size2)
	 ;
	 nad_entails(All_vars,P_Size2,P_Size),
	 retract(eq_ph(Head,(Id,0),E_Exp,NR_Calls,R_Calls,Calls,P_Size2,Term_flag)),
	 assertz(eq_ph(Head,(Id,0),E_Exp,NR_Calls,R_Calls,Calls,P_Size,Term_flag)) 
	 ),!,
	retract(eq_refined(Previous_eqs1,Id)),
	append(Previous_eqs,Previous_eqs1,Previous_eqs2),
	assertz(eq_refined(Previous_eqs2,Id)).
%*/
add_eq_ph(eq_ph(Head,RefCnt,E_Exp,NR_Calls,R_Calls,Calls,P_Size,Term_flag),Previous_eqs) :-
	counter_increase(eq_ph,1,Id),
	assertz(eq_ph(Head,(Id,RefCnt),E_Exp,NR_Calls,R_Calls,Calls,P_Size,Term_flag)),
	assertz(eq_refined(Previous_eqs,Id)).	
	  
%! add_loop_ph(+Head:term,+RefCnt:int,+Calls:list(term),+Cs:polyhedron,+Ids:list(equation_id),Term_flag:flag) is det
% stores the loop corresponding to the cost equations Ids in the database
add_loop_ph(Head,RefCnt,Calls,Cs, Ids,Term_flag) :-
	counter_increase(loop_ph,1,Id),
	assertz(loop_ph(Head,(Id,RefCnt),Calls,Cs,Ids,Term_flag)).
	
%! add_phase_loop(+Phase:phase,+RefCnt:int,+Head:term,+Call:term,+Cs:polyhedron) is det
% stores the summary loop corresponding to the phase Phase in the database	
add_phase_loop(Phase,RefCnt,Head,Call,Cs):-
		assertz(phase_loop(Phase,RefCnt,Head,Call,Cs)).

%! add_external_call_pattern(+Head:term,+Id_RefCnt:(int,int),+Terminating:flag,+Components:list(chain),+Inv:polyhedron) is det
% store a external call pattern
add_external_call_pattern(Head,Id_RefCnt,Terminating,Components,Inv) :-	
	  assertz(external_call_pattern(Head,Id_RefCnt,Terminating,Components,Inv)).


%! add_upper_bound(+Head:term,+Chain:chain,+Cost_structure:cost_structure) is det
% stores the upper bound of chain Chain. It computes the hash of the iterative components of the cost structure
add_upper_bound(Head,Chain,CExpr) :-	
	(upper_bound(Head,Chain,_,CExpr)->
	 true
	;
	  copy_term((Head,CExpr),(E,C)),
	  numbervars((E,C),0,_),
	  term_hash(C,Hash),
	  assertz(upper_bound(Head,Chain,Hash,CExpr))
	),!.
	
%! add_external_upper_bound(+Head:term,+Precondition_id:int,+Cost_structure:cost_structure) is det
% stores the upper bound for the precondition Precondition_id.
add_external_upper_bound(Head,Precondition_id,CExpr) :-	
	(external_upper_bound(Head,Precondition_id,CExpr)->
	 true
	;
	  assertz(external_upper_bound(Head,Precondition_id,CExpr))
	),!.	
	
%! add_closed_upper_bound(+Head:term,+Chain:chain,+Cost_expression:cost_expression) is det
% stores the closed upper bound of chain Chain. It computes the hash of the cost expression
add_closed_upper_bound(Head,Chain,CExpr) :-	
	(closed_upper_bound(Head,Chain,CExpr)->
	 true
	;
	  assertz(closed_upper_bound(Head,Chain,CExpr))
	),!.
%! add_closed_lower_bound(+Head:term,+Chain:chain,+Cost_expression:cost_expression) is det
% stores the closed lower bound of chain Chain. It computes the hash of the cost expression
add_closed_lower_bound(Head,Chain,CExpr) :-	
	(closed_lower_bound(Head,Chain,CExpr)->
	 true
	;
	  assertz(closed_lower_bound(Head,Chain,CExpr))
	),!.	
	
%! add_single_closed_upper_bound(+Head:term,+Cost_expression:cost_expression) is det
% stores the single closed upper bound of the SCC Head.
add_single_closed_upper_bound(Head,CExpr) :-	
	assertz(single_closed_upper_bound(Head,CExpr)).	

%! add_conditional_upper_bound(+Head:term,+Cost_expression:cost_expression,+Preconditions:list(polyhedron)) is det
% stores the conditional upper bound determined by the cost Cost_expression and the precondition Precondition
add_conditional_bound(Head,CExpr,Preconditions) :-	
	  assertz(conditional_bound(Head,CExpr,Preconditions)).

%! closed_upper_bound_print(Head:term,Chain:chain,UB1:cost_expression)
% obtain a printable simplified cost expression from the corresponding closed upper bound
closed_upper_bound_print(Head,Chain,UB1):-
	closed_upper_bound(Head,Chain,Cost_max_min),
	backward_invariant(Head,(Chain,_),_,Head_Pattern),
	strexp_simplify_max_min(Cost_max_min,Cost_max_min_simple),
	strexp_to_cost_expression(Cost_max_min_simple,UB),
	cexpr_simplify(UB,Head_Pattern,UB1),!.

%! closed_lower_bound_print(Head:term,Chain:chain,UB1:cost_expression)
% obtain a printable simplified cost expression from the corresponding closed lower bound	
closed_lower_bound_print(Head,Chain,UB1):-
	closed_lower_bound(Head,Chain,Cost_max_min),
	backward_invariant(Head,(Chain,_),_,Head_Pattern),
	strexp_simplify_max_min(Cost_max_min,Cost_max_min_simple),
	strexp_to_cost_expression(Cost_max_min_simple,UB),
	cexpr_simplify(UB,Head_Pattern,UB1),!.

conditional_upper_bound(Head,Exp,Prec):-
	conditional_bound(Head,(Exp,_),Prec).
conditional_lower_bound(Head,Exp,Prec):-
	conditional_bound(Head,(_,Exp),Prec).		  