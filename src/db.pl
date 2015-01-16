/** <module> db

This module acts as a database that stores:

  * the set of cost equations in different stages of refinement
  * the loops (which are fragments of cost equations)
  * the generated upper bounds

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
	   add_loop_ph/5,
	   add_phase_loop/5,
	   add_eq_ph/3,
	   add_ground_equation_header/2,
		  
	   eq_refined/2,
	   input_eq/5,	 
	   entry_eq/2,   
	   ground_equation_header/1,
	   eq_ph/7,
       loop_ph/4,
	   phase_loop/5,
	   non_terminating_stub/2,
	   non_terminating_chain/2,	   

	   upper_bound/4,
	   add_upper_bound/3,
	   closed_upper_bound/4,
	   add_closed_upper_bound/3,
	   	  
       cofloco_aux_entry_name/1
       
]).
:- use_module('IO/params',[get_param/2]).
:- use_module('utils/cofloco_utils',[assign_right_vars/3]).

:- use_module(stdlib(utils),[ut_var_member/2]).
:- use_module(stdlib(counters),[counter_initialize/2,counter_increase/3,counter_get_value/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_entails/3,nad_glb/3,nad_list_lub/2,nad_lub/6,nad_project/3]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_get_info/3,
				 profiling_stop_timer/2,profiling_stop_timer_acum/2]).


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

/**  eq_ph(?Head:term,?Id_RefCnt:(int,equation_id),-Cost:cost_expression,-Non_rec_Calls:list(term),-Rec_Calls:list(term),-Calls:list(term),-Cs:polyhedron)

 stores a cost equation after the preprocessing. 
 The calls are separated into non-recursive and recursive. Calls has all the calls together in the original order
 
 @arg Id_RefCnt represent the 'RefCnt' and the 'id' of the cost equation
 the refinement takes place in phases. 'RefCnt' indicates to which refinement phase the cost equation belongs

*/
:- dynamic  eq_ph/7.

%! eq_refined(Original:equation_id,Refined:equation_id)
% record the fact that Refined is a refined version of Original
% this is recorded in order to trace the behavior back to the original representation.
:- dynamic eq_refined/2.

%! loop_ph(?Head:term,?Id_RefCnt:(int,equation_id),-Rec_Call:term,-Cs:polyhedron)
% for each recursive equation loop_ph/4 stores the relation between the head and the recursive call (abstracting the cost and the other calls away)
:- dynamic  loop_ph/4.

%! phase_loop(?Phase:phase,?RefCnt:int,-Head:term,-Call:term,-Cs:polyhedron)
% a summary of all the loops of a phase (Phase) of the cost equation Head
:- dynamic  phase_loop/5.

%! upper_bound(?Head:term,?Chain:chain,-Hash:int,-Cost_structure:cost_structure)
% an cost structure that represents an upper bound of the chain Chain that belongs to the SCC Head.  
% Hash is the hash of part of the cost structure and can be used to compress similar cost structures
:- dynamic upper_bound/4.

%! closed_upper_bound(?Head:term,?Chain:chain,-Hash:int,-Cost_expression:cost_expression)
% an cost expression that represents an upper bound of the chain Chain that belongs to the SCC Head.  
% Hash is the hash of part of the cost structure and can be used to compress similar cost structures
:- dynamic closed_upper_bound/4.

%! non_terminating_stub(?Head:term,?Id:equation_id)
% It indicates that the cost equation Id is non-terminating
:-dynamic non_terminating_stub/2.

%! non_terminating_chain(?Head:term,?Chain:chain)
% It indicates that the chain Chain is non-terminating
% a chain whose first element is a non_terminating_stub is non-terminating
:-dynamic non_terminating_chain/2.

%non_terminating_chain(Head,[First|_]):-
%	non_terminating_stub(Head,First).

%! init_db is det
% erase the database and initialize counters
init_db:-
	retractall(input_eq(_,_,_,_,_)),
	retractall(entry_eq(_,_)),
	retractall(ground_eq_header(_)),
	retractall(eq_ph(_,_,_,_,_,_,_)),
	retractall(loop_ph(_,_,_,_)),
	
	retractall(phase_loop(_,_,_,_,_)),
	retractall(upper_bound(_,_,_,_)),
	retractall(closed_upper_bound(_,_,_,_)),
	
	retractall(non_terminating_stub(_,_)),
	retractall(non_terminating_chain(_,_)),
	assert(non_terminating_chain(Head,[First|_]):-non_terminating_stub(Head,First) ),
	counter_initialize(input_eqs,0),
	
	
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


%! add_ground_equation_header(+Non_ground:term,+Ground:term) is det
% store the ground term Ground if there is no ground_eq_header that can be unified with Non_ground.
% that is, we store on ground_eq_header per cost equation header
add_ground_equation_header(Non_ground,_Ground):-
	copy_term(Non_ground,Non_ground2),
	ground_equation_header(Non_ground2),!.
	
add_ground_equation_header(_Non_ground,Ground):-
	assert(ground_equation_header(Ground)).

%! add_eq_ph(+Cost_equation:cost_equation,+Term_flag:flag) is det
% stores the cost equation Cost_equation in the database
%
% @arg Term_flag indicates if the cost equation is terminating or not (it can be 'terminating' or 'non_terminating')
add_eq_ph(eq_ph(Head,RefCnt,E_Exp,NR_Calls,R_Calls,Calls,P_Size),Term_flag,Previous_eqs) :-
	counter_increase(eq_ph,1,Id),
	assertz(eq_ph(Head,(Id,RefCnt),E_Exp,NR_Calls,R_Calls,Calls,P_Size)),
	assertz(eq_refined(Previous_eqs,Id)),	
%	copy_term(eq_ph(Head,(Id,RefCnt),E_Exp,NR_Calls,R_Calls,Calls,P_Size),Eq_print),
%	numbervars(Eq_print,0,_),
%	writeln(Eq_print),
	(Term_flag=non_terminating->
	 	assertz(non_terminating_stub(Head,Id))
	;
	  true).
	  
%! add_loop_ph(+Head:term,+RefCnt:int,+Call:term,+Cs:polyhedron,+Id:equation_id) is det
% stores the loop corresponding to the cost equation Id in the database
add_loop_ph(Head,RefCnt,Call,Cs, Id) :-
	assertz(loop_ph(Head,(Id,RefCnt),Call,Cs)).
	
%! add_phase_loop(+Phase:phase,+RefCnt:int,+Head:term,+Call:term,+Cs:polyhedron) is det
% stores the summary loop corresponding to the phase Phase in the database	
add_phase_loop(Phase,RefCnt,Head,Call,Cs):-
		assertz(phase_loop(Phase,RefCnt,Head,Call,Cs)).

%! add_upper_bound(+Head:term,+Chain:chain,+Cost_structure:cost_structure) is det
% stores the upper bound of chain Chain. It computes the hash of the iterative components of the cost structure
add_upper_bound(Head,Chain,CExpr) :-	
	(upper_bound(Head,Chain,_,CExpr)->
	 true
	;
	  copy_term((Head,CExpr),(E,C)),
	  numbervars((E,C),0,_),
	  C=cost(_,Loops,Constr),
	  term_hash((Loops,Constr),Hash),
	  assertz(upper_bound(Head,Chain,Hash,CExpr))
	),!.
%! add_closed_upper_bound(+Head:term,+Chain:chain,+Cost_expression:cost_expression) is det
% stores the closed upper bound of chain Chain. It computes the hash of the cost expression
add_closed_upper_bound(Head,Chain,CExpr) :-	
	(closed_upper_bound(Head,Chain,_,CExpr)->
	 true
	;
	  copy_term((Head,CExpr),(E,C)),
	  numbervars(E,0,_),
	  term_hash(C,Hash),
	  assertz(closed_upper_bound(Head,Chain,Hash,CExpr))
	),!.


