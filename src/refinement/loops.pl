/** <module> loops

This module  computes loops for each cost equation and phase.
Given a cost equation with a recursive call C(X)=c+D_1(Y1)+...+D_N(Yn)+C(X')  and with the polyhedron phi.
Its loop is a polyhedron phi' that relates X and X'. That is, it's the projection of phi onto X and X',
the rest of the variables are ignored.


A loop of a phase [C1,C2,...,CN] is the convex hull of the loops of each cost equation C1,C2,...,CN.
  
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
:- module(loops,[compute_loops/2,compute_phase_loops/2]).

:- use_module('../db',[eq_ph/8,loop_ph/6, add_loop_ph/6,add_phase_loop/5]).
:- use_module(chains,[phase/3]).

:-use_module('../IO/params',[get_param/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_lub/6]).
:- use_module('../utils/polyhedra_optimizations',[nad_project_group/3,nad_normalize_polyhedron/2]).
:- use_module('../utils/cofloco_utils',[assign_right_vars/3]).
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).		
%! compute_loops(Head:term,RefCnt:int) is det
% compute a loop for each cost equation that has a recursive call
compute_loops(Head,RefCnt):-
	copy_term(Head,Rec_call),
	compute_loops_1(Head,RefCnt,Rec_call,terminating),
    compute_loops_1(Head,RefCnt,none,terminating),
    compute_loops_1(Head,RefCnt,Rec_call,non_terminating),
    compute_loops_1(Head,RefCnt,none,non_terminating),
    %add a non-terminating stub
    add_loop_ph(Head,RefCnt,none,[],[],non_terminating).
      
compute_loops_1(Head,RefCnt,Rec_Call,Term_flag) :-
	findall(((Head,Rec_Call),(Inv,Eq_Id)),(
		    get_equation(Head,Rec_Call,RefCnt,Eq_Id,Cs,Term_flag),
		    term_variables((Head,Rec_Call),Vs),
	        nad_project_group(Vs,Cs,Inv)
	        ),Loops_aux),
	assign_right_vars(Loops_aux,(Head,Rec_Call),Loops),
	maplist(normalize_loop,Loops,Normalized_loops),
	(get_param(compress_chains,[])->
	from_pair_list_mm(Normalized_loops,Simplified_loops)
	;
	maplist(put_in_list,Normalized_loops,Simplified_loops)
	),	
	maplist(save_loop(Head,RefCnt,Rec_Call,Term_flag),Simplified_loops).
												
							        
get_equation(Head,none,RefCnt,Eq_Id,Cs,Term_flag):-
	 eq_ph(Head,(Eq_Id,RefCnt),_,_,[],_,Cs,Term_flag).
	 	 	    
get_equation(Head,Rec_Call,RefCnt,Eq_Id,Cs,Term_flag):-
	 eq_ph(Head,(Eq_Id,RefCnt),_,_,[Rec_Call],_,Cs,Term_flag).
	 
normalize_loop((Inv,Eq_id),(Inv_normalized,Eq_id)):-
	nad_normalize_polyhedron(Inv,Inv_normalized).
	
save_loop(Head,RefCnt,Call,Term_flag,(Inv,Equations)):-
	add_loop_ph(Head,RefCnt,Call,Inv, Equations,Term_flag).
	
put_in_list((Inv,E),(Inv,[E])).

%! compute_phase_loops(Head:term,RefCnt:int) is det
% compute a loop for each iterative phase 
compute_phase_loops(Head,RefCnt) :-
	phase(Class,Head,RefCnt),
	findall(loop(Head,Call,Cs),
		(member(Id,Class),
		 loop_ph(Head,(Id,RefCnt),Call,Cs,_,_)
		),Loops),
	join_loops(Loops,Head_out,Call_out,Cs_out,_Vars),
	add_phase_loop(Class,RefCnt,Head_out,Call_out,Cs_out),
	fail.
compute_phase_loops(_Head,_RefCnt).


join_loops([loop(Head,Call,Cs)],Head,Call,Cs,Vars):-!,
	Head=..[_|V1],
	Call=..[_|V2],
	append(V1,V2,Vars).

join_loops([loop(Head,Call,Cs)|Loops],Head,Call,Cs_out,Vars):-
	join_loops(Loops,Head,Call,Cs_aux,Vars),
	nad_lub(Vars,Cs,Vars,Cs_aux,Vars,Cs_out).
	
	