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

:- use_module('../db',[eq_ph/7,loop_ph/4, add_loop_ph/5,add_phase_loop/5]).
:- use_module(chains,[phase/3]).


:- use_module(stdlib(numeric_abstract_domains),[nad_lub/6,nad_project/3, nad_consistent_constraints/1]).
:- use_module(stdlib(utils),[ut_list_to_dlist/2,ut_sort_rdup/2,ut_member/2]).

	
%! compute_loops(Head:term,RefCnt:int) is det
% compute a loop for each cost equation that has a recursive call
compute_loops(Head,RefCnt) :-
	eq_ph(Head,(Eq_Id,RefCnt),_,_,[Rec_Call],_,Cs),
	Head =.. [F|Vs1],
	Rec_Call=..[F|Vs2],
	append(Vs1,Vs2,Vs),
	nad_project(Vs,Cs,Cs_aux),
	add_loop_ph(Head,RefCnt,Rec_Call,Cs_aux, Eq_Id),
	fail.
compute_loops(_Head,_RefCnt).


%! compute_phase_loops(Head:term,RefCnt:int) is det
% compute a loop for each iterative phase 
compute_phase_loops(Head,RefCnt) :-
	phase(Class,Head,RefCnt),
	findall(loop(Head,Call,Cs),
		(member(Id,Class),
		 loop_ph(Head,(Id,RefCnt),Call,Cs)
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