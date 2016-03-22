/** <module> loops

This module  computes loops for each cost equation and phase.
Given a cost equation with a recursive call C(X)=c+D_1(Y1)+...+D_N(Yn)+C(X')  and with the polyhedron phi.
Its loop is a polyhedron phi' that relates X and X'. That is, it's the projection of phi onto X and X',
the rest of the variables are ignored.

For multiple recursion:
C(X)=c+D_1(Y1)+...+D_N(Yn)+C(X')+C(X'')
it relates X with X' and X'' (the variables of the recursive calls)

A loop of a phase [C1,C2,...,CN] is the convex hull of the loops of each cost equation C1,C2,...,CN.
  
@author Antonio Flores Montoya

@copyright Copyright (C) 2014,2015,2016 Antonio Flores Montoya

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

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
%! compute_loops(Head:term,RefCnt:int) is det
% compute a loop for each cost equation
compute_loops(Head,RefCnt):-
	findall(((Head,Rec_Calls,Term_flag),(Inv,Eq_Id)),(
		    get_equation(Head,Rec_Calls,RefCnt,Eq_Id,Cs,Term_flag),
		    term_variables((Head,Rec_Calls),Vs),
	        nad_project_group(Vs,Cs,Inv)
	        ),Loops),
	      
	%make groups according to number of calls and term_flag       
	foldl(group_loop_vars,Loops,[],_),
	maplist(normalize_loop,Loops,Normalized_loops),
	from_pair_list_mm(Normalized_loops,Grouped_loops),
	(get_param(compress_chains,[])->
	maplist(group_equal_loops,Grouped_loops,Simplified_loops)
	;
	maplist(put_in_list,Grouped_loops,Simplified_loops)
	),	
	maplist(save_loop(RefCnt),Simplified_loops).

%unify the variables if the patterns match												
group_loop_vars(((Head,Rec_Calls,Term_flag),_Info),Groups,Groups):-
	member((Head,Rec_Calls,Term_flag),Groups),!.
group_loop_vars(((Head,Rec_Calls,Term_flag),_Info),Groups,Groups1):-
	Groups1=[(Head,Rec_Calls,Term_flag)|Groups].
	
group_equal_loops((Header,Info),(Header,Info_compressed)):-
	from_pair_list_mm(Info,Info_compressed).
							        	 	 	    
get_equation(Head,Rec_Calls,RefCnt,Eq_Id,Cs,Term_flag):-
	 eq_ph(Head,(Eq_Id,RefCnt),_,_,Rec_Calls,_,Cs,Term_flag).
	 
normalize_loop(((Head,Rec_Calls,Term_flag),(Inv,Eq_id)),((Head,Rec_Calls,Term_flag),(Inv_normalized,Eq_id))):-
	nad_normalize_polyhedron(Inv,Inv_normalized).
	
save_loop(RefCnt,((Head,Calls,Term_flag),List_Inv_Eqs)):-
%	reverse(List_Inv_Eqs,List_Inv_Eqs1),
	maplist(save_loop_1(RefCnt,Head,Calls,Term_flag),List_Inv_Eqs).

save_loop_1(RefCnt,Head,Calls,Term_flag,(Inv,Equations)):-
	add_loop_ph(Head,RefCnt,Calls,Inv, Equations,Term_flag).
	
put_in_list((Header,List_Inv_Eqs),(Header,List_Inv_Eqs1)):-
	maplist(put_in_list_1,List_Inv_Eqs,List_Inv_Eqs1).
	
put_in_list_1((Inv,E),(Inv,[E])).

%! compute_phase_loops(Head:term,RefCnt:int) is det
% compute a loop for each iterative phase 
compute_phase_loops(Head,RefCnt) :-
	phase(Class,Head,RefCnt),
	findall(loop(Head,Calls,Cs),
		(member(Id,Class),
		 loop_ph(Head,(Id,RefCnt),Calls,Cs,_,_)
		),Loops),
	join_loops(Loops,Head_out,Calls_out,Cs_out,_Vars),
	add_phase_loop(Class,RefCnt,Head_out,Calls_out,Cs_out),
	fail.
compute_phase_loops(_Head,_RefCnt).


join_loops([loop(Head,Calls,Cs)],Head,Calls,Cs,Vars):-!,
	Head=..[_|V1],
	term_variables(Calls,V2),
	append(V1,V2,Vars).

join_loops([loop(Head,Calls,Cs)|Loops],Head,Calls,Cs_out,Vars):-
	join_loops(Loops,Head,Calls,Cs_aux,Vars),
	nad_lub(Vars,Cs,Vars,Cs_aux,Vars,Cs_out).
	
	