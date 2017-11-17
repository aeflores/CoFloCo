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
:- module(loops,[
	    loops_range/2,
	    loops_get_list/3,
	    loops_get_ids/2,
	    loop_is_multiple/1,
	    loop_is_base_case/1,
	    loops_get_loop/3,
	    loops_get_loop_fresh/3,
		compute_loops/3,
		compute_phase_loops/2,
		split_multiple_loops/2,
		get_extended_phase/2]).

:- use_module('../db',[add_phase_loop/5]).
:- use_module(chains,[phase/3]).

:-use_module('../IO/params',[get_param/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_lub/6]).
:- use_module('../utils/polyhedra_optimizations',[nad_project_group/3,nad_normalize_polyhedron/2]).
:- use_module('../utils/cofloco_utils',[
			assign_right_vars/3,
			merge_implied_summaries/3]).

:- use_module('../utils/crs',[
	cr_get_loops/2,
	cr_set_loops/3,
	cr_get_ceList_with_id/2
]).
						
:- use_module(stdlib(multimap),[from_pair_list_mm/2]).		
:- use_module(stdlib(list_map)).	
:- use_module(stdlib(set_list),[is_subset_sl/2,union_sl/3]).	
:- use_module(stdlib(numeric_abstract_domains),[nad_entails/3]).
:- use_module(library(apply_macros)).
:- use_module(library(lists)).
:- use_module(library(lambda)).

loop_is_multiple(loop(_,Calls,_,_)):-
	Calls=[_,_|_].
	
loop_is_base_case(loop(_,[],_,_)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
loops_range(loops(Range,_),Range).

loops_get_loop(loops(_Range,Map),Id,Loop):-
	lookup_lm(Map,Id,Loop).
	
loops_get_loop_fresh(loops(_Range,Map),Id,Loop):-
	lookup_lm(Map,Id,Loop1),
	copy_term(Loop1,Loop).

loops_get_ids(loops(_Range,Map),Ids):-
	keys_lm(Map,Ids).

loops_empty(loops(range(1,1),Map)):-
	empty_lm(Map).

loops_add_loop(loops(range(I,F),Map),Loop,loops(range(I,F2),Map2)):-
	assertion(Loop=loop(_Head,_Calls,_Inv,_Info)),
	insert_lm(Map,F,Loop,Map2),
	F2 is F+1.

loops_get_list(loops(_,Map),Ids,List):-
	project_lm(Map,Ids,List).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_loops(Head:term,RefCnt:int) is det
% compute a loop for each cost equation
compute_loops(CR,Compress,CR2):-
	cr_get_ceList_with_id(CR,CE_list_id),
	maplist(
		\Eq_pair_l^Res_l^(
					Eq_pair_l=(Eq_Id,eq_ref(Head,_,_NR_calls,R_calls,_Calls,Cs,Info)),
				    term_variables((Head,R_calls),Vs),
	        	    nad_project_group(Vs,Cs,Inv),	
	        	    Res_l=((Head,R_calls,Info),(Inv,Eq_Id))
	        	    ),CE_list_id,Loops),
	%make groups according to number of calls and term_flag       
	foldl(group_loop_vars,Loops,[],_),
	maplist(normalize_loop,Loops,Normalized_loops),
	from_pair_list_mm(Normalized_loops,Grouped_loops),
	%merge loops that are equivalent or similar, depending on N
	(Compress > 0->
	maplist(group_equal_loops(Compress),Grouped_loops,Simplified_loops)
	;
	maplist(put_in_list,Grouped_loops,Simplified_loops)
	),	
	loops_empty(Empty_loops),
	foldl(save_loop,Simplified_loops,Empty_loops,Loops_complete),
	cr_set_loops(CR,Loops_complete,CR2).

	 
%unify the variables if the patterns match												
group_loop_vars(((Head,Rec_Calls,Term_flag),_Info),Groups,Groups):-
	member((Head,Rec_Calls,Term_flag),Groups),!.
group_loop_vars(((Head,Rec_Calls,Term_flag),_Info),Groups,Groups1):-
	Groups1=[(Head,Rec_Calls,Term_flag)|Groups].

%merge loops that are completely equivalent	
group_equal_loops(1,(Header,Info),(Header,Info_compressed)):-
	from_pair_list_mm(Info,Info_compressed).

%merge loops such that one is more general than another
group_equal_loops(2,(Header,Info),(Header,Info_compressed2)):-
	from_pair_list_mm(Info,Info_compressed),
	term_variables(Header,Vars),
	merge_implied_summaries(Vars,Info_compressed,Info_compressed2).
							        	 	 	    

	 
normalize_loop(((Head,Rec_Calls,Info),(Inv,Eq_id)),((Head,Rec_Calls,Info),(Inv_normalized,Eq_id))):-
	nad_normalize_polyhedron(Inv,Inv_normalized).
	
save_loop(((Head,Calls,Info),List_Inv_Eqs),CR,CR2):-
	reverse(List_Inv_Eqs,List_Inv_Eqs1),
	foldl(save_loop_1(Head,Calls,Info),List_Inv_Eqs1,CR,CR2).

save_loop_1(Head,Calls,Info,(Inv,Equations),CR,CR2):-
	loops_add_loop(CR,loop(Head,Calls,Inv,[eqs(Equations)|Info]),CR2).
	
put_in_list((Header,List_Inv_Eqs),(Header,List_Inv_Eqs1)):-
	maplist(put_in_list_1,List_Inv_Eqs,List_Inv_Eqs1).
	
put_in_list_1((Inv,E),(Inv,[E])).

%! compute_phase_loops(Head:term,RefCnt:int) is det
% compute a loop for each iterative phase 
compute_phase_loops(Head,RefCnt) :-
	phase(Class,Head,RefCnt),
	findall((Head,Calls,Cs),
		(member(Id,Class),
		 loop_ph(Head,(Id,RefCnt),Calls,Cs,_,_)
		),Loops),
	split_multiple_loops(Loops,Loops_splitted),
	join_loops(Loops_splitted,Head_out,Call_out,Cs_out,_Vars),
	add_phase_loop(Class,RefCnt,Head_out,Call_out,Cs_out),
	fail.
compute_phase_loops(_Head,_RefCnt).


join_loops([(Head,Calls,Cs)],Head,Calls,Cs,Vars):-!,
	Head=..[_|V1],
	term_variables(Calls,V2),
	append(V1,V2,Vars).

join_loops([(Head,Calls,Cs)|Loops],Head,Calls,Cs_out,Vars):-
	join_loops(Loops,Head,Calls,Cs_aux,Vars),
	nad_lub(Vars,Cs,Vars,Cs_aux,Vars,Cs_out).
	
	
 split_multiple_loops(Loops,Loops_splitted):-
 	     split_multiple_loops_aux(Loops,[],Loops_splitted).
 
 split_multiple_loops_aux([],Loops_splitted,Loops_splitted).	
 split_multiple_loops_aux([(_Head,[],_Inv)|Loops],Loops_accum,Loops_splitted):-
  	   split_multiple_loops_aux(Loops,Loops_accum,Loops_splitted).
  split_multiple_loops_aux([(Head,[Call|Calls],Inv)|Loops],Loops_accum,Loops_splitted):-
	  term_variables((Head,Call),Vars),
	  nad_project_group(Vars,Inv,Inv_loop),
  	  split_multiple_loops_aux([(Head,Calls,Inv)|Loops],[(Head,Call,Inv_loop)|Loops_accum],Loops_splitted). 
  	  
  	  
get_extended_phase([],[]).
get_extended_phase([Loop|Phase],Extended_phase1):-
	loop_ph(_,(Loop,_),Calls,_,_,_),
	length(Calls,N),
	get_extended_loop_names(1,N,Loop,Extended_loops),
	get_extended_phase(Phase,Extended_phase),
	append(Extended_loops,Extended_phase,Extended_phase1).
get_extended_loop_names(N,N,Loop,[Loop:N]).
get_extended_loop_names(N1,N,Loop,[Loop:N1|Extended_loops]):-
	N1<N,
	N2 is N1+1,
	get_extended_loop_names(N2,N,Loop,Extended_loops).	