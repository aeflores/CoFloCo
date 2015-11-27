/**  <module>  SCCs

This module computes:
  * the strongly connected components SCCs of the input cost equations.
  * the cover point of each of each SCCs (if it exists) that is stored as crs_btc/2 (binding time classification) 
    and will be used to ensure termination of the partial evaluation.


The module implementation is adapted from the module pubs_db.pl (SCC computation) 
and pubs_btc.pl (Cover point computation) in PUBS implemented by 
E.Albert, P.Arenas, S.Genaim, G.Puebla, and D.Zanardini
                        https://costa.ls.fi.upm.es

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

:- module('SCCs',[
    compute_sccs_and_btcs/0,
    crs_scc/5,
    crs_max_scc_id/1,
    crs_btc/2,
    crs_residual_scc/2,
    crs_node_scc/3,
    ignored_scc/1
]).

:- use_module('../db',[input_eq/5]).
%:- use_module(recursion_loop_extraction,[try_loop_extraction/1]).

:- use_module(stdlib(scc),[compute_sccs/2]).
:- use_module(stdlib(minimal_feedback_set),[compute_mfbs_shamir/3]).
:- use_module(stdlib(set_list),[from_list_sl/2]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
%! crs_btc(Functor:atom,Arity:int)
% the cost equation Functor/Arity is a cover point (btc)
:- dynamic crs_btc/2.

%! crs_graph(Graph:list(functor/arity-functor/arity))
% stores the complete call graph
:- dynamic crs_graph/1.

%! crs_edge(Functor:atom,Arity:int,Functor2:atom,Arity2:int)
% stores an edge of the graph
:- dynamic crs_edge/4.
%! crs_rev_edge(Functor2:atom,Arity2:int,Functor:atom,Arity:int)
% stores the reverse of an edge of the graph
:- dynamic crs_rev_edge/4.
%! crs_scc(SCC_N:int,Type:atom,Nodes:list(functor/arity),SCC_Graph:list(functor/arity-functor/arity),Entries:list(functor/arity))
% stores a strongly connected component.
% Type can be recursive and non_recursive
:- dynamic crs_scc/5.

%! crs_node_scc(Functor:functor,Arity:arity,SCC_N:int)
% Functor/Arity belongs to the SCC SCC_N
:- dynamic crs_node_scc/3.

%! crs_max_scc_id(SCC_N:int)
% number of the topmost SCC
:- dynamic crs_max_scc_id/1.

%! crs_residual_scc(SCC_N:int,Term:functor/arity)
% the cost equation Term is a cover point (BTC)
:- dynamic crs_residual_scc/2.

%! ignored_scc(Term:functor/arity)
% the SCC corresponding to Term (after partial evaluation) is never called
:- dynamic ignored_scc/1.

%! compute_sccs_and_btcs
% compute strongly connected components and BTCs (a cover point for each SCC)
%
% @throws error(no_cover_point,[scc=SCC_N])
compute_sccs_and_btcs:-
	init_sccs,
	compute_crs_sccs,
	compute_btcs.
%	catch(compute_btcs
%	,error(no_cover_point,[scc=SCC_N]),
%	    (
%	    try_loop_extraction(SCC_N),
%	    compute_sccs_and_btcs)
%	   ).
	

init_sccs:-
	retractall(crs_btc(_,_)),
	retractall(crs_graph(_)),
	retractall(crs_edge(_,_,_,_)),
	retractall(crs_rev_edge(_,_,_,_)),
	retractall(crs_scc(_,_,_,_,_)),
	retractall(crs_node_scc(_,_,_)),
	retractall(crs_max_scc_id(_)),
	retractall(crs_residual_scc(_,_)),
	retractall(crs_ignored_scc(_)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_btcs is det
% compute a cover point for each SCC
% if it fails, throw an exception
%
% @throws error(no_cover_point,[scc=SCC_N])
compute_btcs:-
	compute_btc_aux(0),
	!.

compute_btc_aux(SCC_N) :-
	compute_cover_point_for_scc(SCC_N),
	!,
	SCC_N1 is SCC_N+1,
	compute_btc_aux(SCC_N1).
compute_btc_aux(_).


compute_cover_point_for_scc(SCC_N) :-
	crs_scc(SCC_N,Type,Nodes,SCC_Graph,Entries),

	( compute_cover_point_for_scc_aux(Type,SCC_N,Nodes,SCC_Graph,Entries,Cover_Point) ->
		add_to_btc([Cover_Point]),
		declare_residual_scc(SCC_N,Cover_Point)
	;
	    throw(error(no_cover_point,[scc=SCC_N]))
	    
	).

compute_cover_point_for_scc_aux(non_recursive,_SCC_N,[F/A],_SCC_Graph,_Entries,F/A) :-!.


compute_cover_point_for_scc_aux(recursive,_SCC_N,_Nodes,SCC_Graph,Entries,Cover_Point) :- % try shamir's algorithm
	Entries=[E|_],
	compute_mfbs_shamir(SCC_Graph,E,MFBS),
	MFBS=[Cover_Point],
	!.

compute_cover_point_for_scc_aux(recursive,_SCC_N,Nodes,SCC_Graph,Entries,Cover_Point) :- % try the naive (quadratic) algorithm
	(member(N,Entries); (member(N,Nodes), \+ member(N,Entries))),
	is_1fbs(SCC_Graph,N),
	Cover_Point=N,
	!.

is_1fbs(Graph,Node) :-
	findall(A-B,(member(A-B,Graph),A \== Node,B \== Node),Reduced_Graph),
	compute_sccs(Reduced_Graph,SCCs_aux),
	\+ member((recursive,_),SCCs_aux),
	!.


add_to_btc([]).
add_to_btc([F/A|Ns]) :-
	( crs_btc(F,A) -> true ; assertz(crs_btc(F,A)) ),
	add_to_btc(Ns).


declare_residual_scc(SCC_N,BTC) :-
	assertz(crs_residual_scc(SCC_N,BTC)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_crs_sccs is det
%compute strongly connected components.
%
%first create the call graph, then compute the sccs and store them
compute_crs_sccs :-
	findall(F1/A1-F2/A2,
	        (input_eq(Head,_,_,Calls,_), member(Call, Calls),functor(Head,F1,A1), functor(Call,F2,A2) ),
	        Graph_aux),
	from_list_sl(Graph_aux,Graph),  
	store_graph(Graph),
	compute_sccs(Graph,SCCs),
	store_sccs(SCCs).

store_graph(Graph) :-
	assertz(crs_graph(Graph)),
	maplist(store_edge,Graph).

store_edge(F1/A1-F2/A2) :-
	assertz(crs_edge(F1,A1,F2,A2)),
	assertz(crs_rev_edge(F2,A2,F1,A1)).

store_sccs(SCCs) :-
	store_sccs_aux(SCCs,0,N),
	Last_SCC_Id is N-1,
	assertz(crs_max_scc_id(Last_SCC_Id)).

store_sccs_aux([],N,N).
store_sccs_aux([(Type,Nodes)|SCCs],N,Last_N) :-
	store_scc(Type,Nodes,N),
	N1 is N+1,
	store_sccs_aux(SCCs,N1,Last_N).



store_scc(Type,Nodes,N) :-
	maplist(store_scc_node(N),Nodes),
	compute_scc_subgraph(Nodes,N,Sub_Graph,Entries),
	assertz(crs_scc(N,Type,Nodes,Sub_Graph,Entries)).

compute_scc_subgraph(Nodes,SCC_N,Sub_Graph,Entries) :-
	findall(F2/A2-F1/A1,
	        (member(F1/A1,Nodes), crs_rev_edge(F1,A1,F2,A2) ),
	        Sub_Graph_aux),
	remove_entry_edges(Sub_Graph_aux,SCC_N,Sub_Graph,Entries_aux),
	from_list_sl(Entries_aux,Entries).

remove_entry_edges([],_,[],[]).
remove_entry_edges([F1/A1-F2/A2|Es],SCC_N,[F1/A1-F2/A2|Sub_Es],Entries) :-
	crs_node_scc(F1,A1,SCC_N),
	!,
	remove_entry_edges(Es,SCC_N,Sub_Es,Entries).
remove_entry_edges([_-F2/A2|Es],SCC_N,Sub_Es,[F2/A2|Entries]) :-
	remove_entry_edges(Es,SCC_N,Sub_Es,Entries).


store_scc_node(N,F/A) :-
	assertz(crs_node_scc(F,A,N)).




