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

:- use_module('../db',[
		input_eq/5,
		entry_eq/2,
		get_input_output_arities/3,
		get_input_output_vars/3,
		save_input_output_vars/3]).
:- use_module('../IO/output',[print_merging_cover_points/3]).		
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
% @throws error(irreducible_multual_recursion(SCC_graph))
compute_sccs_and_btcs:-
	init_sccs,
	compute_crs_sccs,
	compute_btcs.

	

init_sccs:-
	retractall(crs_btc(_,_)),
	retractall(crs_graph(_)),
	retractall(crs_edge(_,_,_,_)),
	retractall(crs_rev_edge(_,_,_,_)),
	retractall(crs_scc(_,_,_,_,_)),
	retractall(crs_node_scc(_,_,_)),
	retractall(crs_max_scc_id(_)),
	retractall(crs_residual_scc(_,_)),
	retractall(ignored_scc(_)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_btcs is det
% compute a cover point for each SCC
% if it fails, throw an exception
%
% @throws error(irreducible_multual_recursion(SCC_graph))
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
	crs_scc(SCC_N,non_recursive,[Node],_SCC_Graph,_Entries),!,
	((has_entry_node([Node])
	 ; 
	 \+has_one_eq(Node) )->
		add_to_btc([Node]),
		declare_residual_scc(SCC_N,Node)
		;
		true
	).
	

compute_cover_point_for_scc(SCC_N) :-
	crs_scc(SCC_N,recursive,Nodes,SCC_Graph,Entries),
	compute_cover_point_for_scc_aux(Nodes,SCC_Graph,Entries,Cover_Points),
	( Cover_Points=[Cover_Point] ->
	%we can partially evaluate the SCC to Cover_point
		add_to_btc([Cover_Point]),
		declare_residual_scc(SCC_N,Cover_Point)	
	;
		%a single node is not enough so we merge the multiple ones
	    merge_multiple_cover_points(Cover_Points,Merged_cover_point),
	    print_merging_cover_points(SCC_N,Cover_Points,Merged_cover_point),
	    add_to_btc([Merged_cover_point]),
		declare_residual_scc(SCC_N,Merged_cover_point)	
	    
	).

has_entry_node(Nodes):-
	entry_eq(Head,_),
	functor(Head,F,A),
	member(F/A,Nodes),!.
has_one_eq(F/A):-
	functor(Head,F,A),
	findall(Id,input_eq(Head,Id,_,_,_),[_]).
	
% Substitute all the calls and cost relations of Cover_points by calls and cost relations of a merged predicate
% the merged predicate has the maximum number of input and output variables
% for example, to merge p(X1,Y1,Z1),[X1,Y1],[Z1] and q(X2,Y2,Z2,W2),[X2],[Y2,Z2,W2] we obtain a merged
% pq(X1,Y1,Y2,Z2,W2) [X1,Y1] [Y2,Z2,W2]
merge_multiple_cover_points(Cover_points,New_name/Max_arity):-
	generate_merged_name_arity(Cover_points,New_name,Max_arity_input,Max_arity_output),
	Max_arity is Max_arity_input+Max_arity_output,
	maplist(get_extra_arity(Max_arity_input,Max_arity_output),Cover_points,Extra_Iarities,Extra_Oarities),
	maplist(substitute_calls(New_name),Cover_points,Extra_Iarities,Extra_Oarities),
	maplist(substitute_equations(New_name),Cover_points,Extra_Iarities,Extra_Oarities),
	maplist(substitute_entries(New_name),Cover_points,Extra_Iarities,Extra_Oarities),
	length(Ivars,Max_arity_input),
	length(Ovars,Max_arity_output),
	append(Ivars,Ovars,Vars),
	Head=..[New_name|Vars],
	save_input_output_vars(Head,Ivars,Ovars),
	% We update all the scc information as well
	update_crs_graph(New_name/Max_arity,Cover_points).

generate_merged_name_arity([Last/Arity],Last,Iarity,Oarity):-!,
	get_input_output_arities(Last/Arity,Iarity,Oarity).
	
generate_merged_name_arity([Name1/Arity1|Cover_points],Merged_name,Iarity_max,Oarity_max):-
	get_input_output_arities(Name1/Arity1,Iarity1,Oarity1),
	generate_merged_name_arity(Cover_points,Name2,Iarity2,Oarity2),
	Iarity_max is max(Iarity1,Iarity2),
	Oarity_max is max(Oarity1,Oarity2),
	atom_concat(Name1,Name2,Merged_name).

get_extra_arity(Max_Ia,Max_Oa,Name/A,Extra_Ia,Extra_Oa):-
	get_input_output_arities(Name/A,Ia,Oa),
	Extra_Ia is Max_Ia-Ia,
	Extra_Oa is Max_Oa-Oa.

substitute_calls(New_name,Old_name/Arity,Extra_Iarity,Extra_Oarity):-
	crs_rev_edge(Old_name,Arity,Caller,Arity_caller),
	functor(Head_caller,Caller,Arity_caller),	
	retract(db:input_eq(Head_caller,Id,Cost,Calls,Cs)),
	maplist(substitute_call(Old_name/Arity,New_name,Extra_Iarity,Extra_Oarity),Calls,Calls2),
	assertz(db:input_eq(Head_caller,Id,Cost,Calls2,Cs)),
	fail.
	
substitute_calls(_,_,_,_).

substitute_call(Old_name/Arity,New_name,Extra_Iarity,Extra_Oarity,Call,Call_new):-
	functor(Call,Old_name,Arity),!,
	get_new_head(Call,New_name,Extra_Iarity,Extra_Oarity,Call_new).
substitute_call(_,_,_,_,Call,Call).

substitute_equations(New_name,Old_name/Arity,Extra_Iarity,Extra_Oarity):-
	functor(Head,Old_name,Arity),
	get_new_head(Head,New_name,Extra_Iarity,Extra_Oarity,Head_new),
	retract(db:input_eq(Head,Id,Cost,Calls,Cs)),
	assertz(db:input_eq(Head_new,Id,Cost,Calls,Cs)),
	fail.
substitute_equations(_,_,_,_).

substitute_entries(New_name,Old_name/Arity,Extra_Iarity,Extra_Oarity):-
	functor(Head,Old_name,Arity),
	get_new_head(Head,New_name,Extra_Iarity,Extra_Oarity,Head_new),
	retract(db:entry_eq(Head,Cs)),
	assertz(db:entry_eq(Head_new,Cs)),
	fail.
substitute_entries(_,_,_,_).

get_new_head(Head,New_name,E_Iarity,E_Oarity,Head_new):-	
	get_input_output_vars(Head,Ivars,Ovars),
	length(Extra_Ivars,E_Iarity),
	length(Extra_Ovars,E_Oarity),
	append(Ivars,Extra_Ivars,New_Ivars),
	append(Ovars,Extra_Ovars,New_Ovars),
	append(New_Ivars,New_Ovars,New_vars),
	Head_new=..[New_name|New_vars],!.

		
	
update_crs_graph(New_name,Old_names):-
	update_crs_global_graph(New_name,Old_names),
	update_edges(New_name,Old_names),
	update_scc(New_name,Old_names).

update_crs_global_graph(New_name,Old_names):-
	retract(crs_graph(Graph)),
	maplist(substitute_edge(New_name,Old_names),Graph,Graph2),
	from_list_sl(Graph2,Graph_set),
	assertz(crs_graph(Graph_set)).

update_edges(New_name,Old_names):-
	maplist(update_edges_1(New_name),Old_names).
	
update_edges_1(New_name/A_new,Old_name/A_old):-
	retract(crs_edge(Old_name,A_old,D,Da)),
	assertz(crs_edge(New_name,A_new,D,Da)),
	fail.
update_edges_1(New_name/A_new,Old_name/A_old):-
	retract(crs_edge(O,Oa,Old_name,A_old)),
	assertz(crs_edge(O,Oa,New_name,A_new)),
	fail.
update_edges_1(New_name/A_new,Old_name/A_old):-
	retract(crs_rev_edge(Old_name,A_old,D,Da)),
	assertz(crs_rev_edge(New_name,A_new,D,Da)),
	fail.
update_edges_1(New_name/A_new,Old_name/A_old):-
	retract(crs_rev_edge(O,Oa,Old_name,A_old)),
	assertz(crs_rev_edge(O,Oa,New_name,A_new)),
	fail.
update_edges_1(_,_).


update_scc(New_name/New_arity,Old_names):-		
	Old_names=[Old_name/Old_arity|_],
	crs_node_scc(Old_name,Old_arity,SCC_N),
	retract(crs_scc(SCC_N,recursive,Nodes,SCC_Graph,Entries)),
	maplist(substitute_node(New_name/New_arity,Old_names),Nodes,Nodes2),
	from_list_sl(Nodes2,Nodes_set),
	maplist(substitute_node(New_name/New_arity,Old_names),Entries,Entries2),
	from_list_sl(Entries2,Entries_set),
	maplist(substitute_edge(New_name/New_arity,Old_names),SCC_Graph,SCC_Graph2),
	from_list_sl(SCC_Graph2,SCC_Graph_set),
	assertz(crs_scc(SCC_N,recursive,Nodes_set,SCC_Graph_set,Entries_set)),
	maplist(remove_node_scc_reference,Old_names),
	assertz(crs_node_scc(New_name,New_arity,SCC_N)).
	
remove_node_scc_reference(Old_name/Old_arity):-
	retract(crs_node_scc(Old_name,Old_arity,_SCC_N)).
	
substitute_edge(New_name,Old_names,Node-Node2,New_node-New_node2):-
	(member(Node,Old_names)->
		New_node=New_name
		;
		New_node=Node
		),
    (member(Node2,Old_names)->
		New_node2=New_name
		;
		New_node2=Node2
		),!.
substitute_node(New_name,Old_names,Node,New_node):-
	(member(Node,Old_names)->
		New_node=New_name
		;
		New_node=Node
		),!.		

	
compute_cover_point_for_scc_aux(_,SCC_Graph,Entries,MFBS) :- % try shamir's algorithm
	Entries=[E|_],
	compute_mfbs_shamir(SCC_Graph,E,MFBS),!.

compute_cover_point_for_scc_aux(Nodes,SCC_Graph,Entries,Cover_Point) :- % try the naive (quadratic) algorithm
	(member(N,Entries); (member(N,Nodes), \+ member(N,Entries))),
	is_1fbs(SCC_Graph,N),
	Cover_Point=N,
	!.
	
compute_cover_point_for_scc_aux(_Nodes,SCC_Graph,_Entries,_Cover_Point):-
	throw(irreducible_multual_recursion(SCC_Graph)).
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




