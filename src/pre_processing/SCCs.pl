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
    compute_sccs_and_btcs/3,
    scc_get_internal_callers/3,
    scc_get_cover_points/2
]).

:- use_module('../IO/output',[print_merging_cover_points/3]).		
:- use_module('../utils/cofloco_utils',[sort_with/3,tuple/3,zip_with_op2/4]).	

:- use_module('../utils/crs',[
	crs_get_graph/2,
	crs_get_ce_by_name/3,
	entry_name/2
]).	


:- use_module(stdlib(scc),[compute_sccs/2]).
:- use_module(stdlib(minimal_feedback_set),[compute_mfbs_shamir/3]).
:- use_module(stdlib(set_list),[from_list_sl/2]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).

%! compute_sccs_and_btcs
% compute strongly connected components and BTCs (a cover point for each SCC)
%
% @throws error(irreducible_multual_recursion(SCC_graph))
compute_sccs_and_btcs(CRSE,SCCs_list4,CRSE2):-
	CRSE=crse(Entries,CRS),
	compute_crs_sccs(Entries,CRS,SCCs_list),
	maplist(compute_scc_extra_info(CRS),SCCs_list,SCCs_list2),
	compute_btcs(CRSE,SCCs_list2,SCCs_list3),
	length(SCCs_list,N),
	merge_multiple_cover_points(SCCs_list3,N,CRSE,SCCs_list4,CRSE2).


scc_get_internal_callers(scc(_,_,Sub_Graph,_,_),F/A,Callers):-
	setof(Caller,
		A2^member(Caller/A2-F/A,Sub_Graph)
		,Callers).
scc_get_cover_points(scc(_,_,_,_,Info),Cover_points):-
	member(cover_points(Cover_points),Info),!.
scc_get_cover_points(scc(_,_,_,_,_),[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_crs_sccs is det
%compute strongly connected components.
%



%first create the call graph, then compute the sccs and store them
compute_crs_sccs(Entries,CRS,SCCs1):-
	maplist(entry_name,Entries,Entry_names),
	crs_get_graph(CRS,call_graph(Edges)),
	maplist(zip_with_op2('-','$cofloco_aux_entry$'),Entry_names,Aux_edges),
	append(Aux_edges,Edges,Edges1),
	compute_sccs(Edges1,SCCs_basic),
	maplist(compute_enriched_scc(call_graph(Edges1)),SCCs_basic,SCCs),
	select(scc(non_recursive,['$cofloco_aux_entry$'],_,_,_),SCCs,SCCs1).


compute_enriched_scc(Graph,(Type,Nodes),scc(Type,Nodes,Sub_Graph,Entries,[])):-
	compute_scc_subgraph(Graph,Nodes,Sub_Graph,Entries).
	
compute_scc_subgraph(call_graph(Edges),Nodes,Sub_Graph,Entries):-
	include(edge_to(Nodes),Edges,Sub_graph_aux),
	partition(edge_from(Nodes),Sub_graph_aux,Sub_Graph,Entry_edges),
	maplist(get_edge_destination,Entry_edges,Entries_aux),
	from_list_sl(Entries_aux,Entries).

edge_to(Nodes,_O-D):-
	member(D,Nodes),!.
edge_from(Nodes,O-_D):-
	member(O,Nodes),!.
	
get_edge_destination(_O-D,D).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


compute_scc_extra_info(_CRS,scc(non_recursive,Nodes,Sub_Graph,Entries,[]),scc(non_recursive,Nodes,Sub_Graph,Entries,[])):-!.

compute_scc_extra_info(CRS,scc(recursive,Nodes,Sub_Graph,Entries,[]),scc(recursive,Nodes,Sub_Graph,Entries,Info)):-
	(is_non_tail_recursive(Nodes,CRS)->
		Info=[non_tail|Info2]
		;
		Info=Info2
	),
	(is_multiple_recursive(Nodes,CRS)->
		Info2=[multiple]
		;
		Info2=[]
	).

is_non_tail_recursive(Nodes,CRS):-
	member(Node/_Arity,Nodes),
	crs_get_ce_by_name(CRS,Node,eq(_,_,Calls,_)),
	discard_until_first_recursive(Calls,Nodes,Rest),
	member(Non_rec,Rest),
	functor(Non_rec,Node_non,Arity_non),
	\+member(Node_non/Arity_non,Nodes),!.
	
is_multiple_recursive(Nodes,CRS):-
	member(Node/_Arity,Nodes),
	crs_get_ce_by_name(CRS,Node,eq(_,_,Calls,_)),

	discard_until_first_recursive(Calls,Nodes,Rest),
	discard_until_first_recursive(Rest,Nodes,_),!.
	

discard_until_first_recursive([Call|Rest],Nodes,Rest):-
	functor(Call,Node,Arity),
	member(Node/Arity,Nodes),!.
discard_until_first_recursive([_|Rest1],Nodes,Rest):-
	discard_until_first_recursive(Rest1,Nodes,Rest).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


	
%! compute_btcs is det
% compute a cover point for each SCC
% if it fails, throw an exception
%
% @throws error(irreducible_multual_recursion(SCC_graph))


compute_btcs(CRSE,SCCs,SCCs_with_cover_points):-
	maplist(compute_cover_point_for_scc(CRSE),SCCs,SCCs_with_cover_points).


compute_cover_point_for_scc(CRSE,scc(non_recursive,[Node],SCC_graph,SCC_Entries,Info),
							scc(non_recursive,[Node],SCC_graph,SCC_Entries,InfoExtra)):-!,
		
	CRSE=crse(Entries,CRS),
	((has_entry_node(Entries,Node)
	 ; 
	 \+is_simple_path(CRS,Node) )->
	 	InfoExtra=[cover_points([Node])|Info]
		;
		InfoExtra=Info
	).
	

compute_cover_point_for_scc(CRSE,scc(recursive,Nodes,SCC_Graph,SCC_Entries,Info),
								 scc(recursive,Nodes,SCC_Graph,SCC_Entries,InfoExtra)) :-
			
	CRSE=crse(_,CRS),
	crs_get_graph(CRS,Graph),
	sort_entries(SCC_Entries,Nodes,Graph,Entries_sorted),
	compute_cover_point_for_scc_aux(Nodes,SCC_Graph,Entries_sorted,Cover_Points),
	InfoExtra=[cover_points(Cover_Points)|Info].


has_entry_node(Entries,Node/A):-
	functor(Head,Node,A),
	member(entry(Head,_),Entries),!.

	
%has_one_eq(_Nodes):-!,fail.	
is_simple_path(CRS,Name/_):-
	findall(Calls,crs_get_ce_by_name(CRS,Name,eq(_,_,Calls,_)),[Calls]),
	length(Calls,N),N < 2.



% prioritize entries that are called more times and have less variables
sort_entries(Entries,Nodes,Graph,Entries_sorted):-
	maplist(annotate_entries_with_n_calls(Nodes,Graph),Entries,Entries_annotated),
	sort_with(Entries_annotated,worse_entry,Entries_annotated_sorted),
	maplist(tuple,Entries_sorted,_,Entries_annotated_sorted).
	
annotate_entries_with_n_calls(Nodes_scc,call_graph(Edges),F/A,(F/A,N)):-
	findall(Caller,
		(
	    	member(Caller-F/A,Edges),
	    	\+member(Caller,Nodes_scc)
	    ),Callers),
	    length(Callers,N).
	    	
	    	
worse_entry((_F/_A,N),(_F2/_A2,N2)):-
	N<N2,!.
worse_entry((_F/A,N),(_F2/A2,N2)):-
	N=N2,	
	A>A2.

compute_cover_point_for_scc_aux(_,SCC_Graph,Entries,MFBS) :- % try shamir's algorithm
	member(E,Entries),
	compute_mfbs_shamir(SCC_Graph,E,MFBS),!.

compute_cover_point_for_scc_aux(Nodes,SCC_Graph,Entries,Cover_Points) :- % try the naive (quadratic) algorithm
	(member(N,Entries); (member(N,Nodes), \+ member(N,Entries))),
	is_1fbs(SCC_Graph,N),
	Cover_Points=[N],
	!.
	
compute_cover_point_for_scc_aux(_Nodes,SCC_Graph,_Entries,_Cover_Point):-
	throw(irreducible_multual_recursion(SCC_Graph)).
	
is_1fbs(Graph,Node) :-
	findall(A-B,(member(A-B,Graph),A \== Node,B \== Node),Reduced_Graph),
	compute_sccs(Reduced_Graph,SCCs_aux),
	\+ member((recursive,_),SCCs_aux),
	!.
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

merge_multiple_cover_points([],_,CRSE,[],CRSE).
merge_multiple_cover_points([SCC|SCCs],N,CRSE,[SCC1|SCCs1],CRSE_out):-
	SCC=scc(_Type,_Nodes,_Sub_Graph,_Entries,Info),
	(member(cover_points([_,_|_]),Info)->
		scc_merge_multiple_cover_points(SCC,N,CRSE,SCC1,CRSE1)	    
	 ;
	 	SCC1=SCC,
	 	CRSE1=CRSE
	 ),
	 N1 is N-1,
	 merge_multiple_cover_points(SCCs,N1,CRSE1,SCCs1,CRSE_out).
	

	
% Substitute all the calls and cost relations of Cover_points by calls and cost relations of a merged predicate
% the merged predicate has the maximum number of input and output variables
% for example, to merge p(X1,Y1,Z1),[X1,Y1],[Z1] and q(X2,Y2,Z2,W2),[X2],[Y2,Z2,W2] we obtain a merged
% pq(X1,Y1,Y2,Z2,W2) [X1,Y1] [Y2,Z2,W2]
scc_merge_multiple_cover_points(SCC,SCC_N,CRSE,SCC1,CRSE1):-
	SCC=scc(_Type,_Nodes,_Sub_Graph,_,Info),
	%update the scc
	select(Info,cover_points(Cover_points),Info1),
	CRSE=crse(_,CRS),
	generate_merged_name_arity(Cover_points,CRS,New_name,Max_arity_input,Max_arity_output),
	Max_arity is Max_arity_input+Max_arity_output,
	Info2=[cover_points([New_name/Max_arity])|Info1],
	update_scc(SCC,Info2,New_name/Max_arity,Cover_points,SCC1),

	%update the crse
	crse_merge_crs(New_name/Max_arity_input/Max_arity_output,Cover_points,CRSE,CRSE1),
	print_merging_cover_points(SCC_N,Cover_points,New_name/Max_arity).
	
	
	
generate_merged_name_arity([Last/_Arity],CRS,Last,Iarity,Oarity):-!,
	crs_IOvars_arities(CRS,Last,Iarity,Oarity).

generate_merged_name_arity([Name1/_|Cover_points],CRS,Merged_name,Iarity_max,Oarity_max):-
	crs_IOvars_arities(CRS,Name1,Iarity1,Oarity1),
	generate_merged_name_arity(Cover_points,CRS,Name2,Iarity2,Oarity2),
	Iarity_max is max(Iarity1,Iarity2),
	Oarity_max is max(Oarity1,Oarity2),
	atom_concat(Name1,Name2,Merged_name).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



update_scc(scc(Type,Nodes,SCC_Graph,Entries,_Info),Info2,New_node,Old_nodes,SCC1):-
	maplist(substitute_node(New_node,Old_nodes),Nodes,Nodes2),
	from_list_sl(Nodes2,Nodes_set),
	maplist(substitute_node(New_node,Old_nodes),Entries,Entries2),
	from_list_sl(Entries2,Entries_set),
	maplist(substitute_edge(New_node,Old_nodes),SCC_Graph,SCC_Graph2),
	from_list_sl(SCC_Graph2,SCC_Graph_set),
	SCC1=scc(Type,Nodes_set,SCC_Graph_set,Entries_set,Info2).
	
	
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




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%assign_new_scc_if_not_cutpoint(Entry):-
%	functor(Entry,F,A),
%	crs_btc(F,A),!.
%assign_new_scc_if_not_cutpoint(Entry):-
%	functor(Entry,F,A),
%	retract(crs_max_scc_id(N)),
%	N1 is N+1,
%	assert(crs_max_scc_id(N1)),
%	retractall(crs_node_scc(F,A,_)),
%	assert(crs_node_scc(F,A,N1)),
%	assert(crs_scc(N1,non_recursive,[F/A],[],[F/A],[entry_scc])),
%	assert(crs_residual_scc(N1,F/A)),
%	print_new_scc(F/A,N1).


	

