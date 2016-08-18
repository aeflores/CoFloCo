:- module(node_splitting,[make_graph_reducible/2]).
:- use_module(stdlib(multimap)).
:- use_module(stdlib(set_list)).

:-dynamic node_split/2.
%Graph=[location-location]
make_graph_reducible(Edges,Split_nodes):-
	foldl(get_predecessors_map,Edges,[],Pred_map),
	exclude_end_points(Pred_map,Pred_map2),
	reduce_graph(Pred_map2),
	findall([Node,Predecessors],
		node_split(Node,Predecessors),
		Split_nodes),
	retractall(node_split(_,_)).

get_predecessors_map(O-D,Map,Map1):-
	put_mm(Map,[D],[O],Map1).

exclude_end_points(Pred_map,Pred_map_final):-
	exclude_end_points_1(Pred_map,[],Pred_map2_inv),
	reverse(Pred_map2_inv,Pred_map2),
	length(Pred_map,N),
	length(Pred_map2,N2),
	(N2< N-> 
		exclude_end_points(Pred_map2,Pred_map_final)
		;
		Pred_map_final=Pred_map2).
exclude_end_points_1([],Pred_map_inv,Pred_map_inv).
exclude_end_points_1([(Elem,Preds)|Pred_map],Pred_map_accum,Pred_map_inv):-
	maplist(not_predecesor(Elem),[(Elem,Preds)|Pred_map]),
	maplist(not_predecesor(Elem),Pred_map_accum),!,
	exclude_end_points_1(Pred_map,Pred_map_accum,Pred_map_inv).
	
exclude_end_points_1([(Elem,Preds)|Pred_map],Pred_map_accum,Pred_map_inv):-
	exclude_end_points_1(Pred_map,[(Elem,Preds)|Pred_map_accum],Pred_map_inv).

not_predecesor(Elem,(_,Preds)):-
	\+contains_sl(Preds,Elem).
	
reduce_graph(Graph):-
	%maplist(writeln,Graph),nl,trace,
	is_reduced_graph(Graph).
	
reduce_graph(Graph):-
	t1(Graph,Graph1),%!,writeln(t1),
	reduce_graph(Graph1).
	
reduce_graph(Graph):-
	t2(Graph,Graph1),%!,writeln(t2),
	reduce_graph(Graph1).

reduce_graph(Graph):-
	t3(Graph,Graph1),%!,writeln(t3),
	reduce_graph(Graph1).
	
is_reduced_graph([_One]).

t1(Pred_map,Pred_map2):-
	maplist(remove_self_edges,Pred_map,Pred_map2),
	Pred_map\=Pred_map2.
remove_self_edges((D,Origins),(D,Origins2)):-
	exclude(=(D),Origins,Origins2).

t2(Pred_map,Pred_map2):-
	get_mergeable_loc(Pred_map,Loc,Pred),
	merge_nodes(Pred,Loc,Pred_map,Pred_map2).

get_mergeable_loc([(Loc,[Pred])|_],Loc,Pred):-!.

get_mergeable_loc([_|Map],Loc,Pred):-
	get_mergeable_loc(Map,Loc,Pred).

merge_nodes(Pred,Loc,Pred_map,Pred_map5):-
	remove_key_mm(Pred_map,Loc,Pred_map1),
	values_of_mm_no_fail(Pred_map1,Pred,Predecessors),
	remove_key_mm(Pred_map1,Pred,Pred_map2),
	append(Pred,Loc,Merged),
	put_values_mm(Pred_map2,Merged,Predecessors,Pred_map3),
	maplist(substitute_predecessor(Loc,Merged),Pred_map3,Pred_map4),
	maplist(substitute_predecessor(Pred,Merged),Pred_map4,Pred_map5).

substitute_predecessor(Old,New,(Loc,Set),(Loc,Set2)):-
	contains_sl(Set,Old),!,
	remove_sl(Set,Old,Set1),
	insert_sl(Set1,New,Set2).
substitute_predecessor(_Old,_New,(Loc,Set),(Loc,Set)).

t3(Pred_map,Pred_map2):-
	split_node(Pred_map,Pred_map2).

split_node(Pred_map,Pred_map2):-
	Pred_map=[(Node1,Preds)|Rest],
	get_node_weight((Node1,Preds),Weight1),
	foldl(get_minimum_weight_node,Rest,(Node1,Weight1),(Node,_)),
	values_of_mm(Pred_map,Node,Predecessors),
	assertz(node_split(Node,Predecessors)),
	%writeln(node_split(Node,Predecessors)),
	split_node_1(Node,Pred_map,Pred_map2).
	
get_minimum_weight_node((Node,Preds),(Node2,Weight2),(Node_min,Weight_min)):-
	get_node_weight((Node,Preds),Weight),
	(Weight < Weight2->
		Node_min=Node,
		Weight_min=Weight
		;
		Node_min=Node2,
		Weight_min=Weight).
get_node_weight((Node,Preds),Weight):-
	length(Node,N1),
	length(Preds,N2),
	Weight is N1*N2.
split_node_1(Node,Pred_map,Pred_map3):-
	values_of_mm(Pred_map,Node,Predecessors),
	remove_key_mm(Pred_map,Node,Pred_map1),
	foldl(add_splited_node(Node),Predecessors,(1,[],Pred_map1),(_Max,New_nodes,Pred_map2)),
	from_list_sl(New_nodes,New_nodes_set),
	maplist(substitute_predecessor_by_set(Node,New_nodes_set),Pred_map2,Pred_map3).

values_of_mm_no_fail(Pred_map,Node,Predecessors):-
	values_of_mm(Pred_map,Node,Predecessors),!.
values_of_mm_no_fail(_Pred_map,_Node,[]).
	
add_splited_node(Node,Predecessor,(N,New_nodes,Pred_map),(N1,[[Node:N]|New_nodes],Pred_map2)):-
	put_mm(Pred_map,[Node:N],Predecessor,Pred_map2),
	N1 is N+1.
substitute_predecessor_by_set(Old,New_nodes_set,(Loc,Set),(Loc,Set2)):-
	contains_sl(Set,Old),!,
	remove_sl(Set,Old,Set1),
	union_sl(Set1,New_nodes_set,Set2).
substitute_predecessor_by_set(_Old,_New,(Loc,Set),(Loc,Set)).
	