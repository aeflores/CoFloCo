:- module(scc_tarjan_lazy,[
		scc_lazy_tarjan/2
	]).

	
scc_lazy_tarjan(Graph,SCCs_translated):-
	graph_nodes(Graph,Nodes),
	length(Nodes,N),
	functor(State,state,N),
	functor(DfsNum,dfsum,N),
	functor(DfsLow,dflow,N),
	Stack=[],
	lazy_tarjan(1,N,0,Graph,State,DfsNum,DfsLow,Stack,[],SCCs),
	translate_back(SCCs,Nodes,SCCs_translated).


lazy_tarjan(V,Max,_,_,_,_,_,_,SCCs,SCCs):-
	V > Max,!.
	
lazy_tarjan(V,Max,N,Graph,State,DfsNum,DfsLow,Stack,SCCs_accum,SCCs):-
	lazy_tarjan_N(V,N,Graph,State,DfsNum,DfsLow,Stack,
		_,N2,Stack2,SCCs_accum,SCCs_accum2),
	V1 is V+1, 
	lazy_tarjan(V1,Max,N2,Graph,State,DfsNum,DfsLow,Stack2,SCCs_accum2,SCCs).
	

translate_back(SCCs,Index,SCCs_originals):-
	maplist(translate_back_scc(Index),SCCs,SCCs_originals).

translate_back_scc(Index,SCC,SCC_original_sorted):-
	maplist(translate_back_node(Index),SCC,SCC_original),
	sort(SCC_original,SCC_original_sorted).
translate_back_node(Index,Node,Node_original):-
	nth1(Node,Index,Node_original).

lazy_tarjan_N(V,N,_Graph,State,_DfsNum,DfsLow,Stack,Ret,N,Stack,SCCs,SCCs):-
	arg(V,State,Val),
	nonvar(Val),!,
	arg(V,DfsLow,Ret).
	
lazy_tarjan_N(V,N,Graph,State,DfsNum,DfsLow,Stack,
	Ret,N_final,Stack3,SCCs_accum,SCCs):-
%	writeln(State),
%	writeln(DfsNum),
%	writeln(DfsLow),
	arg(V,State,visited),
	arg(V,DfsNum,N),
	arg(V,DfsLow,N),
	N1 is N+1,
	Stack1=[V|Stack],
	do_for_each_successor(1,V,N1,Graph,State,DfsNum,DfsLow,Stack1,
		N_final,Stack2,SCCs_accum,SCCs_accum2),
	setarg(V,State,finished),
	arg(V,DfsLow,Low_v),
	arg(V,DfsNum,Num_v),
	(Low_v >= Num_v ->
		pop_scc(Stack2,V,State,Stack3,SCC),
		SCCs=[SCC|SCCs_accum2]
		;
		Stack3=Stack2,
		SCCs=SCCs_accum2
		),
	arg(V,DfsLow,Ret).



do_for_each_successor(I,V,N,Graph,State,DfsNum,DfsLow,Stack,
		N_final,Stack2,SCCs_accum,SCCs):-
		get_next_nonpopped_successor(I,V,Graph,State,DfsLow,W),!,
		arg(W,State,W_state),
		(W_state==popped->
			SCCs_accum2=SCCs_accum,
			N1=N,
			Stack1=Stack
			;
			lazy_tarjan_N(W,N,Graph,State,DfsNum,DfsLow,Stack
				,Ret,N1,Stack1,SCCs_accum,SCCs_accum2),
			arg(V,DfsLow,Old_v_low),
			Min is min(Old_v_low,Ret),
			setarg(V,DfsLow,Min)
		),
		I1 is W+1,
		do_for_each_successor(I1,V,N1,Graph,State,DfsNum,DfsLow,Stack1,
		N_final,Stack2,SCCs_accum2,SCCs).
				

do_for_each_successor(_,_,N,_Graph,_State,_DfsNum,_DfsLow,Stack,
		N,Stack,SCCs,SCCs).


get_next_nonpopped_successor(Index,V,Graph,State,DfsLow,Index):-
	arg(Index,State,Index_state),
	Index_state\==popped,
	(
	var(Index_state)
	; 
	nonvar(Index_state),
	arg(V,DfsLow,Old_v_low),
	arg(Index,DfsLow,Ret),
	Ret<Old_v_low
	),
	edge(Graph,V,Index),!.
get_next_nonpopped_successor(Index,V,Graph,State,DfsLow,D):-
	Index1 is Index+1,
	graph_size(Graph,Size),
	Index1 =< Size,
	get_next_nonpopped_successor(Index1,V,Graph,State,DfsLow,D).
	

pop_scc([],_State,[],[]).
pop_scc([Elem|Stack],V,State,Stack2,[Elem|SCC]):-
	setarg(Elem,State,popped),
	(Elem=V->
		SCC=[],
		Stack=Stack2
	;
		pop_scc(Stack,V,State,Stack2,SCC)
	).


edge(fixed_graph(Nodes,Edges),O,D):-
	nth1(O,Nodes,NO),
	nth1(D,Nodes,ND),
	member(NO-ND,Edges),!.


edge(lazy_graph(Nodes,Pred,Args),O,D):-
	nth1(O,Nodes,NO),
	nth1(D,Nodes,ND),
	call(Pred,Args,NO,ND),!.
	
graph_size(fixed_graph(Nodes,_Edges),Size):-
	length(Nodes,Size).
	
graph_size(lazy_graph(Nodes,_Pred,_Args),Size):-
	length(Nodes,Size).
	
graph_nodes(fixed_graph(Nodes,_Edges),Nodes).
graph_nodes(lazy_graph(Nodes,_Pred,_Args),Nodes).

	