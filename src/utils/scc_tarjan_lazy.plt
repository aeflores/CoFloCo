
:-begin_tests(scc_tarjan_lazy).
:-ensure_loaded(scc_tarjan_lazy).

test(basic_example):-
	Graph=fixed_graph([0,1,2,3,4,5,6,7],
		[0-1,0-2,1-3,3-4,4-1,2-5,2-6,6-5,5-1,5-7,7-2]),
	scc_lazy_tarjan(Graph,SCCs),
	SCCs=[[0], [2,5,6, 7], [1,3,4]].

test(two_loops):-
	Graph=fixed_graph([0,1,2,3,4,5,6,7],
		[0-1,1-2,2-3,3-4,4-0,  5-6,6-7,7-5]),
	scc_lazy_tarjan(Graph,SCCs),
	SCCs=[[5,6,7],[0,1,2,3,4]].

test(two_loops_connected):-
	Graph=fixed_graph([0,1,2,3,4,5,6,7],
		[0-1,1-2,2-3,3-4,4-0,   4-5,    5-6,6-7,7-5]),
	scc_lazy_tarjan(Graph,SCCs),
	SCCs=[[0,1,2,3,4],[5,6,7]].
	

	
test(fake_lazy):-
	Graph=lazy_graph([0,1,2,3,4,5,6,7],plunit_scc_tarjan_lazy:lazy_edge1,
	[0-1,0-2,1-3,3-4,4-1,2-5,2-6,6-5,5-1,5-7,7-2]),
	scc_lazy_tarjan(Graph,SCCs),
	SCCs=[[0], [2,5,6, 7], [1,3,4]].
	
test(translation):-
	Graph=lazy_graph([a,b,c,d,e,f,g,h],plunit_scc_tarjan_lazy:lazy_edge1,
	[a-b,a-c,b-d,d-e,e-b,c-f,c-g,g-f,f-b,f-h,h-c]),
	scc_lazy_tarjan(Graph,SCCs),
	SCCs=[[a], [c,f,g, h], [b,d,e]].

test(complete_graph):-
	Graph=lazy_graph([a,b,c,d,e,f,g,h],plunit_scc_tarjan_lazy:lazy_edge_complete,
	_),
	scc_lazy_tarjan(Graph,SCCs),
	SCCs=[[a,b,c,d,e,f,g,h]].

test(disconnected_graph):-
	Graph=lazy_graph([a,b,c,d,e,f,g,h],plunit_scc_tarjan_lazy:lazy_edge_disconnected,
	_),
	scc_lazy_tarjan(Graph,SCCs),
	SCCs=[[h],[g],[f],[e],[d],[c],[b],[a]].


lazy_edge1(Edges,O,D):-
	member(O-D,Edges),!.
	
lazy_edge_complete(_,_O,_D).	
lazy_edge_disconnected(_,_O,_D):-fail.	

:-end_tests(scc_tarjan_lazy).


	