#!/usr/bin/prolog

:-module(cfg2ces_module,[main_cfg2ces/0,main_bin_cfg2ces/0]).

:-include('../../../src/search_paths.pl').


:- use_module(stdlib(linear_expression), [parse_le/2, integrate_le/3]).
:- use_module(stdlib(fraction),[negate_fr/2]).
:- use_module(stdlib(parsing_writing),[write_sum/2]).
:- use_module(stdlib(pair_list),[zip_with/4,unzip/3]).
:- use_module(stdlib(relational),[is_relational/1]).
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list),[union_sl/3,intersection_sl/3,from_list_sl/2,contains_sl/2,insert_sl/3,difference_sl/3]).
:- use_module(stdlib(counters),[counter_initialize/2,counter_increase/3,counter_get_value/2]).

:- dynamic iloop_header/2.
:- dynamic iloop_header_rev/2.
:- dynamic dfsp_pos/2.
:- dynamic traversed/1.
:- dynamic irreducible/1.
:- dynamic loop_header/1.
:- dynamic reentry/2.
:- dynamic cfg_edge/2.
:- dynamic cfg_edge_rev/2.
:- dynamic pcfg_edge/4.
:- dynamic cfg_nodes/1.
:- dynamic cfg_entry/1.
:- dynamic node_in_loop/2.
:- dynamic exit_id/2.
:- dynamic eq/5.
:- dynamic ground_term/3.
:- dynamic loop_has_new_vars/2.
:- dynamic removed_n_outs/2.

:- dynamic option/1.
:- dynamic exit_location/1.
:- dynamic last_id/1.

init_db :-
	counter_initialize(eq,0),
	retractall(iloop_header(_,_)),
	retractall(iloop_header_rev(_,_)),
	retractall(dfsp_pos(_,_)),
	retractall(traversed(_)),
	retractall(irreducible(_)),
	retractall(loop_header(_)),
	retractall(reentry(_,_)),
	retractall(cfg_edge(_,_)),
	retractall(cfg_edge_rev(_,_)),
	retractall(pcfg_edge(_,_,_,_)),
	retractall(cfg_nodes(_)),
	retractall(cfg_entry(_)),
	retractall(node_in_loop(_,_)),
	retractall(exit_id(_,_)),
	retractall(eq(_,_,_,_,_)),
	retractall(ground_term(_,_,_)),
	retractall(loop_has_new_vars(_,_)),
	retractall(exit_location(_)),
	retractall(last_id(_)),
	assert(last_id(1)),
	!.

save_equation(Head,Cost,Calls,Cs):-
	counter_increase(eq,1,Id),
	assertz(eq(Id,Head,Cost,Calls,Cs)).
	
loop_cont_name('_loop_cont').

main_cfg2ces:-
    current_prolog_flag(argv, Args),
    cfg2ces(Args),
	halt.
main_bin_cfg2ces:-
    current_prolog_flag(argv, [_|Args]),
    cfg2ces(Args),
	halt.
	       
cfg2ces([]):-format(user_error,'No file parameter received~n',[]).

cfg2ces([F|Other_args]) :-
	process_args(Other_args),
	catch(cfg2ces_1(F),Error,(format(user_error,'~p~n',[Error]),halt)),!.


process_args([]).
process_args(['-o',File|Args]):-!,
	assert(option(to_file(File))),
	process_args(Args).
process_args(['-dot',File|Args]):-!,
	assert(option(dot(File))),
	process_args(Args).	
process_args(['-ces',File|Args]):-!,
	assert(option(ces_dot(File))),
	process_args(Args).	
process_args([loop_cost_model|Args]):-!,
	assert(option(loop_cost_model)),
	process_args(Args).
process_args([continuation_style|Args]):-!,
	assert(option(continuation_style)),
	process_args(Args).
process_args([slice|Args]):-!,
	assert(option(slice)),
	process_args(Args).	
process_args([add_outs|Args]):-!,
	assert(option(add_outs)),
	process_args(Args).		
process_args([X|_Args]):-!,
	throw(invalid_parameter(X)).	
	
cfg2ces_1(F) :-
	(F=stdin->
		read_term(CFG,[variable_names(Bindings)])
	;
	open(F,read,S),
	read_term(S,CFG,[variable_names(Bindings)]),
	close(S)
	),
	(option(to_file(File))->
		tell(File),
		cfg2ces_2(CFG,Bindings),
		told
	;
		cfg2ces_2(CFG,Bindings)
	),
	!.

cfg2ces_2(CFG,Bindings) :-
	init_db,
	set_prolog_flag(print_write_options,[quoted(false),numbervars(true)]),
	assert_cfg_into_db(CFG,Bindings),
	identify_loops,
	(option(dot(Dot_file))->
		draw_initial_graph(Dot_file)
		;
		true),	
	assert(loop_header(nil)),
	store_nodes_in_loop,
	(option(dot(Dot_file))->
		draw_initial_graph(Dot_file)
		;
		true
	),
	collect_all_loops(nil,Loops),
	reverse([nil|Loops],Loops_rev),
	maplist(extract_loop,Loops_rev),
	add_leafs,
	((option(slice),\+irreducible(_))->
		maplist(slice,Loops_rev)
		;
		true
	),
	(option(ces_dot(Ces_dot_file))->
		draw_ces_graph(Ces_dot_file)
		;
		true),
	print_io_vars,
	print_eqs.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Preparing the database of rules
assert_cfg_into_db(cfg(Edges),Bindings) :-
	Edges=[e(StartNode,_,_,_)|_],
	StartNode=..[Start_name|_],
	assert(cfg_entry(Start_name)),
	assert_cfg_into_db_1(Edges,Bindings,Nodes_1),
	sort(Nodes_1,Nodes),
	assert(cfg_nodes(Nodes)).


assert_cfg_into_db_1([],_,[]).
assert_cfg_into_db_1([e(Head,Call,C,Cs)|Es],Bindings,[S,T|Ns]) :-
	Head =.. [S|Vs],
	Call =.. [T|PVs],
	save_ground_name(S,Vs,Bindings),
	assert(cfg_edge(S,T)),
	assert(cfg_edge_rev(T,S)),
	assert(pcfg_edge(S,T,C,cons(Vs,PVs,Cs))), 
	assert_cfg_into_db_1(Es,Bindings,Ns).

save_ground_name(Name,_Vars,_Bindings):-
	ground_term(Name,_,_),!.
	
save_ground_name(Name,Vars,Bindings):-
	copy_term((Vars,Bindings),(Vars2,Bindings2)),
	maplist(substitute_numbervars,Bindings2,Bindings3),
	max_var_number(Bindings3,0,Max),
	Max1 is Max+1,
	maplist(unify_eq,Bindings3),
	assert(ground_term(Name,Vars2,Max1)).
	

unify_eq(X=X).
	
substitute_numbervars(Atom=Var,'$VAR'(Pos)=Var):-
	atom_chars(Atom,[Capital|Number_chars]),
	char_type(Capital,upper),
	(
		Number_chars=[],
		Number=0
	; 
		is_number_char_list(Number_chars),
		number_chars(Number,Number_chars)
	),!,
	char_code(Capital,Code),
	char_code('A',Code_ini),
	Pos is (Code-Code_ini)+ (26*Number).
	
substitute_numbervars(Atom=Var,Atom=Var).
	
is_number_char_list(List):-
	char_code('0',Zero),
	char_code('9',Nine),
	is_number_char_list_1(List,Zero,Nine).
	
is_number_char_list_1([],_Zero,_Nine).
is_number_char_list_1([Ch|Chs],Zero,Nine):-
	char_code(Ch,Ch_code),
	Ch_code=< Nine,
	Ch_code>= Zero,
	is_number_char_list_1(Chs,Zero,Nine).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% START: identify loops

%%
%% loops identification using the algorithm described in
%%
%%   Tao Wei, Jian Mao, Wei Zou, Yu Chen:
%%   A New Algorithm for Identifying Loops in Decompilation.
%%   Static Analysis, 14th International Symposium, SAS 2007, Kongens Lyngby, 
%%   Denmark, August 22-24, 2007, Proceedings. Lecture Notes in Computer Science 4634 
%%   Springer 2007, ISBN 978-3-540-74060-5, Pages 170-183.
%%

identify_loops :-
	cfg_nodes(N),
	maplist(initialize_loop_info,N),
%	identify_loops_initialization(N),
	cfg_entry(H0),
	trav_loops_DFS(H0,1, _Ret),
	!.
identify_loops(CFG_Signature) :-
	throw(identify_loops_failed(CFG_Signature)).


%%
%%
initialize_loop_info(B):-
	set_dfsp_pos(B,0),
	set_iloop_header(B,nil).

%%
%%
trav_loops_DFS(B0, DFSP_pos, Ret) :-
	mark_as_traversed(B0),
	set_dfsp_pos(B0,DFSP_pos),
	findall(A,cfg_edge(B0,A),Succ_B0),        % the successors of B0
	trav_loops_DFS_1(Succ_B0, B0, DFSP_pos, Ret).


trav_loops_DFS_1([], B0, _DFSP_pos, Ret) :-
	set_dfsp_pos(B0,0),
	iloop_header(B0,Ret).
trav_loops_DFS_1([B|Bs], B0, DFSP_pos, Ret) :-
	trav_loops_DFS_2(B, B0, DFSP_pos),
	trav_loops_DFS_1(Bs, B0, DFSP_pos, Ret).


trav_loops_DFS_2(B, B0, DFSP_pos) :-  % case(A)
	\+ traversed(B),
	!,
	DFSP_pos_aux is DFSP_pos+1,
	trav_loops_DFS(B, DFSP_pos_aux, NH),
	tag_lhead(B0, NH).

trav_loops_DFS_2(B, B0, _DFSP_pos) :-  % case(B)
	dfsp_pos(B,DFSP_pos_B),
	DFSP_pos_B > 0,
	!,
	mark_as_loop_header(B),
	tag_lhead(B0,B).

trav_loops_DFS_2(B, _B0, _DFSP_pos) :-  % case(C)
	iloop_header(B,nil),
	!.

trav_loops_DFS_2(B, B0, _DFSP_pos) :-  % case(D)
	iloop_header(B,H),
	dfsp_pos(H,DFSP_pos_H),
	DFSP_pos_H > 0,
	!,
	tag_lhead(B0,H).

trav_loops_DFS_2(B, B0, _DFSP_pos) :-  % case(E)
	iloop_header(B,H),
	mark_as_reentry(B,(from(B0),loop(H))),
	mark_irreducible(H),
	trav_loops_DFS_3(B0,H).

%%
trav_loops_DFS_3(B0,H) :-	% the while loop of case E
	iloop_header(H,H_aux),
	( H_aux == nil -> 
	  true
	;
	  dfsp_pos(H_aux,DFSP_pos_H_aux),
	  ( DFSP_pos_H_aux > 0 ->
	    tag_lhead(B0,H_aux)
	  ;
	    mark_irreducible(H_aux),
	    trav_loops_DFS_3(B0,H_aux)
	  )
	).

tag_lhead(B,H) :-
	( (B=H ; H=nil) -> 
	  true 
	; 
	  tag_lhead_1(B,H) 
	).

tag_lhead_1(Cur1, Cur2) :-
	iloop_header(Cur1,IH),
	(IH == nil -> 
	  set_iloop_header(Cur1,Cur2)
	;
	  (IH == Cur2 ->	% IH not nil
	    true
	    ;
	    dfsp_pos(IH,DFSP_pos_IH),
	    dfsp_pos(Cur2,DFSP_pos_Cur2),
	    ( DFSP_pos_IH < DFSP_pos_Cur2 ->  
	      set_iloop_header(Cur1,Cur2),
	      tag_lhead_1(Cur2, IH)
	    ;
	      tag_lhead_1(IH, Cur2)
	    )
	  )
	).


mark_as_traversed(B) :-
	assertz(traversed(B)).


set_iloop_header(A,B) :-
	(retract(iloop_header(A,C)) ->
	  retractall(iloop_header_rev(C,A))
	;
	  true
	),
	assertz(iloop_header(A,B)),
	assertz(iloop_header_rev(B,A)).


set_dfsp_pos(A,B) :-
	retractall(dfsp_pos(A,_)),
	assertz(dfsp_pos(A,B)).
     
mark_irreducible(B) :-
	assertz(irreducible(B)).

mark_as_reentry(A,B) :-
	assertz(reentry(A,B)).

mark_as_loop_header(B) :-
	(loop_header(B) -> true ; assertz(loop_header(B))).




%%%% END: identify loops
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fill the predicate node_in_loop which assigns each node to a loop
store_nodes_in_loop:-
	cfg_nodes(Nodes),
	maplist(store_node_in_loop,Nodes).

store_node_in_loop(Node):-
	loop_header(Node),!,
	assert(node_in_loop(Node,Node)).
store_node_in_loop(Node):-
	\+traversed(Node),!,
	format('% node ~p not reachable~n',[Node]).
	
store_node_in_loop(Node):-
	iloop_header(Node,Header),
	assert(node_in_loop(Node,Header)).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Collect loops in topological order
collect_all_loops(Loop,All_loops):-
	findall(Child,
		  (
		  iloop_header(Child,Loop),
		  loop_header(Child)
		  ),
		Children),
	sort_children(Children,Sorted_children),
	maplist(collect_all_loops,Sorted_children,Grand_children),
	ut_flat_list([Sorted_children,Grand_children],All_loops).


sort_children(Children,Sorted_children_rev):-
	compute_pred_graph(Children,Map_pred),
	get_topological_sorting(Map_pred,[],Sorted_children),
	reverse(Sorted_children,Sorted_children_rev).
	
compute_pred_graph(Nodes,Map_pred):-
	from_list_sl(Nodes,Nodes_set),
	foldl(compute_pred_set(Nodes_set),Nodes_set,[],Map_pred).

:-dynamic pred_set/2.

compute_pred_set(Nodes_set,Node,Accum,[(Node,Preds_set)|Accum]):-
	findall(Pred,
	     (
	     cfg_edge_rev(Node,Caller),
	     node_in_loop(Caller,Pred),Pred\=Node,
	     contains_sl(Nodes_set,Pred)
	     ),Preds),
	     from_list_sl(Preds,Preds_set),
	     assert(pred_set(Node,Preds_set)).
	
get_topological_sorting([],Sorted_nodes,Sorted_nodes).

get_topological_sorting(Pred_graph,Accum,Sorted_nodes):-
	get_no_pred(Pred_graph,[],Nodes,Pred_graph2),
	(Nodes\=[]->
		maplist(remove_preds(Nodes),Pred_graph2,Pred_graph3),
		append(Nodes,Accum,Accum2),
		get_topological_sorting(Pred_graph3,Accum2,Sorted_nodes)
		;
		throw(error('cycle among siblings:',Pred_graph))
	).
	
% get iconstrs with no predecessors
get_no_pred([],Accum,Accum,[]).
get_no_pred([(Node,[])|Map],Accum,Nodes,Map_out):-!,
	insert_sl(Accum,Node,Accum2),
	get_no_pred(Map,Accum2,Nodes,Map_out).
	
get_no_pred([Other|Map],Accum,Nodes,[Other|Map_out]):-
	get_no_pred(Map,Accum,Nodes,Map_out).	

%remove predecessors 	
remove_preds(Pred_set,(Node,Set),(Node,Set2)):-
	difference_sl(Set,Pred_set,Set2).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% add base cases for the leafs of the cfg
add_leafs:-
	cfg_nodes(Nodes),
	include(is_leaf,Nodes,Leafs),
	include(traversed,Leafs,Reachable_leafs),
	maplist(add_leaf,Reachable_leafs).

add_leaf(Leaf):-
	cfg_edge_rev(Leaf,Caller),
	
	eq(_Id,Head,_,Calls,_),
	functor(Head,Caller,_),
	member(Call,Calls),
	functor(Call,Leaf,N_leaf),!,
	
	length(Vars,N_leaf),
	Head_leaf=..[Leaf|Vars],
	save_equation(Head_leaf,0,[],[]).
	
	
is_leaf(Node):-
	\+cfg_edge(Node,_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% extract loops


extract_loop(H):-
	(option(add_outs)->cond_add_abort_edge(H);true),
	get_extra_loop_vars(H),
	
	 % and the loop_cont node in case there were no exits edges
	 (iloop_header(H,Father_loop)->
	 	loop_cont_name(Loop_cont_suffix),
	 	atom_concat(H,Loop_cont_suffix,LoopCont_node),
	 	store_loop_cont_node_in_loop(LoopCont_node,Father_loop)
	 	;
	 	true
	),
	findall(Node,node_in_loop(Node,H),Nodes),
	maplist(transform_edges_from,Nodes).

cond_add_abort_edge(nil):-!.

cond_add_abort_edge(H):-
	add_abort_edge(H).
cond_add_abort_edge(_).

add_abort_edge(Loop_header):-
	cond_add_exit_location(Exit_location),
	%get the head vars from any edge
	pcfg_edge(Loop_header,_,_,cons(Head_vars,_,_)),
	assertz(pcfg_edge(Loop_header,Exit_location,0,cons(Head_vars,[],[]))),
	%add all the other information predicates
	assertz(cfg_edge(Loop_header,Exit_location)),
	assertz(cfg_edge_rev(Exit_location,Loop_header)).

cond_add_exit_location(Exit_location):-
	exit_location(Exit_location),!.

cond_add_exit_location(exit_location):-
	retract(cfg_nodes(Nodes)),
	assertz(cfg_nodes([exit_location|Nodes])),
	assertz(exit_location(exit_location)),
	assertz(traversed(exit_location)),
	assertz(iloop_header(exit_location,nil)),
	assertz(iloop_header_rev(nil,exit_location)),
	assertz(node_in_loop(exit_location,nil)).
	
transform_edges_from(Node):-
	retract(pcfg_edge(Node,Dest,C,Cons)),
	(is_in_node(Node,Dest)->
	 transform_in_node(Node,Dest,C,Cons)
	 ;
	 (is_out_node(Node,Dest)->
	     transform_out_node(Node,Dest,C,Cons)
	   ;
	     transform_normal_node(Node,Dest,C,Cons)
	   )
	),fail.
transform_edges_from(_Node).

transform_in_node(Node,Dest,C,cons(Head_vars,Call_vars,Cs)):-
	node_in_loop(Node,Origin_loop),
	loop_has_new_vars(Origin_loop,N_extra_vs_origin_loop),
	node_in_loop(Dest,Dest_loop),
	loop_has_new_vars(Dest_loop,N_extra_vs_dest_loop),

	
	%now create new head for the node
	length([Flag2|Origin_loop_extra_vars],N_extra_vs_origin_loop),
	append(Head_vars,[Flag2|Origin_loop_extra_vars],Head_vars_new),
	Head=..[Node|Head_vars_new],
	
	%create the extra out vars
	length([Flag|Out_vars],N_extra_vs_dest_loop),
	%create call to the modified inner loop
	append(Call_vars,[Flag|Out_vars],Call_vars_total),	
	Call_dest=..[Dest|Call_vars_total],
	
	% create call to loop_cont
	create_cont_list(Dest_loop,Origin_loop,	[Flag|Out_vars],[Flag2|Origin_loop_extra_vars],Cont_calls),
	(option(loop_cost_model)->C2=0;C2=C),
	save_equation(Head,C2,[Call_dest|Cont_calls],Cs),!.
	
transform_in_node(Node,Dest,_,_):-
	throw(failed_to_transform_in_edge(Node,Dest)).
	
create_cont_list(Dest_loop,Origin_loop,	[Flag|Out_vars],Final_out_vars,Cont_calls):-
	loop_cont_name(Loop_cont_suffix),
	atom_concat(Dest_loop,Loop_cont_suffix,LoopCont_Node),
	node_in_loop(LoopCont_Node,Cont_node_loop),
	(Cont_node_loop=Origin_loop->
		append([Flag|Out_vars],Final_out_vars,Loop_cont_vars),
		Loop_cont=..[LoopCont_Node|Loop_cont_vars],
		Cont_calls=[Loop_cont]
		;
		loop_has_new_vars(Cont_node_loop,N_extra_cont_loop),
		length([Flag2|Origin_loop_extra_vars],N_extra_cont_loop),
		append([Flag|Out_vars],[Flag2|Origin_loop_extra_vars],Loop_cont_vars),
		Loop_cont=..[LoopCont_Node|Loop_cont_vars],
		create_cont_list(Cont_node_loop,Origin_loop,[Flag2|Origin_loop_extra_vars],Final_out_vars,Cont_calls2),
		Cont_calls=[Loop_cont|Cont_calls2]
	).

transform_out_node(Node,Dest,C,cons(Head_vars,Call_vars,Cs)):-
	node_in_loop(Node,Origin_loop),
	(option(continuation_style),pred_set(Origin_loop,[Father_loop])
		;
	iloop_header(Origin_loop,Father_loop)
	),
	get_exit_id(Dest,Exit_id),
	loop_has_new_vars(Origin_loop,N_extra_vs_origin_loop),

	%extra vars for the base case
	length(Extra_vars_base_case,N_extra_vs_origin_loop),
	%instantiate extra vars for base case
	append([Exit_id|Call_vars],_,Extra_vars_base_case),
	%build the base case
	append(Head_vars,Extra_vars_base_case,Head_vars_new),
	Head_base=..[Node|Head_vars_new],
	
	(option(loop_cost_model)->C2=0;C2=C),
	save_equation(Head_base,C2,[],Cs),
	
	%build the loop_cont edge! not equation
	loop_cont_name(Loop_cont_suffix),
	atom_concat(Origin_loop,Loop_cont_suffix,LoopCont_node),
	%generate new call vars of the right length
	length(Call_vars,N_call_vars),
	length(New_call_vars,N_call_vars),
	% generate head vars for the cont_loop node
	length(Head_loop_cont_vars,N_extra_vs_origin_loop),
	append([Exit_id|New_call_vars],_,Head_loop_cont_vars),
	store_loop_cont_node_in_loop(LoopCont_node,Father_loop),
	assert(cfg_edge(LoopCont_node,Dest)),
	assert(cfg_edge_rev(Dest,LoopCont_node)),
	assert(pcfg_edge(LoopCont_node,Dest,0,cons(Head_loop_cont_vars,New_call_vars,Cs))),!.

transform_out_node(Node,Dest,_,_):-
	throw(failed_to_transform_out_edge(Node,Dest)).
	
	
store_loop_cont_node_in_loop(Node,Loop):-
	node_in_loop(Node,Loop),!.
store_loop_cont_node_in_loop(Node,Loop):-
	assert(node_in_loop(Node,Loop)).

transform_normal_node(Node,Dest,C,cons(Head_vars,Call_vars,Cs)):-
	node_in_loop(Node,Loop),
	loop_has_new_vars(Loop,N),
	length(New_vars,N),
	append(Head_vars,New_vars,Head_vars_new),
	append(Call_vars,New_vars,Call_vars_new),
	Head=..[Node|Head_vars_new],
	Call=..[Dest|Call_vars_new],
	
	(option(loop_cost_model)->
		(Dest=Loop->
			C2=1
			;
			C2=0
		)
		;C2=C),
	save_equation(Head,C2,[Call],Cs),!.

transform_normal_node(Node,Dest,_,_):-
	throw(failed_to_transform_normal_edge(Node,Dest)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_extra_loop_vars(nil):-
	save_loop_has_new_vars(nil,1).
	
get_extra_loop_vars(H):-
	loop_header(H),
	findall((Dest,N),
		(
		 node_in_loop(Node,H),
		 cfg_edge(Node,Dest),
		 is_out_node(Node,Dest),
		 pcfg_edge(Node,Dest,_,cons(_,V_out,_)),
		 length(V_out,N)
		)
	,Nodes),
	sort(Nodes,Nodes1),
%	format(user_output,'loop: ~p ~n Exits  ~p ~n',[H,Nodes2]),
	maplist(tuple,_,N_vars,Nodes1),
	max_list([0|N_vars],N_new_vars),
	N_new_vars1 is N_new_vars +1,
	save_loop_has_new_vars(H,N_new_vars1).
	
is_in_node(Origin,Dest):-
	node_in_loop(Origin,Loop1),
	node_in_loop(Dest,Loop2),
	Loop1\=Loop2,
	(
		iloop_header_trans(Loop2,Loop1)
		
	;
		option(continuation_style),
		iloop_header(Loop2,Other),
		iloop_header(Loop1,Other)
	).

iloop_header_trans(Loop2,Loop1):-
	iloop_header(Loop2,Loop1),!.
iloop_header_trans(Loop2,Loop1):-
	iloop_header(Loop2,Loop_aux),
	iloop_header_trans(Loop_aux,Loop1).
	
	
is_out_node(Origin,Dest):-
	node_in_loop(Origin,Loop1),Loop1\=nil,
	node_in_loop(Dest,Loop2),
	Loop1\=Loop2,
	\+iloop_header(Loop2,Loop1).
	
%%%% END: extract loops





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% slicing

slice(Loop_header):-
	slice_unmodified_ovars(Loop_header,Unmodified_ins),
	slice_unused_ivars(Loop_header,Unmodified_ins).

slice(Loop_header):-
	throw(failed_slicing(Loop_header)).

%remove out variables that are not modified during the loop
slice_unmodified_ovars(Loop_header,Unused_later_ipositions):-
	get_eqs_in_loop_split(Loop_header,Non_rec_eqs,Rec_eqs),
	get_unmodified_ivars(Rec_eqs,Unmodified_ipositions),
	format('% unmodified input variables in loop ~p: ~p ~n',[Loop_header,Unmodified_ipositions]),
	get_matching_ovars(Non_rec_eqs,Unmodified_ipositions,Common_out_positions),	
	%if the only exit nodes are abort nodes we do not need the output variables
	(Common_out_positions=top ->
		get_all_output_matches(Loop_header,Common_out_positions1),
		format('% removed  all output variables in loop ~p ~n',[Loop_header]),
		Unused_later_ipositions=Unmodified_ipositions
	;
		maplist(tuple,Unused_later_ipositions,Removed_outs,Common_out_positions),
		format('% removed  output variables ~p in loop ~p ~n',[Removed_outs,Loop_header]),
		Common_out_positions1=Common_out_positions
	),
	remove_ovars(Loop_header,Common_out_positions1).

	
%remove input variables that are not modified and not used
slice_unused_ivars(Loop_header,Unused_later_ipositions):-
	get_unused_ivars(Loop_header,Unused_later_ipositions,Unused_positions),
	format('% remove in vars  ~p in loop ~p ~n',[Unused_positions,Loop_header]),
	remove_ivars(Loop_header,Unused_positions).

%%%%%%%%%%%%%%%%%%%%%%%%

get_unmodified_ivars(Rec_eqs,Set):-
	maplist(get_CE_unmodified_ivars,Rec_eqs,Unmodified_sets),
	reduce(intersection_sl,Unmodified_sets,Set).
	

get_CE_unmodified_ivars(Id,Set):-
	eq(Id,Head,_Cost,Calls,_Cs),
	last(Calls,Call),
	get_head_significant_ivars(Head,In1),
	get_head_significant_ivars(Call,In2),
	get_unmodified_positions(In1,In2,1,Set).


get_unmodified_positions([],_,_,[]):-!.
get_unmodified_positions(_,[],_,[]):-!.
get_unmodified_positions([V|In],[V2|In2],N,Set):-
	N1 is N+1,
	get_unmodified_positions(In,In2,N1,Set1),
	(V==V2->
		Set=[N|Set1]
		;
		Set=Set1
	).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_matching_ovars(Non_rec_eqs,Positions,Common_out_positions):-
	maplist(check_matching_base_case(Positions),Non_rec_eqs,Out_matches),
	format('% matching input-output vars: ~p ~n',[Out_matches]),
	foldl(intersection_with_top,Out_matches,top,Common_out_positions).


check_matching_base_case(Positions,Id,Matches_set):-
	eq(Id,Head,_Cost,[],_Cs),
    get_head_input_output(Head,In,[Exit|Out]),
    (exit_id(exit_location,Exit)->
    	Matches_set=top
    	;
    	
		numbervars((In,Out),0,_),
		check_matching_base_case_aux(Positions,In,Out,Matches),
		from_list_sl(Matches,Matches_set)
	).

check_matching_base_case_aux([],_In,_Out,[]).
check_matching_base_case_aux([P|Ps],In,Out,[(P_out,P)|Rest]):-
	nth1(P,In,Var),
	nth1(P_out,Out,Var),!,
	check_matching_base_case_aux(Ps,In,Out,Rest).
	
check_matching_base_case_aux([_P|Ps],In,Out,Rest):-
	check_matching_base_case_aux(Ps,In,Out,Rest).
	

intersection_with_top(top,Set,Set):-!.
intersection_with_top(Set,top,Set):-!.
intersection_with_top(Set1,Set2,Set):-
	intersection_sl(Set1,Set2,Set).
	
get_all_output_matches(Loop_header,Matches):-
	loop_has_new_vars(Loop_header,N_extra),
	N is N_extra-1,
	get_n_trivial_matches(1,N,Matches).
	
get_n_trivial_matches(I,N,[]):-
	I >= N,!.
get_n_trivial_matches(I,N,[(I,none)|Matches]):-
	I1 is I+1,
	get_n_trivial_matches(I1,N,Matches).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5
remove_ovars(Loop_header,Matches):-
	maplist(tuple,Outs,_,Matches),
	get_eqs_in_loop(Loop_header,Eqs),
	maplist(remove_ovars_loop_eq(Outs),Eqs),

	get_loop_calling_eqs(Loop_header,Calling_eqs),
	maplist(remove_ovars_in_calling_eq(Matches,Outs),Calling_eqs),
	
	length(Matches,N_removed),
	assert(removed_n_outs(Loop_header,N_removed)).


	
remove_ovars_loop_eq(Outs,Id):-
	retract(eq(Id,Head,Cost,Calls,Cs)),
	remove_ovars_head(Outs,Head,Head2),
	(   Calls=[Call],
		remove_ovars_head(Outs,Call,Call2),
		Calls2=[Call2]
	;   Calls=[Other,Call],
		remove_ovars_head(Outs,Call,Call2),
		Calls2=[Other,Call2]
	;
		Calls=[],
		Calls2=[]
	),
	assert(eq(Id,Head2,Cost,Calls2,Cs)).
		
remove_ovars_head(Outs,Head,Head2):-
	functor(Head,F,_),
	get_head_input_output(Head,In,[Exit|Out]),
	remove_elems(Outs,1,Out,Out2),
	append(In,[Exit|Out2],Vars2),
	Head2=..[F|Vars2].
	
remove_elems([],_Index,Outs,Outs).
remove_elems([Index|Ns],Index,[_Out|Outs],Outs2):-!,
	Index1 is Index+1,
	remove_elems(Ns,Index1,Outs,Outs2).
remove_elems([N|Ns],Index,[Out|Outs],[Out|Outs2]):-
	N>Index,
	Index1 is Index+1,
	remove_elems([N|Ns],Index1,Outs,Outs2).	

		


remove_ovars_in_calling_eq(Matches,Outs,Id):-
	retract(eq(Id,Head,Cost,Calls,Cs)),
	Calls=[Call_loop,Call_cont],
	remove_ovars_head(Outs,Call_loop,Call_loop2),
	maplist(get_vars_substitutions(Call_loop),Matches,Substitutions),
	foldl(apply_substitutions,Substitutions,Call_cont,Call_cont2),
	Calls2=[Call_loop2,Call_cont2],
	assert(eq(Id,Head,Cost,Calls2,Cs)).

%for trivial matches we do trivial substitutions
get_vars_substitutions(Call,(Out_pos,In_pos),(Out_var,Out_var)):-
	In_pos==none,!,
	get_head_input_output(Call,_,[_Exit|Outs]),
	nth1(Out_pos,Outs,Out_var).
	
get_vars_substitutions(Call,(Out_pos,In_pos),(Out_var,In_var)):-
	get_head_input_output(Call,Ins,[_Exit|Outs]),
	nth1(Out_pos,Outs,Out_var),
	nth1(In_pos,Ins,In_var).

apply_substitutions((Out_var,In_var),Head,Head2):-
	Head=..[F|Vars],
	maplist(substitute((Out_var,In_var)),Vars,Vars2),
	Head2=..[F|Vars2].
substitute((A,B),C,B):-
	A==C,!.
substitute(_,C,C).


		
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% second part of slicing, remove unused input vars


get_unused_ivars(Loop_header,Initial_set,Set):-
	get_eqs_in_loop(Loop_header,Eqs),
	maplist(get_CE_unused_ivars(Initial_set),Eqs,Sets),
	reduce(intersection_sl,Sets,Set).

get_CE_unused_ivars(Initial_set,Id,Set):-
	eq(Id,Head,_,Calls,Cs),
	term_variables(Cs,Used),
	from_list_sl(Used,Used_set),
	get_used_vars_calls(Calls,Initial_set,Used_set,Used2),
	get_head_significant_vars(Head,_,Vars),
	exclude(used_vars(Used2,Vars),Initial_set,Set).

used_vars(Used,Args,N):-
	nth1(N,Args,V),
	contains_sl(Used,V).
	
get_used_vars_calls([],_,Used,Used).

% this is a recursive call, we ignore the indices where the ivar appears
get_used_vars_calls([Call],Initial,Used,Used2):-
	get_head_significant_vars(Call,_,Vars),
	exclude_index(Initial,1,Vars,Vars2),
	term_variables(Vars2,Vs),
	from_list_sl(Vs,Vs_set),
	union_sl(Used,Vs_set,Used2).

% all the variables in the first call and the second call is recursive, it is reduced to the previous case	
get_used_vars_calls([Call,Cont],Initial,Used,Used2):-	
	term_variables(Call,Vars),
	from_list_sl(Vars,Vars_set),
	union_sl(Vars_set,Used,Used1),
	get_used_vars_calls([Cont],Initial,Used1,Used2).
	
exclude_index([],_N,Vs,Vs).
exclude_index([N|Ns],N,[_V|Vs],Vs2):-
	Index1 is N+1,
	exclude_index(Ns,Index1,Vs,Vs2).
exclude_index([N|Ns],Index,[V|Vs],[V|Vs2]):-
	N>Index,
	Index1 is Index+1,
	exclude_index([N|Ns],Index1,Vs,Vs2).
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


remove_ivars(Loop_header,In):-
	get_loop_calling_eqs(Loop_header,Loop_eqs),
	maplist(remove_ivars_in_calling_eq(In),Loop_eqs),
	get_eqs_in_loop(Loop_header,Calling_eqs),
	maplist(remove_ivars_loop_eq(In),Calling_eqs).


remove_ivars_in_calling_eq(In,Id):-
	retract(eq(Id,Head,Cost,Calls,Cs)),
	Calls=[Call_loop,Call_cont],
	remove_ivars_head(In,Call_loop,Call_loop2),
	Calls2=[Call_loop2,Call_cont],
	assert(eq(Id,Head,Cost,Calls2,Cs)).

remove_ivars_loop_eq(Ins,Id):-
	retract(eq(Id,Head,Cost,Calls,Cs)),
	adapt_ground_term(Head,Ins),
	remove_ivars_head(Ins,Head,Head2),
	(   Calls=[Call],
		remove_ivars_head(Ins,Call,Call2),
		Calls2=[Call2]
	;   Calls=[Other,Call],
		remove_ivars_head(Ins,Call,Call2),
		Calls2=[Other,Call2]
	;
		Calls=[],
		Calls2=[]
	),
	assert(eq(Id,Head2,Cost,Calls2,Cs)).
		


remove_ivars_head(Ins,Head,Head2):-
	get_head_significant_vars(Head,Prefix,Vars),
	functor(Head,Name,_),
	remove_elems(Ins,1,Vars,Vars2),
	append(Prefix,Vars2,Vars_final),
	Head2=..[Name|Vars_final].
	
adapt_ground_term(Head,Ins):-
	get_head_input_output(Head,In,_),
	functor(Head,Name,_),
	(retract(ground_term(Name,In,N))->
		remove_ivars_head(Ins,Head,Head2),
		get_head_input_output(Head2,In2,_),
		assert(ground_term(Name,In2,N))
	;
		true
	).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Print cost relations

print_io_vars:-
	setof((F,N),
	 C^Call^Cs^Head^Id^(
	  	eq(Id,Head,C,Call,Cs),
	  	functor(Head,F,N)
	  	),Heads),
	maplist(print_io_vars_1,Heads).
print_io_vars_1((Name,N)):-
	functor(Head,Name,N),
	get_head_input_output(Head,Input_vars,Out_vars),
	(ground_term(Name,Input_vars,Numvar_ini)->
		true
	;
		Numvar_ini=0
	),
	numbervars(Head,Numvar_ini,_),
	format('~p.~n',[input_output_vars(Head,Input_vars,Out_vars)]),!.
print_io_vars_1(_).	

print_eqs:-
	cfg_entry(Entry),
	eq(Id,Head,C,Call,Cs),
	Head=..[Entry|_],!,
	retract(eq(Id,_,_,_,_)),
	Head=..[Name|Vars],
	(ground_term(Name,Input_vars,Numvar_ini)->
	  append(Input_vars,_,Vars)
	; 
         Numvar_ini=0),
	numbervars(eq(Head,C,Call,Cs),Numvar_ini,_),
	format('~p.~n',[eq(Head,C,Call,Cs)]),
	print_eqs_1.
	
print_eqs_1:-
	retract(eq(_Id,Head,C,Call,Cs)),	
	Head=..[Name|Vars],
	(ground_term(Name,Input_vars,Numvar_ini)->
	  append(Input_vars,_,Vars)
	; 
      Numvar_ini=0),
	numbervars(eq(Head,C,Call,Cs),Numvar_ini,_),
	format('~p.~n',[eq(Head,C,Call,Cs)]),
	fail.
print_eqs_1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Draw graphs
draw_ces_graph(File):-
    open(File, write, File_Handler),
	init_dot(File_Handler),
	%draw_initial_nodes(File_Handler),
	draw_loops(File_Handler),
	draw_ces_edges(File_Handler),
	finalize_dot(File_Handler),
	close(File_Handler),
	!.

draw_ces_edges(File_Handler):-
	eq(_Id,Head,Cost,Calls,_Cs),
	functor(Head,O,_),
	member(Call,Calls),
	functor(Call,D,_),
	short_name(O,O_name),
	short_name(D,D_name),
	(is_loop_cont(O)->
		Head=..[_,Exit|_]
	;
	    Exit=''
	),
	draw_edge(File_Handler,O_name,D_name,Cost,Exit),
	fail.
draw_ces_edges(_).


draw_initial_graph(File):-
    open(File, write, File_Handler),
	init_dot(File_Handler),
	%draw_initial_nodes(File_Handler),
	draw_loops(File_Handler),
	draw_edges(File_Handler),
	finalize_dot(File_Handler),
	close(File_Handler),
	!.

short_name(Name,Short_name):-
	cfg_entry(Name_entry),
	atom_concat(Prefix,'start',Name_entry),
	atom_concat(Prefix,Short_name,Name),!.
short_name(Name,Name).	

init_dot(File_Handler) :-
	format(File_Handler,"digraph mhp_info {~n~n",[]).

finalize_dot(File_Handler) :-
	format(File_Handler,"~n}~n",[]).

draw_initial_nodes(File_Handler):-
	cfg_nodes(Nodes),
	maplist(draw_node(File_Handler),Nodes).

draw_loops(File_Handler):-
	loop_header(Header),
	short_name(Header,Header_short),
	format(File_Handler,"subgraph cluster~p {~n ",[Header_short]),
	(Header\=nil->
		draw_node(File_Handler,Header)
		;
		true
	),
	draw_loop(File_Handler,Header),
	format(File_Handler,"}~n",[]),
	fail.
draw_loops(_).	
	
draw_loop(File_Handler,Header):-
	node_in_loop(Node,Header),
	draw_node(File_Handler,Node),
	fail.
draw_loop(_,_).

draw_edges(File_Handler):-
	pcfg_edge(O,D,Cost,cons(_Head_vars,_Call_vars,_Cs)),
	short_name(O,O_name),
	short_name(D,D_name),
	draw_edge(File_Handler,O_name,D_name,Cost,''),
	fail.
draw_edges(_).


draw_node(File_Handler,Node):-
	short_name(Node,Name),
	format(File_Handler,'"~p" ',[Name]),
	draw_exits(File_Handler,Node,Name),
	draw_shape(Node,File_Handler).

draw_exits(File_Handler,Node,Name):-
	node_in_loop(Node,Loop),
	loop_has_new_vars(Loop,N_extra),
	findall(Exit,
		(
		eq(_Id,Head,_,[],_),
		functor(Head,Node,N),
		Head=..[Node|Vars],
		N_exit is N-N_extra,
		nth0(N_exit,Vars,Exit)
		)
	, Exits),
	format(File_Handler,' [label="~p',[Name]),
	(Exits\=[]->
		format(File_Handler,' ~nExits:',[]),
		maplist(format_aux(File_Handler,'~p '),Exits)
	;
		true
	),
	format(File_Handler,'"',[]),!.
	
draw_exits(File_Handler,_Node,Name):-
	format(File_Handler,' [label="~p"',[Name]).
	
format_aux(File_Handler,Format,Elem):-
	format(File_Handler,Format,[Elem]).	
	
draw_shape(Name,File_Handler):-
	cfg_entry(Name),!,
	format(File_Handler,',shape=box,style="filled", fillcolor="blue"];~n',[]).	
draw_shape(Name,File_Handler):-
	loop_header(Name),!,
	format(File_Handler,',style="filled", fillcolor="grey"];~n',[]).

draw_shape(_,File_Handler):-
	format(File_Handler,',style="filled", fillcolor="white"];~n',[]).


draw_edge(File_Handler,O,D,Cost,''):-!,
	format(File_Handler,'"~p" -> "~p" [label=\"c:~p\"] ;~n',[O,D,Cost]).
draw_edge(File_Handler,O,D,Cost,Exit):-!,
	format(File_Handler,'"~p" -> "~p" [label=\"c:~p e: ~p\"] ;~n',[O,D,Cost,Exit]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Auxiliary predicates

is_loop_cont(Name):-
	loop_cont_name(Loop_cont_suffix),
	atom_concat(_,Loop_cont_suffix,Name).
	
	
get_loop_calling_eqs(Header,Eqs_set):-
	findall(Caller,
		(cfg_edge_rev(Header,Caller),
		\+node_in_loop(Caller,Header)),
		Callers),
	from_list_sl(Callers,Callers_set),	
	findall(Id,
		(
		member(Caller,Callers_set),
		eq(Id,Head,_Cost,Calls,_Cs),
		functor(Head,Caller,_),
		Calls=[Loop_call,_Cont],
		functor(Loop_call,Header,_)
		),Eqs),
	from_list_sl(Eqs,Eqs_set).

get_eqs_in_loop(Header,Eqs):-
	findall(Id,
		(
		node_in_loop(Name,Header),
		eq(Id,Head,_Cost,_Calls,_Cs),
		functor(Head,Name,_)
		), Eqs).

get_eqs_in_loop_split(Loop_header,Non_rec_eqs,Rec_eqs):-
	get_eqs_in_loop(Loop_header,Eqs),
	partition(is_eq_base_case,Eqs,Non_rec_eqs,Rec_eqs).
	
	
get_head_input_output(Head,In,Out):-
	functor(Head,Name,N_total),
	Head=..[_|Vars],
	node_in_loop(Name,Loop_header),
	loop_has_new_vars(Loop_header,N_extra),
	(removed_n_outs(Loop_header,N_removed);N_removed=0),
	N_extra2 is N_extra-N_removed,
	N_in is N_total-N_extra2,
	ut_split_at_pos(Vars,N_in,In,Out).

% loop cont terms have an extra variable at the beginning to identify the exit
% which has to be ignored for the slicing
get_head_significant_vars(Head,Prefix,Vars1):-
	Head=..[Name|Vars],
	(is_loop_cont(Name)->
		Vars=[First|Vars1],
		Prefix=[First]
		;
		Prefix=[],
		Vars=Vars1
	).
get_head_significant_ivars(Head,In1):-
	get_head_input_output(Head,In,_),
	functor(Head,Name,_),
	(is_loop_cont(Name)->
		In=[_|In1]
		;
		In=In1
	).
	
is_eq_base_case(Id):-
	eq(Id,_Head,_Cost,[],_Cs).

reduce(Predicate,[X|Xs],R):-
	foldl(Predicate,Xs,X,R).

tuple(X,Y,(X,Y)).

normalize_constraint(C,CN):-
	constraint_to_coeffs_rep(C,Coeff_rep),  % this to lines normalize
	coeffs_rep_to_constraint(Coeff_rep,CN).

constraint_to_coeffs_rep(Constr, coeff_rep(Coeffs,Rel,B)) :-
    Constr =.. [ Rel, L, R],
    is_relational(Rel),
    parse_le( L-R, Le_x),
    integrate_le(  Le_x, _Den, Coeffs_x + NegB), 
    unzip( Coeffs_x, Vars, Fracs),
    zip_with( '*', Fracs, Vars, Coeffs), 
    negate_fr( NegB, B).

coeffs_rep_to_constraint(coeff_rep(Coeffs,Op,B), Constraint) :-
	write_sum(Coeffs,Exp),
	Constraint =.. [ Op, Exp, B].


order_loops(Loops,Ordered_loops_rev):-
	maplist(annotate_loop(Loops),Loops,Ann_loops),!,
	order_loops_1(Ann_loops,[],Ordered_loops),
	reverse(Ordered_loops,Ordered_loops_rev),!.

order_loops_1([],Ord_loops,Ord_loops).
order_loops_1(Loops,Ord_loops,Ord_loops_out):-!,
	get_ready_loops(Loops,Sel_loops,Loops1),
	append(Ord_loops,Sel_loops,Ord_loops1),
	(Sel_loops=[]->
	 Loops1=[(L,_)|Loop11],
	 Loops2=[(L,[])|Loop11]
	;
	maplist(update_annotations(Ord_loops1),Loops1,Loops2)
	),


	order_loops_1(Loops2,Ord_loops1,Ord_loops_out).

get_ready_loops([],[],[]).
get_ready_loops([(Loop,[])|More],[Loop|More_ready],Not_ready):-!,
	get_ready_loops(More,More_ready,Not_ready).

get_ready_loops([Not|More],More_ready,[Not|Not_ready]):-
	get_ready_loops(More,More_ready,Not_ready).

update_annotations(Ready_loops,(Loop,Calls),(Loop,Calls1)):-
	exclude(member_inv(Ready_loops),Calls,Calls1).
member_inv(List,El):-
	member(El,List),!.

annotate_loop(Loops,Loop,(Loop,Callsp)):-
	include(cfg_edge_aux(Loop),Loops,Calls),
	exclude(equal(Loop),Calls,Callsp).
equal(L,L).

cfg_edge_aux(S,X):-
	cfg_edge(S,X,_,_).


save_loop_has_new_vars(H,N):-
	loop_has_new_vars(H,N),!.
save_loop_has_new_vars(H,N):-
	assertz(loop_has_new_vars(H,N)).


get_exit_id(Node,Id):-
	exit_id(Node,Id),!.
get_exit_id(Node,Id):-
	retract(last_id(N)),
	Id is N+1,
	assert(exit_id(Node,Id)),
	assert(last_id(Id)).

inc_counter_exits:-
	retract(counter_exits(N)),
	N1 is N+1,
	assert(counter_exits(N1)).