#!/usr/bin/prolog

:-module(cfg2ces_module,[main_cfg2ces/0,main_bin_cfg2ces/0]).

:-include('../../../src/search_paths.pl').



:- use_module(stdlib(linear_expression), [parse_le/2, integrate_le/3]).

:- use_module(stdlib(fraction),[negate_fr/2]).
:- use_module(stdlib(parsing_writing),[write_sum/2]).
:- use_module(stdlib(pair_list),[zip_with/4,unzip/3]).
:- use_module(stdlib(relational),[is_relational/1]).
:- use_module(stdlib(utils),[ut_flat_list/2]).


main_cfg2ces:-
    current_prolog_flag(argv, Args),
    cfg2ces(Args),
	halt.
        
main_bin_cfg2ces:-
    current_prolog_flag(argv, [_|Args]),
    cfg2ces(Args),
	halt.
        
save_exec:-
	make,
	check,
	prolog_history(disable),
	qsave_program('cfg2ces',[stand_alone(true),goal(main_bin),foreign(save)]),
	writeln('Binary package generated').

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

:- dynamic eq/4.
:- dynamic ground_term/3.
:- dynamic loop_has_new_vars/2.

:- dynamic option/1.
:- dynamic exit_location/1.

init_db :-
	retractall(traversed(_)),
	retractall(iloop_header(_,_)),
	retractall(iloop_header_rev(_,_)),
	retractall(dfsp_pos(_,_)),
	retractall(irreducible(_)),
	retractall(reentry(_,_)),
	retractall(loop_header(_)),
	retractall(cfg_edge(_,_)),
	retractall(cfg_edge_rev(_,_)),
	retractall(pcfg_edge(_,_,_,_)),
	retractall(cfg_entry(_)),
	retractall(cfg_nodes(_)),
	retractall(ground_term(_,_,_)),
	retractall(exit_location(_)),
	assert(last_id(1)),
	!.

get_exit_id(Node,Id):-
	exit_id(Node,Id),!.
get_exit_id(Node,Id):-
	retract(last_id(N)),
	Id is N+1,
	assert(exit_id(Node,Id)),
	assert(last_id(Id)).

cfg2ces([]):-format(user_error,'No file parameter received~n',[]).

cfg2ces([F|Other_args]) :-
	process_args(Other_args),
	catch(cfg2ces_1(F),Error,(format(user_error,'~p~n',[Error]),halt)),!.


process_args([]).
process_args(['-o',File|Args]):-!,
	assert(option(to_file(File))),
	process_args(Args).
process_args([loop_cost_model|Args]):-!,
	assert(option(loop_cost_model)),
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
	assert_cfg_into_db(CFG,Bindings),
	identify_loops,
	(\+irreducible(_)->
	assert(loop_header(nil)),
	store_nodes_in_loop,
	collect_all_loops(nil,Loops),
	reverse([nil|Loops],Loops_rev),
	maplist(extract_loop,Loops_rev)
	;
	 throw(irreducible_cfg)
	),
	print_io_vars,
	print_eqs.

print_io_vars:-
	setof((F,N),
	 C^Call^Cs^Vars^Head^(
	  	eq(Head,C,Call,Cs),
	  	Head=..[F|Vars],
	  	length(Vars,N)
	  	),Heads),
	maplist(print_io_vars_1,Heads).
print_io_vars_1((Name,N)):-
	length(Vars,N),	
	node_in_loop(Name,Loop),
	loop_has_new_vars(Loop,N_extra),
	length(Out_vars,N_extra),
	ground_term(Name,Input_vars,Numvar_ini),
	append(Input_vars,Out_vars,Vars),
	Head=..[Name|Vars],
	numbervars(Head,Numvar_ini,_),
	format('~p.~n',[input_output_vars(Head,Input_vars,Out_vars)]),!.
print_io_vars_1(_).	

collect_all_loops(Loop,All_loops):-
	findall(Child,
		  (
		   iloop_header(Child,Loop),
		  loop_header(Child)
		  ),
		Children),
	maplist(collect_all_loops,Children,Grand_children),
	ut_flat_list([Children,Grand_children],All_loops).

store_nodes_in_loop:-
	cfg_nodes(Nodes),
	maplist(store_node_in_loop,Nodes).

store_node_in_loop(Node):-
	loop_header(Node),!,
	assert(node_in_loop(Node,Node)).
store_node_in_loop(Node):-
	iloop_header(Node,Header),
	assert(node_in_loop(Node,Header)).
	
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
	iloop_header(Loop2,Loop1).
is_out_node(Origin,Dest):-
	node_in_loop(Origin,Loop1),Loop1\=nil,
	node_in_loop(Dest,Loop2),
	Loop1\=Loop2,
	\+iloop_header(Loop2,Loop1).


%%%% START: extract loops


extract_loop(H):-
	(option(add_outs)->cond_add_abort_edge(H);true),
	get_extra_loop_vars(H),
	findall(Node,node_in_loop(Node,H),Nodes),
	maplist(transform_edges_from,Nodes).

cond_add_abort_edge(nil):-!.

cond_add_abort_edge(H):-
%	findall((Node,Dest),
%		(
%		 node_in_loop(Node,H),
%		 cfg_edge(Node,Dest),
%		 is_out_node(Node,Dest)
%		)
%	,[]),!,
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
	assertz(exit_location(exit_location)),
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
	%create the extra out vars
	length([Flag|Out_vars],N_extra_vs_dest_loop),
	
	%create call to the modified inner loop
	append(Call_vars,[Flag|Out_vars],Call_vars_total),	
	Call_dest=..[Dest|Call_vars_total],
	
	%now create new head for the node
	length([Flag2|Origin_loop_extra_vars],N_extra_vs_origin_loop),
	append(Head_vars,[Flag2|Origin_loop_extra_vars],Head_vars_new),
	Head=..[Node|Head_vars_new],
	
	% create call to loop_cont
	atom_concat(loop_cont_,Dest_loop,LoopCont_Node),
	append([Flag|Out_vars],[Flag2|Origin_loop_extra_vars],Loop_cont_vars),
	Loop_cont=..[LoopCont_Node|Loop_cont_vars],
	
	(option(loop_cost_model)->C2=1;C2=C),
	assertz(eq(Head,C2,[Call_dest,Loop_cont],Cs)),!.
transform_in_node(Node,Dest,_,_):-
	throw(failed_to_transform_in_edge(Node,Dest)).

transform_out_node(Node,Dest,C,cons(Head_vars,Call_vars,Cs)):-
	node_in_loop(Node,Origin_loop),
	iloop_header(Origin_loop,Father_loop),
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
	assertz(eq(Head_base,C2,[],Cs)),
	
	%build the loop_cont edge! not equation
	atom_concat(loop_cont_,Origin_loop,LoopCont_node),
	%generate new call vars of the right length
	length(Call_vars,N_call_vars),
	length(New_call_vars,N_call_vars),
	% generate head vars for the cont_loop node
	length(Head_loop_cont_vars,N_extra_vs_origin_loop),
	append([Exit_id|New_call_vars],_,Head_loop_cont_vars),
	
	store_node_in_loop(LoopCont_node,Father_loop),
	assert(cfg_edge(LoopCont_node,Dest)),
	assert(cfg_edge_rev(Dest,LoopCont_node)),
	assert(pcfg_edge(LoopCont_node,Dest,0,cons(Head_loop_cont_vars,New_call_vars,Cs))),!.

transform_out_node(Node,Dest,_,_):-
	throw(failed_to_transform_out_edge(Node,Dest)).
store_node_in_loop(Node,Loop):-
	node_in_loop(Node,Loop),!.
store_node_in_loop(Node,Loop):-
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
		(loop_header(Dest)->
			C2=1
			;
			C2=0
		)
		;C2=C),
	assertz(eq(Head,C2,[Call],Cs)),!.

transform_normal_node(Node,Dest,_,_):-
	throw(failed_to_transform_normal_edge(Node,Dest)).


	
%%%% END: extract loops
	
tuple(X,Y,(X,Y)).

print_eqs:-
	cfg_entry(Entry),
	eq(Head,C,Call,Cs),
	Head=..[Entry|_],!,
	retract(eq(Head,C,Call,Cs)),
	Head=..[Name|Vars],
	(ground_term(Name,Input_vars,Numvar_ini)->
	  append(Input_vars,_,Vars)
	; 
         Numvar_ini=0),
	numbervars(eq(Head,C,Call,Cs),Numvar_ini,_),
	format('~p.~n',[eq(Head,C,Call,Cs)]),
	print_eqs_1.

print_eqs_1:-
	retract(eq(Head,C,Call,Cs)),	
	Head=..[Name|Vars],
	(ground_term(Name,Input_vars,Numvar_ini)->
	  append(Input_vars,_,Vars)
	; 
      Numvar_ini=0),
	numbervars(eq(Head,C,Call,Cs),Numvar_ini,_),
	format('~p.~n',[eq(Head,C,Call,Cs)]),
	fail.
print_eqs_1.

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

%%
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
	mark_as_reentry(B,(B0,B)),
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
	( 
	  IH == nil -> 
	  set_iloop_header(Cur1,Cur2)
	;
	  ( IH == Cur2 ->	% IH not nil
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
	( retract(iloop_header(A,C)) ->
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


next_level_loops([],[]).
next_level_loops([L|Ls],[LP|LPs]) :-
	iloop_header(L,LP),
	LP \== nil,
	!,
	next_level_loops(Ls,LPs).
next_level_loops([_|Ls],LPs) :-
	next_level_loops(Ls,LPs).

deepest_loops(Ls) :-
	findall(H,(
		   loop_header(H),
		   \+ (
		       loop_header(H1),
		       iloop_header(H1,H)
		      )
		  ),Ls).


%%%% END: identify loops






%Auxiliary predicates



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

inc_counter_exits:-
	retract(counter_exits(N)),
	N1 is N+1,
	assert(counter_exits(N1)).
