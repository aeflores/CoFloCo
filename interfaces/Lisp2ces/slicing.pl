:- module(slicing,[
		slice_cost_equations/4,print_sliced_iout/1
	]).

:- use_module(stdlib(set_list),[from_list_sl/2,insert_sl/3,union_sl/3,intersection_sl/3,difference_sl/3]).
:-use_module(basic_lisp,[eq/4]).

:-dynamic n_in_vars/2.
:-dynamic slice_eq/4.
:-dynamic important_in_vars/2.
:-dynamic important_out_vars/2.
:-dynamic scheduled/1.

:-dynamic caller_of/2.
:-dynamic influence_map/2.

slice_cost_equations(Entries,Cost_relations,Sliced_entries,Sliced_cost_relations):-
	maplist(save_initial_eq,Cost_relations),
	fixpoint_computation,
	%print_important_variables,
	get_sliced_eqs(Sliced_cost_relations),
	maplist(slice_entries,Entries,Sliced_entries).

slice_entries(entry(Term:Pre),entry(Term2:Pre)):-
	remove_variables_1(Term,Term2).

get_sliced_eqs(Eqs_sliced):-
	findall(Eq,
		(slice_eq(Head,Cost,Calls,Cs),Eq=eq(Head,Cost,Calls,Cs)),Eqs),
	maplist(remove_variables,Eqs,Eqs_sliced).

remove_variables(eq(Head,Cost,Calls,Cs),eq(Head2,Cost,Calls2,Cs)):-
	maplist(remove_variables_1,[Head|Calls],[Head2|Calls2]).
remove_variables_1(Term,Term2):-
	functor(Term,F,A),
	get_important(F/A,Important),
	Term=..[F|Vars],
	Important=..[F|Important_vars],
	keep_important(Vars,Important_vars,Vars1),
	Term2=..[F|Vars1].

keep_important([],[],[]).

keep_important([_|Vs],[Var|Vs2],Is):-
	var(Var),!,
	keep_important(Vs,Vs2,Is).
keep_important([V|Vs],[i|Vs2],[V|Is]):-
	keep_important(Vs,Vs2,Is).
keep_important([V|Vs],[o|Vs2],[V|Is]):-
	keep_important(Vs,Vs2,Is).	
	

get_important(F/A,Head3):-
   functor(Head,F,A),
   important_in_vars(Head,In),!,
   functor(Head,F,A),
   functor(Head2,F,A),
   important_out_vars(Head2,Out),
   Head=..[F|Vars1],
   Head2=..[F|Vars2],
   append(In_vars,[_,_,_],Vars1),
   append(_In_vars2,[Oi,Ol,Os],Vars2),
   append(In_vars,[Oi,Ol,Os],Vars3),
   Head3=..[F|Vars3],
   maplist(=(i),In),
   maplist(=(o),Out),
   save_in_vars(F,Vars3).
% for undefined stuff we just ignore everything
get_important(F/A,Head):-
	functor(Head,F,A),
	save_in_vars(F,[]).

save_in_vars(CR,_List_var):-
	n_in_vars(CR,_N),!.
save_in_vars(CR,List_var):-
	include(==(i),List_var,Ins),
	length(Ins,N),
	assert(n_in_vars(CR,N)).
	
print_important_variables:-
   important_in_vars(Head,In),
   functor(Head,F,A),
   functor(Head2,F,A),
   important_out_vars(Head2,Out),
   Head=..[F|Vars1],
   Head2=..[F|Vars2],
   append(In_vars,[_,_,_],Vars1),
   append(_In_vars2,[Oi,Ol,Os],Vars2),
   append(In_vars,[Oi,Ol,Os],Vars3),
   Head3=..[F|Vars3],
   maplist(=(i),In),
   maplist(=(o),Out),
   numbervars(Head3,0,_),
   writeln(Head3),
   fail.
print_important_variables.

	
print_sliced_iout([Name,N_args]):-
	functor(Head,Name,N_args),!,
	n_in_vars(Name,N_in),
	Head=..[Name|Vars],
	length(In,N_in),
	append(In,Out,Vars),
	numbervars(Vars,0,_),
	format("~q.~n",[input_output_vars(Head,In,Out)]).

count_occurrences(Set,Var,N,N1):-
	contains_sl(Set,Var),!,
	N1 is N+1.
count_occurrences(_Set,_Var,N,N).
	
save_initial_eq(Eq):-
	clean_constants(Eq,eq(Head,Cost,Calls,Cs)),
	assert(slice_eq(Head,Cost,Calls,Cs)),
	functor(Head,F,_),
	(scc_of_function(F,_)-> schedule(Head);true),
	initialize_important_vars(Head),
	maplist(save_caller(Head),Calls).
	
clean_constants(eq(Head,Cost,Calls,Cs),eq(Head2,Cost,Calls2,Cs2)):-
	maplist(clean_constants_1,[Head|Calls],[Head2|Calls2],Extra_cs),
	ut_flat_list([Extra_cs,Cs],Cs2).
clean_constants_1(Term,Term2,Cs):-
	Term=..[F|Vars],
	clean_constants_2(Vars,Vars2,Cs),
	Term2=..[F|Vars2].

clean_constants_2([],[],[]).
clean_constants_2([V|Vs],[V|Vs2],Cs):-
	var(V),!,
	clean_constants_2(Vs,Vs2,Cs).
clean_constants_2([Cnt|Vs],[V|Vs2],[Cnt=V|Cs]):-
	nonvar(Cnt),!,
	clean_constants_2(Vs,Vs2,Cs).

initialize_important_vars(Head):-
	functor(Head,F,A),
	functor(Head_fresh,F,A),
	(important_in_vars(Head_fresh,_)->
	   true
	;
	   assert(important_in_vars(Head_fresh,[]))
	),
	(important_out_vars(Head_fresh,_)->
	   true
	;
	   assert(important_out_vars(Head_fresh,[]))
	).

save_caller(Caller,Callee):-
	(caller_of(Callee,Caller)-> 
	  true
	;
	  assert(caller_of(Callee,Caller))
	).
	

	
fixpoint_computation:-
	retract(scheduled(F/A)),!,
	%writeln(F/A),
	functor(Head,F,A),
	((\+eq(Head,_,_,_),slice_eq(Head,_,_,_))->
	   propagate_vars_in_CR(F/A)
	;
	   propagate_vars_in_undefined_CR(Head)
	),
	fixpoint_computation.
fixpoint_computation.

propagate_vars_in_CR(F/A):-
	functor(Head,F,A),
	slice_eq(Head,Cost,Calls,Cs),
	propagate_vars_in_CE(Head,Cost,Calls,Cs),
	fail.
propagate_vars_in_CR(_).	

propagate_vars_in_CE(Head,_Cost,Calls,Cs):-
	get_initial_set(Head,Cs,Ini_set),
	propagate_backwards(Ini_set,Calls,New_set),
	get_input_vars(Head,In_set),
	intersection_sl(In_set,New_set,Important_in_vars),
	update_important_in_vars(Head,Important_in_vars),!.

propagate_backwards(Ini_set,Calls,New_set):-
	reverse(Calls,Calls_rev),
	foldl(propagate,Calls_rev,Ini_set,New_set).

propagate(Call,Set1,Set2):-
	get_ouput_vars(Call,Out_set),
	intersection_sl(Set1,Out_set,Important_out_set),
	update_important_out_vars(Call,Important_out_set),
	important_in_vars(Call,Important_in_vars),
	from_list_sl(Important_in_vars,Important_in_vars_set),
	union_sl(Important_in_vars_set,Set1,Set2).

propagate_vars_in_undefined_CR(Head):-
	influence_map(Head,Map),!,
	important_out_vars(Head,Out_vars),
	from_list_sl(Out_vars,Out_set),
	foldl(map_influence_map(Out_set),Map,[],In_vars),
	update_important_in_vars(Head,In_vars).
propagate_vars_in_undefined_CR(Head):-
	default_influence_map(Head,Map),!,
	important_out_vars(Head,Out_vars),
	from_list_sl(Out_vars,Out_set),
	foldl(map_influence_map(Out_set),Map,[],In_vars),
	update_important_in_vars(Head,In_vars).	
	
propagate_vars_in_undefined_CR(Head):-
	get_input_vars(Head,In_vars),
	update_important_in_vars(Head,In_vars).

default_influence_map(Term,Map):-
	Term=..[_T|Vars],
	Vars=[Ai,Al,As,Bi,Bl,Bs],!,
	Map=[ (Bi,[Ai]),
	  (Bl,[Al]),
	  (Bs,[As])].
default_influence_map(Term,Map):-
	Term=..[_T|Vars],
	Vars=[Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs],!,
	Map=[(Cl,[Al,Bl]),
             (Cs,[As,Bs]),
             (Ci,[Ai,Bi])].
map_influence_map(Out_set,(Out,Ins),Set,Set1):-
	contains_sl(Out_set,Out),!,
	from_list_sl(Ins,In_set),
	union_sl(Set,In_set,Set1).
map_influence_map(_Out_set,_,Set,Set).
	
get_initial_set(Head,Cs,Ini_set):-
	important_out_vars(Head,Ini_vars),
	functor(Head,F,_),
	%is recursive
	(scc_of_function(F,_)->
	    foldl(get_condition_variables,Cs,[],Cond_vars)
	    ;
	    Cond_vars=[]
	),
	append(Cond_vars,Ini_vars,Ini_vars2),
	from_list_sl(Ini_vars2,Ini_set).
	
get_condition_variables(X=Y,List,[X|List]):-
	number(Y),!.
get_condition_variables(_,List,List).

get_ouput_vars(Call,Out_set):-
	Call=..[_F|Vars],
	append(_,[A,B,C],Vars),
	from_list_sl([A,B,C],Out_set).
get_input_vars(Call,In_set):-
	Call=..[_F|Vars],
	append(In_vars,[_,_,_],Vars),
	from_list_sl(In_vars,In_set).
		

	
update_important_in_vars(Head,Vars):-
	(important_in_vars(Head,Vars2);Vars2=[]),
	from_list_sl(Vars2,Vars2_set),
	union_sl(Vars2_set,Vars,New_vars),
	length(New_vars,N_new),
	length(Vars2,N_old),
	(N_new > N_old ->
	   retractall(important_in_vars(Head,Vars2)),
	   assert(important_in_vars(Head,New_vars)),
	   schedule_callers(Head)
	;
	  true),!.

schedule_callers(Head):-
		caller_of(Head,Caller),
		schedule(Caller),
		fail.
schedule_callers(_).  

update_important_out_vars(Head,Vars):-
	(important_out_vars(Head,Vars2);Vars2=[]),
	from_list_sl(Vars2,Vars2_set),
	union_sl(Vars2_set,Vars,New_vars),
	length(New_vars,N_new),
	length(Vars2,N_old),
	(N_new > N_old ->
	   retractall(important_out_vars(Head,Vars2)),
	   assert(important_out_vars(Head,New_vars)),
	   schedule(Head)
	;
	  true),!.	
	  
schedule(Head):-
	functor(Head,F,A),
	(scheduled(F/A)->
		true
		;
		assert(scheduled(F/A))
	).
	
influence_map('cons'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),
             [ (Cl,[Al,Bl]),
             (Cs,[As,Bs]),
             (Ci,[Ai,Bi])]).

influence_map('consp'(_Ai,Al,As,Bi,_Bl,_Bs),
             [ (Bi,[Al,As])]).       

influence_map('atom'(Ai,Al,As,Bi,Bl,Bs),Map):-
	influence_map('consp'(Ai,Al,As,Bi,Bl,Bs),Map).
influence_map('endp'(Ai,Al,As,Bi,Bl,Bs),Map):-
	influence_map('consp'(Ai,Al,As,Bi,Bl,Bs),Map).

influence_map('car'(Ai,Al,As,Bi,Bl,Bs),
	[ (Bi,[Ai]),
	  (Bl,[Al]),
	  (Bs,[As])]).
influence_map('cdr'(Ai,Al,As,Bi,Bl,Bs),Map):-
	influence_map('car'(Ai,Al,As,Bi,Bl,Bs),Map).

influence_map('or'(Ai,_Al,_As,Bi,_Bl,_Bs,Ci,_Cl,_Cs),
             [(Ci,[Ai,Bi])]).

influence_map('and'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map):-
	influence_map('or'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map).

influence_map('-'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map):-
	influence_map('or'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map).
influence_map('+'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map):-
	influence_map('or'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map).

influence_map('='(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map):-
	influence_map('or'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map).
influence_map('/='(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map):-
	influence_map('or'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map).
influence_map('>'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map):-
	influence_map('or'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map).
influence_map('<'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map):-
	influence_map('or'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map).

influence_map('binary-+'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map):-
	influence_map('or'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map).
influence_map('binary--'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map):-
	influence_map('or'(Ai,Al,As,Bi,Bl,Bs,Ci,Cl,Cs),Map).
	
influence_map('cons'(_Ai,_Al,_As,_Bi,_Bl,_Bs,Ci,Cl,Cs,Di,Dl,Ds),
             [ (Dl,[Cl]),
             (Ds,[Cs]),
             (Di,[Ci])]).

/*

eq('1+'(Ai,_Al,_As,Bi,0,0),1,[],[Bi=Ai+1]).
eq('1-'(Ai,_Al,_As,Bi,0,0),1,[],[Bi=Ai-1]).


eq('unary--'(Ai,0,0,Bi,0,0),1,[],[Bi=0-Ai]).

%make them as multually exclusive as possible
eq('integerp'(_Ai,Al,As,0,0,0),1,[],[Al>=1,As>=1]).
eq('integerp'(_Ai,Al,As,Bi,0,0),1,[],[Al=0,As=0,Bi>=0,Bi=<1]).
eq('rationalp'(_Ai,Al,As,0,0,0),1,[],[Al>=1,As>=1]).
eq('rationalp'(_Ai,Al,As,Bi,0,0),1,[],[Al=0,As=0,Bi>=0,Bi=<1]).
eq('complex-rationalp'(_Ai,Al,As,0,0,0),1,[],[Al>=1,As>=1]).
eq('complex-rationalp'(_Ai,Al,As,Bi,0,0),1,[],[Al=0,As=0,Bi>=0,Bi=<1]).
eq('acl2-numberp'(_Ai,Al,As,0,0,0),1,[],[Al>=1,As>=1]).
eq('acl2-numberp'(_Ai,Al,As,Bi,0,0),1,[],[Al=0,As=0,Bi>=0,Bi=<1]).

eq('not'(A,_,_,1,0,0),1,[],[A=0]).
eq('not'(A,_,_,0,0,0),1,[],[A=1]).

eq('zp'(A,_,_,1,0,0),1,[],[A=0]).
eq('zp'(A,_,_,0,0,0),1,[],[A>=1]).

eq('zip'(A,_,_,1,0,0),1,[],[A=0]).
eq('zip'(A,_,_,0,0,0),1,[],[A>=1]).
eq('zip'(A,_,_,0,0,0),1,[],[A+1=<0]).

eq('ash'(A,_,_,B,_,_,A,0,0),1,[],[B=0]).
eq('ash'(A,_,_,B,_,_,C,0,0),1,[],[B>=1,2*C=<A]).
eq('ash'(A,_,_,B,_,_,C,0,0),1,[],[B+1=<0,C>=2*A]).

eq('null'(Ai,0,0,0,0,0),1,[],[Ai>=1]).
eq('null'(Ai,0,0,0,0,0),1,[],[Ai+1=<0]).
eq('null'(0,0,0,1,0,0),1,[],[]).
eq('null'(_Ai,Al,As,0,0,0),1,[],[Al>=1,As>=1]).

%type check, we assume for now that it never fails
eq('the-check'(_Ai,_,_,_Bi,_,_,Ci,Cl,Cs,Ci,Cl,Cs),1,[],[]).

eq('hide'(Ai,Al,As,Ai,Al,As),1,[],[]).   % identity function
eq('coerce'(Ai,Al,As,Ai,Al,As),1,[],[]).   % for now, also treat this as id

eq('return-last'(_Ai,_,_,_Bi,_,_,Ci,Cl,Cs,Ci,Cl,Cs),1,[],[]).

% included for completeness and to avoid warnings, but not currently functional
eq('unary-/'(Ai,_Al,_As,Bi,0,0),1,[],[Ai>=1,Bi=1/Ai]).
eq('unary-/'(Ai,_Al,_As,Bi,0,0),1,[],[Ai+1=<0,Bi=1/Ai]).
eq('binary-*'(Ai,_Al,_As,Bi,_Bl,_Bs,Ci,0,0),1,[],[Ci=Ai*Bi]).

eq('eq'(Ai,0,0,Ai,0,0,1,0,0),1,[],[]).
eq('eq'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai+1=<Bi]).
eq('eq'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai>=Bi+1]).
% we would have to distinguish also the cases where A has bigger length but smaller size than B and vice-versa
% we just behave non-deterministically and improve performance
%eq('eq'(_,Al,As,_,Bl,Bs,0,0,0),1,[],[As>=Bs+1,Al>=Bl+1]).
%eq('eq'(_,Al,As,_,Bl,Bs,0,0,0),1,[],[As=<Bs-1,Al=<Bl+1]).
eq('eq'(_,Al,As,_,Bl,Bs,ZeroOne,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0,0=<ZeroOne,ZeroOne=<1]).
%eq('eq'(_,Al,As,_,Bl,Bs,1,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0]).

eq('equal'(Ai,0,0,Ai,0,0,1,0,0),1,[],[]).
eq('equal'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai+1=<Bi]).
eq('equal'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai>=Bi+1]).
% we would have to distinguish also the cases where A has bigger length but smaller size than B and vice-versa
% we just behave non-deterministically and improve performance
%eq('equal'(_,Al,As,_,Bl,Bs,0,0,0),1,[],[As>=Bs+1,Al>=Bl+1]).
%eq('equal'(_,Al,As,_,Bl,Bs,0,0,0),1,[],[As=<Bs-1,Al=<Bl+1]).
eq('equal'(_,Al,As,_,Bl,Bs,ZeroOne,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0,0=<ZeroOne,ZeroOne=<1]).
%eq('equal'(_,Al,As,_,Bl,Bs,1,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0]).

eq('eql'(Ai,0,0,Ai,0,0,1,0,0),1,[],[]).
eq('eql'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai+1=<Bi]).
eq('eql'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai>=Bi+1]).
eq('eql'(_,Al,As,_,Bl,Bs,ZeroOne,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0,0=<ZeroOne,ZeroOne=<1]).
%eq('eql'(_,Al,As,_,Bl,Bs,1,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0]).

eq('floor'(_Ai,0,0,_Bi,0,0,_Ci,0,0),1,[],[]).
eq('ceiling'(_Ai,0,0,_Bi,0,0,_Ci,0,0),1,[],[]).

eq('lognot'(_Ai,0,0,_Bi,0,0),1,[],[]).
eq('binary-logand'(_Ai,0,0,_Bi,0,0,_Ci,0,0),1,[],[]).
eq('binary-logior'(_Ai,0,0,_Bi,0,0,_Ci,0,0),1,[],[]).
eq('binary-logxor'(_Ai,0,0,_Bi,0,0,_Ci,0,0),1,[],[]).
eq('logbitp'(Ai,0,0,_Bi,0,0,_Ci,0,0),1,[],[Ai>=0]).
eq('logcount'(_Ai,0,0,_Bi,0,0),1,[],[]).
eq('xor'(_Ai,0,0,_Bi,0,0,_Ci,0,0),1,[],[]).

*/