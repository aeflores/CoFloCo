:- module(crs_test,[]).
	
:-begin_tests(crs).

:-use_module(crs).
:-use_module(library(lambda)).

% CE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
test(ce_equal):-
	E1=eq(wh(A,B),1,[wh(A2,B)],[A >= B]),
	
	E2=eq(wh(A,B),0,[wh(A2,B)],[A >= B]),
	E3=eq(wh(A,B),1,[wh(A2,B)],[B >= A]),
	assertion(ce_equal(E1,E1)),
	copy_term(E1,E1p),
	assertion(ce_equal(E1,E1p)),
	assertion(\+ce_equal(E1,E2)),
	assertion(\+ce_equal(E1,E3)).
	
	
test(ce_more_general_than):-
	E1=eq(wh(A,B),1,[wh(A2,B)],[A >= B]),
	
	E2=eq(wh(A,B),1,[wh(A2,B)],[B >= A]),
	
	E3=eq(wh(A,B),1,[wh(A2,B)],[A >= B+1]),
	E4=eq(wh(A,B),1,[wh(A2,B)],[A >= B,B >=0]),
	
	copy_term(E1,E1p),
	assertion(ce_more_general_than(E1,E1p)),
	assertion(ce_more_general_than(E1p,E1)),
	
	assertion(\+ce_more_general_than(E1,E2)),
	assertion(ce_more_general_than(E1,E3)),
	assertion(ce_more_general_than(E1,E4)),
	
	assertion(\+ce_more_general_than(E3,E1)),
	assertion(\+ce_more_general_than(E3,E1)).



%cr
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%test(cr_creation_invalid_arity):-
%	cr_empty(wh(_,_,_),CR),
%	CR=cr(wh/3,[],[]),
%	trace,
%	catch(cr_add_eq(CR,1,eq(wh(_,_),0,[],[]),_CR2,_),_Exception,true).


cr_eqs1([
	eq(wh(A,B,O),0,[wh(A2,B)],[A+1 =< B,A2=A+1]),
	eq(wh(A,B,O),0,[wh(A2,B)],[A >= B,A2=A+1]),
	eq(wh(A,B,O),0,[wh(A2,B)],[A2 >= A+1]),
	eq(wh(A,B,O),0,[wh(A2,B)],[A2 = A+1])
	]).


cr_eqs2([
	eq_ref(wh(A,B),0,[],[wh(A2,B)],[wh(A2,B)],[A+1 =< B,A2=A+1],[]),
	eq_ref(wh(A,B),0,[],[wh(A2,B)],[wh(A2,B)],[A >= B,A2=A+1],[]),
	eq_ref(wh(A,B),0,[],[wh(A2,B)],[wh(A2,B)],[A2 >= A+1],[]),
	eq_ref(wh(A,B),0,[],[wh(A2,B)],[wh(A2,B)],[A2 = A+1],[])
	]).

test(cr_creation_subsumtion):-
	cr_empty(wh(_,_,_),CR_empty),
	CR_empty=cr(wh/3,[],_,_,[]),
	cr_eqs1(Eqs),
	foldl(\Eq_l^Pair1^Pair2^(
				Pair1=(CRS_l,Id_l),
				Pair2=(CRS2_l,Id2_l),
				cr_add_eq(CRS_l,Id_l,Eq_l,CRS2_l,Id2_l)
		),Eqs,(CR_empty,1),(CR,_N)),
	CR=cr(wh/3,[(3,eq(wh(A,B,_),0,[wh(A2,B)],Cs))],_Loops,_Chains,[]),
	Cs==[A2 >= A+1].


test(cr_creation_subsumtion2):-
	cr_empty(wh(_,_),CR_empty),
	CR_empty=cr(wh/2,[],_,_,[]),
	cr_eqs2(Eqs),
		foldl(\Eq_l^Pair1^Pair2^(
				Pair1=(CRS_l,Id_l),
				Pair2=(CRS2_l,Id2_l),
				cr_add_eq(CRS_l,Id_l,Eq_l,CRS2_l,Id2_l)
		),Eqs,(CR_empty,1),(CR,_N)),
	CR=cr(wh/2,[(3,eq_ref(wh(A,B),0,[],[wh(A2,B)],[wh(A2,B)],Cs,[]))],_Loops,_Chains,[]),
	Cs==[A2 >= A+1].
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
crs_eqs1([
	eq(wh(A,B,O),1,[crazy_call(A,B,_C)],[A < B,O=A]),
	eq(wh(A,B,O),2,[wh(A+1,B)],[A >= B]),
	
	eq(wh2(A,B,O),3,[],[A < B,O=A]),
	eq(wh2(A,B,O2),4,[wh(A,B,O),wh2(A+1,O,O2)],[A >= B])
	]).

crs_create_example1(CRSE):-
	crse_empty(1,CRSE_empty),
	assertion(CRSE_empty=crse([],crs(range(1,1),[]))),
	
	CRSE_empty=crse(Entries,CRS_empty),
	crs_eqs1(Eqs),
	foldl(\Eq_l^CRS_l^CRS2_l^crs_add_eq(CRS_l,Eq_l,CRS2_l),Eqs,CRS_empty,CRS),
	CRSE=crse(Entries,CRS).
	
test(crs_creation):-
	crs_create_example1(CRSE),
	CRSE=crse(_,CRS),
	assertion(CRS=crs(range(1,5),[(wh,CR),(wh2,CR2)])),
	CRS=crs(range(1,5),[(wh,CR),(wh2,CR2)]),
	
	assertion(CR=cr(wh/3,[
				(1,eq(wh(A,B,O),1,[crazy_call(A,B,_C)],_)),
				(2,eq(wh(A,B,O),2,[wh(_,_)],_))
		],loops(_,_),chains(_,_,_),[])),

	assertion(CR2=cr(wh2/3,[
				(3,eq(wh2(A,B,O),3,[],_)),
				(4,eq(wh2(A,B,O),4,[wh(_,_,_),wh2(_,_,_)],_))
		],loops(_,_),chains(_,_,_),[])).

test(remove_undefined_calls):-
	crs_create_example1(CRSE),
	crs:crse_remove_undefined_calls(CRSE,crse(_Entries,CRS)),
	assertion(CRS=crs(range(1,5),[(wh,CR),(wh2,CR2)])),
	CRS=crs(range(1,5),[(wh,CR),(wh2,CR2)]),
	assertion(CR=cr(wh/3,[
				(1,eq(wh(A,B,O),1,[],_)),
				(2,eq(wh(A,B,O),2,[],_))
		],loops(_,_),chains(_,_,_),[])),
		
	assertion(CR2=cr(wh2/3,[
				(3,eq(wh2(A,B,O),3,[],_)),
				(4,eq(wh2(A,B,O),4,[wh(_,_,_),wh2(_,_,_)],_))
		],loops(_,_),chains(_,_,_),[])).
		
test(save_io_vars):-
	crse_empty(1,CRSE_empty),
	CRSE_empty=crse([],CRS_empty),
	crs_save_IOvars(CRS_empty,ioVars(wh(A,B,C),[A,B],[C]),CRS),
	assertion(crs_get_names(CRS,[wh/3])),
	findall(Eq,
			 crs_get_ce(CRS,Eq),
			 []).

	
test(access_CEs):-
		crs_create_example1(CRSE),
		CRSE=crse(_,CRS),
		crs_get_ce_by_id(CRS,1,eq(wh(_,_,_),1,_,_)),
		crs_get_ce_by_id(CRS,2,eq(wh(_,_,_),2,_,_)),
		crs_get_ce_by_id(CRS,3,eq(wh2(_,_,_),3,_,_)),
		crs_get_ce_by_id(CRS,4,eq(wh2(_,_,_),4,_,_)),
		findall(Eq,crs_get_ce_by_name(CRS,wh,Eq),Eqs1),
		assertion(Eqs1=[eq(wh(_,_,_),1,_,_),eq(wh(_,_,_),2,_,_)]),
		
		
		findall(Eq,crs_get_ce_by_name_fresh(CRS,wh,Eq),Eqs2),
		assertion(Eqs2=[eq(wh(_,_,_),1,_,_),eq(wh(_,_,_),2,_,_)]),
		
		findall(Eq,crs_get_ce(CRS,Eq),Eqs3),
		assertion(Eqs3=[eq(wh(_,_,_),1,_,_),eq(wh(_,_,_),2,_,_),eq(wh2(_,_,_),3,_,_),eq(wh2(_,_,_),4,_,_)]),
		assertion(crs_get_names(CRS,[wh/3,wh2/3])),
		crs_get_cr(CRS,wh,CR),
		assertion(cr_head(CR,wh(_,_,_))),
		assertion(cr_get_ids(CR,[1,2])),
		assertion(crs_range(CRS,range(1,5))).

double_cost(eq(Head,N,Calls,Cs),eq(Head,N2,Calls,Cs)):-
	N2 is 2*N.
	
add_call(Call,eq(Head,N,Calls,Cs),eq(Head,N,[Call|Calls],Cs)).

test(apply_and_check_all_ce):-
	crs_create_example1(CRSE),
		CRSE=crse(_,CRS),
	crs_apply_all_ce(plunit_crs:double_cost,CRS,CRS2),
	
	crs_get_ce_by_id(CRS2,1,eq(wh(_,_,_),2,_,_)),
	crs_get_ce_by_id(CRS2,2,eq(wh(_,_,_),4,_,_)),
	crs_get_ce_by_id(CRS2,3,eq(wh2(_,_,_),6,_,_)),
	crs_get_ce_by_id(CRS2,4,eq(wh2(_,_,_),8,_,_)),
	
	crs_get_cr(CRS2,wh,CR),
	crs_get_cr(CRS2,wh2,CR2),
	assertion(\+cr_is_cr_called_multiply(CR,wh2/3)),
	assertion(\+cr_is_cr_called_multiply(CR2,wh2/3)),
	
	crs_apply_all_ce(plunit_crs:add_call(wh2(_,_,_)),CRS,CRS3),
	crs_get_cr(CRS3,wh,CR3),
	crs_get_cr(CRS3,wh2,CR4),
	
	assertion(\+cr_is_cr_called_multiply(CR3,wh2/3)),
	assertion(cr_is_cr_called_multiply(CR4,wh2/3)).
	
		
crs_for_graph([
	eq(a(A),1,[a(A)],[]),
	eq(a(A),2,[c(A),d(A)],[]),
	
	eq(c(A),3,[e(A),e(A)],[]),
	
	eq(d(A),4,[f(A)],[]),
	eq(d(A),5,[g(A)],[]),
	eq(d(A),6,[h(A)],[]),
	
	eq(e(A),7,[a(A)],[]),
	eq(f(A),8,[],[]),
	eq(g(A),9,[],[]),
	eq(h(A),10,[],[])
	]).	

crs_create_example_for_graph(CRSE):-
	crse_empty(1,CRSE_empty),
	assertion(CRSE_empty=crse([],crs(range(1,1),[]))),
	
	CRSE_empty=crse([],CRS_empty),
	crs_for_graph(Eqs),
	foldl(\Eq_l^CRS_l^CRS2_l^crs_add_eq(CRS_l,Eq_l,CRS2_l),Eqs,CRS_empty,CRS),
	CRSE=crse([entry(a(_),[]),entry(b(B),[B=1]),entry(d(_),[])],CRS).	

test(create_graph):-
	crs_create_example_for_graph(CRSE),
	CRSE=crse(_,CRS),
	crs_get_graph(CRS,call_graph(Edges)),
	sort(Edges,Edges_set),
	Edges_set=[a/1-a/1,  a/1-c/1,  a/1-d/1,
		       c/1-e/1,  
		       d/1-f/1,  d/1-g/1,  d/1-h/1,
		       e/1-a/1].
	
	
test(merge_cr):-
	crs_create_example_for_graph(CRSE),
	crse_merge_crs(ad,[a,d],CRSE,CRSE1),
	CRSE1=crse(Entries,CRS),
	assertion(Entries=[entry(ad(_),[]),entry(b(B),[B=1]),entry(ad(_),[])]),
	maplist(entry_name,Entries,[ad/1,b/1,ad/1]),
	
	findall(Eq,crs_get_ce_by_name(CRS,ad,Eq),Eqs_ad),
	assertion(Eqs_ad=[
					eq(ad(A),1,[ad(A)],[]),
					eq(ad(A),2,[c(A),ad(A)],[]),
					eq(ad(A),4,[f(A)],[]),
					eq(ad(A),5,[g(A)],[]),
					eq(ad(A),6,[h(A)],[])
					]),
					
	findall(Eq,crs_get_ce_by_name(CRS,c,Eq),Eqs_c),
	assertion(Eqs_c=[eq(c(A),3,[e(A),e(A)],[])]),
	
	findall(Eq,crs_get_ce_by_name(CRS,e,Eq),Eqs_e),	
	assertion(Eqs_e=[eq(e(A),7,[ad(A)],[])]).
	

test(merge_cr2):-
	crs_create_example_for_graph(CRSE),
	CRSE=crse(Entries,CRS),
	crs_save_IOvars(CRS,ioVars(a(A),[],[A]),CRS1),
	crs_save_IOvars(CRS1,ioVars(d(A),[A],[]),CRS2),
	CRSE1=crse(Entries,CRS2),
	crse_merge_crs(ad,[a,d],CRSE1,CRSE2),
	CRSE2=crse(_,CRS_new),
	
	findall(Eq,crs_get_ce_by_name(CRS_new,ad,Eq),Eqs_ad),
	numbervars(Eqs_ad,0,_),
	assertion(Eqs_ad=[
					eq(ad(_,A),1,[ad(_,A)],[]),
					eq(ad(_,B),2,[c(B),ad(B,_)],[]),
					eq(ad(C,_),4,[f(C)],[]),
					eq(ad(D,_),5,[g(D)],[]),
					eq(ad(E,_),6,[h(E)],[])
					]),
	crs_IOvars(CRS_new,ad,ioVars(ad(_,_),[_],[_])).
  

crs_for_unfold([
	eq(a(A),cost([],[],[],[],1),[a(A)],[]),
	eq(a(A),cost([],[],[],[],1),[c(A),d(A)],[ A>=1 ]),
	
	eq(c(A),cost([],[],[],[],1),[e(A),e(A)],[]),
	
	eq(d(A),cost([],[],[],[],1),[f(A)],[]),
	eq(d(A),cost([],[],[],[],1),[g(A)],[]),
	eq(d(A),cost([],[],[],[],1),[h(A)],[]),
	
	eq(e(A),cost([],[],[],[],1),[a(A)],[]),
	eq(e(A),cost([],[],[],[],2),[a(A)],[]),
	
	eq(f(A),cost([],[],[],[],1),[],[A=0]),
	eq(g(A),cost([],[],[],[],1),[],[]),
	eq(h(A),cost([],[],[],[],1),[],[])
	]).	
	
crs_create_example_for_unfold(CRSE):-
	crse_empty(1,CRSE_empty),
	CRSE_empty=crse([],CRS_empty),
	crs_for_unfold(Eqs),
	foldl(\Eq_l^CRS_l^CRS2_l^crs_add_eq(CRS_l,Eq_l,CRS2_l),Eqs,CRS_empty,CRS),
	CRSE=crse([],CRS).	
	
test(unfold):-
	crs_create_example_for_unfold(CRSE),
	CRSE=crse(_,CRS),
	crs_unfold_and_remove(CRS,a,d,CRS2),
	%should generate a total of 4 eqs in a
	crs_get_cr(CRS2,a,CR_a1),
	cr_get_ceList(CR_a1,Eqs_a1),
	assertion(Eqs_a1=[
		eq(a(A),cost([],[],[],[],1),[a(A)],[]),
		eq(a(A),cost([],[],[],[],2),[c(A),f(A)],[ 1*A>=1 ]),
		eq(a(A),cost([],[],[],[],2),[c(A),g(A)],[ 1*A>=1 ]),
		eq(a(A),cost([],[],[],[],2),[c(A),h(A)],[ 1*A>=1 ])
		]),
	%should discard one eq leaving 3 in a		
	crs_unfold_and_remove(CRS2,a,f,CRS3),
	crs_get_cr(CRS3,a,CR_a2),
	cr_get_ceList(CR_a2,Eqs_a2),
	assertion(Eqs_a2=[
		eq(a(A),cost([],[],[],[],1),[a(A)],[]),
		eq(a(A),cost([],[],[],[],2),[c(A),g(A)],[ 1*A>=1 ]),
		eq(a(A),cost([],[],[],[],2),[c(A),h(A)],[ 1*A>=1 ])
		]),
	%should maintain the same number of eqs	
	crs_unfold_and_remove(CRS3,a,g,CRS4),
	crs_get_cr(CRS4,a,CR_a3),
	cr_get_ceList(CR_a3,Eqs_a3),
	assertion(Eqs_a3=[
		eq(a(A),cost([],[],[],[],1),[a(A)],[]),
		eq(a(A),cost([],[],[],[],3),[c(A)],[ 1*A>=1 ]),
		eq(a(A),cost([],[],[],[],2),[c(A),h(A)],[ 1*A>=1 ])
		]),
	%the new equation should be redundant with the previous one		
	crs_unfold_and_remove(CRS4,a,h,CRS5),
	crs_get_cr(CRS5,a,CR_a4),
	cr_get_ceList(CR_a4,Eqs_a4),
	assertion(Eqs_a4=[
		eq(a(A),cost([],[],[],[],1),[a(A)],[]),
		eq(a(A),cost([],[],[],[],3),[c(A)],[ 1*A>=1 ])
		]),
	crs_unfold_and_remove(CRS5,c,e,CRS6),
	crs_get_cr(CRS6,c,CR_c1),
	cr_get_ceList(CR_c1,Eqs_c1),
	%should generate 4 equations of c but two of them are equivalent (same cost)
	% so in total we have 3
	assertion(Eqs_c1=[
		eq(c(A),cost([],[],[],[],3),[a(A),a(A)],[]),
		eq(c(A),cost([],[],[],[],4),[a(A),a(A)],[]),
		eq(c(A),cost([],[],[],[],5),[a(A),a(A)],[])
		]),
	%completely partially evaluated: 4 equations of a	
	crs_unfold_and_remove(CRS6,a,c,CRS7),
	crs_get_cr(CRS7,a,CR_a5),
	cr_get_ceList(CR_a5,Eqs_a5),	
	assertion(Eqs_a5=	[
				eq(a(A),cost([],[],[],[],1),[a(A)],[]),
				eq(a(A),cost([],[],[],[],6),[a(A),a(A)],[ 1*A>=1]),
				eq(a(A),cost([],[],[],[],7),[a(A),a(A)],[ 1*A>=1]),
				eq(a(A),cost([],[],[],[],8),[a(A),a(A)],[ 1*A>=1])
				]),
	assertion(crs_get_names(CRS7,[a/1])).

	
	
	
:-end_tests(crs).
