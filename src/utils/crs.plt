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
	eq(wh(A,B,O),0,[crazy_call(A,B,_C)],[A < B,O=A]),
	eq(wh(A,B,O),1,[wh(A+1,B)],[A >= B]),
	
	eq(wh2(A,B,O),0,[],[A < B,O=A]),
	eq(wh2(A,B,O2),1,[wh(A,B,O),wh2(A+1,O,O2)],[A >= B])
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
				(1,eq(wh(A,B,O),0,[crazy_call(A,B,_C)],_)),
				(2,eq(wh(A,B,O),1,[wh(_,_)],_))
		],loops(_,_),chains(_,_,_),[])),

	assertion(CR2=cr(wh2/3,[
				(3,eq(wh2(A,B,O),0,[],_)),
				(4,eq(wh2(A,B,O),1,[wh(_,_,_),wh2(_,_,_)],_))
		],loops(_,_),chains(_,_,_),[])).

test(remove_undefined_calls):-
	crs_create_example1(CRSE),
	crs:crse_remove_undefined_calls(CRSE,crse(_Entries,CRS)),
	assertion(CRS=crs(range(1,5),[(wh,CR),(wh2,CR2)])),
	CRS=crs(range(1,5),[(wh,CR),(wh2,CR2)]),
	assertion(CR=cr(wh/3,[
				(1,eq(wh(A,B,O),0,[],_)),
				(2,eq(wh(A,B,O),1,[],_))
		],loops(_,_),chains(_,_,_),[])),
		
	assertion(CR2=cr(wh2/3,[
				(3,eq(wh2(A,B,O),0,[],_)),
				(4,eq(wh2(A,B,O),1,[wh(_,_,_),wh2(_,_,_)],_))
		],loops(_,_),chains(_,_,_),[])).
		
	

		
:-end_tests(crs).
