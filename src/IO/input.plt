
:- module(input_test,[]).

:-begin_tests(input).

:-include('../search_paths.pl').
:-use_module(input).
:-use_module('../utils/crs').

	
test(process_initial_crse):-
	crse_empty(1,CRSE_empty),
	assertion(CRSE_empty=crse([],crs(range(1,1),[]))),
	
	Eq1=(eq(wh(A,B,O),0,[],[A < B,O=A]),['x'=A,'y'=B]),
	Eq2=(eq(wh(A,B,O),1,[wh(A+1,B,O)],[A >= B]),['x'=A,'y'=B]),
	IO=(input_output_vars(wh(A,B,O),[A,B],[O]),['x'=A,'y'=B]),
	
	input:process_initial_crse(Eq1,CRSE_empty,CRSE1),
	
	assertion(CRSE1=crse([],crs(range(1,2),[(wh,CR)]))),
	CRSE1=crse([],crs(range(1,2),[(wh,CR)])),
	
	assertion(CR=cr(wh/3,[(1,eq(wh(A,B,O),cost([],[],[],[],0),[],_))],_Loops,_Chains,[])),
	input:process_initial_crse(Eq2,CRSE1,CRSE2),
	
	assertion(CRSE2=crse([],crs(range(1,3),[(wh,CR2)]))),
	CRSE2=crse([],crs(range(1,3),[(wh,CR2)])),
	assertion(CR2=cr(wh/3,[
				(1,eq(wh(A,B,O),cost([],[],[],[],0),[],_)),
				(2,eq(wh(A,B,O),cost([],[],[],[],1),[wh(_,_,_)],_))
		],_,_,[])),
		
	input:process_initial_crse(IO,CRSE2,CRSE3),
	
	assertion(CRSE3=crse([],crs(range(1,3),[(wh,CR3)]))),
	CRSE3=crse([],crs(range(1,3),[(wh,CR3)])),
	assertion(CR3=cr(wh/3,[
				(1,eq(wh(A,B,O),cost([],[],[],[],0),[],_)),
				(2,eq(wh(A,B,O),cost([],[],[],[],1),[wh(_,_,_)],_))
		],_,_,[ioVars(wh(A,B,O),[A,B],[O])])).

test(process_initial_crse_redundant):-
	crse_empty(1,CRSE_empty),
	assertion(CRSE_empty=crse([],crs(range(1,1),[]))),
	
	Eq1=(eq(wh(A,B,O),1,[wh(A2,B)],[A2=A+1,A >= B]),['x'=A,'y'=B]),
	Eq2=(eq(wh(A,B,O),1,[wh(A+1,B)],[A >= B]),['x'=A,'y'=B]),
	input:process_initial_crse(Eq1,CRSE_empty,CRSE1),
	input:process_initial_crse(Eq2,CRSE1,CRSE2),
	
	%crs_get_cr(CRSE1,wh,CR),
	%crs_get_cr(CRSE2,wh,CR),
	assertion(CRSE1=CRSE2).
	
test(process_initial_crse_2cr):-
	crse_empty(1,CRSE_empty),
	assertion(CRSE_empty=crse([],crs(range(1,1),[]))),
	
	Eq1=(eq(wh(A,B,O),0,[],[A < B,O=A]),['x'=A,'y'=B]),
	Eq2=(eq(wh(A,B,O),1,[wh(A+1,B)],[A >= B]),['x'=A,'y'=B]),
	
	Eq3=(eq(wh2(A,B,O),0,[],[A < B,O=A]),['x'=A,'y'=B]),
	Eq4=(eq(wh2(A,B,O2),1,[wh(A,B,O),wh2(A+1,O,O2)],[A >= B]),['x'=A,'y'=B]),
	
	input:process_initial_crse(Eq1,CRSE_empty,CRSE1),
	input:process_initial_crse(Eq2,CRSE1,CRSE2),
	input:process_initial_crse(Eq3,CRSE2,CRSE3),
	input:process_initial_crse(Eq4,CRSE3,CRSE4),
	
	assertion(CRSE4=crse([],crs(range(1,5),[(wh,CR),(wh2,CR2)]))),
	CRSE4=crse([],crs(range(1,5),[(wh,CR),(wh2,CR2)])),
	assertion(CR=cr(wh/3,[
				(1,eq(wh(A,B,O),cost([],[],[],[],0),[],_)),
				(2,eq(wh(A,B,O),cost([],[],[],[],1),[wh(_,_)],_))
		],_,_,[])),
		
	assertion(CR2=cr(wh2/3,[
				(3,eq(wh2(A,B,O),cost([],[],[],[],0),[],_)),
				(4,eq(wh2(A,B,O),cost([],[],[],[],1),[wh(_,_,_),wh2(_,_,_)],_))
		],_,_,[])).
	
test(process_initial_crse_entries):-
	crse_empty(1,CRSE_empty),
	assertion(CRSE_empty=crse([],crs(range(1,1),[]))),
	
	Entry1=(entry(wh(A,B):[]),['x'=A,'y'=B]),
	Entry2=(entry(a(A):[A > 0]),[]),

	
	input:process_initial_crse(Entry1,CRSE_empty,CRSE1),
	input:process_initial_crse(Entry2,CRSE1,CRSE2),
	
	assertion(CRSE2=
		crse([entry(a(A),[1*A>=1]),entry(wh(A,B),[])],crs(range(1,1),[]))).
	
test(process_initial_crse_bad_eq):-
	crse_empty(1,CRSE_empty),
	Eq1=(eq(wh(A,B,O),[],[A < B,O=A]),['x'=A,'y'=B]),
	catch(input:process_initial_crse(Eq1,CRSE_empty,_CRSE1),Exception,true),
	nonvar(Exception),
	Exception=cofloco_err(failed_to_add_equation,add_equation/1,[eq=Eq1]).


test(declare_entry):-
	crse_empty(1,CRSE_empty),
	assertion(CRSE_empty=crse([],crs(range(1,1),[]))),
	
	Entry1=(entry(a(A):[A > 0]),[]),
	Entry2=(entry(wh(A,B):[]),['x'=A,'y'=B]),
	
	Eq1=(eq(wh(A,B),0,[],[A < B]),['x'=A,'y'=B]),
	
	input:process_initial_crse(Eq1,CRSE_empty,CRSE1),
	input:process_initial_crse(Entry1,CRSE1,CRSE2),
	input:process_initial_crse(Entry2,CRSE2,CRSE3),
	
	
	
	input:declare_entry(CRSE1,CRSE1_entry),
	input:declare_entry(CRSE2,CRSE2_entry),
	input:declare_entry(CRSE3,CRSE3_entry),
	
	assertion(CRSE1_entry=crse([entry(wh(_,_),[])],crs(range(1,2),[(wh,CR)]))),
	assertion(CRSE2_entry=crse([entry(a(_),_)],crs(range(1,2),[(wh,CR)]))),
	assertion(CRSE3_entry=crse([entry(a(_),_),entry(wh(_,_),[])],crs(range(1,2),[(wh,CR)]))).

%get_ground_term(Term,Bindings,Ground_term):-
	

%normalize_input_equation(EQ,EQ_Normalized) :-

%normalize_entry(entry(Call:Cs), Entry_Normalized) :-


	
:-end_tests(input).
