:- module(crs,[
		ce_equal/2,
		ce_more_general_than/2,
		ce_calls_accum/3,
			
		cr_empty/2,
		cr_get_ce_by_id/3,
		cr_head/2,
		cr_get_ids/2,
		cr_add_eq/5,
		cr_get_ce/2,
		cr_IOvars/2,
		cr_get_ceList/2,
		cr_apply_all_ce/3,
		cr_set_loops/3,
		cr_get_loops/2,
		cr_set_chains/3,
		cr_get_chains/2,
		cr_is_cr_called_multiply/2,
		
		crs_empty/2,
		crs_range/2,
		crs_add_eq/3,
		crs_get_ce_by_id/3,
		crs_get_ce_by_name/3,
		crs_get_ce/2,
		crs_get_cr/3,
		crs_save_IOvars/3,
		crs_IOvars/3,
		crs_get_graph/2,
		crs_apply_all_ce/3,
		crs_get_names/2,
		crs_get_ce_by_name_fresh/3,	
		crs_unfold_in_cr/4,
		crs_unfold_and_remove/4,
		crs_remove_cr/3,
	

		
		crse_empty/2,
		crse_remove_undefined_calls/2,
		crse_merge_crs/4,
		
		entry_name/2
	]).
	
:-use_module('../IO/output',[print_warning/2]).
:-use_module(cofloco_utils,[zip_with_op3/5]).
:-use_module(cost_structures,[cstr_join/3]).
:-use_module(stdlib(numeric_abstract_domains),[nad_entails/3,nad_glb/3]).
:-use_module(polyhedra_optimizations,[nad_consistent_constraints_group/2,nad_project_group/3]).
:-use_module(stdlib(list_map)).
:-use_module(stdlib(set_list)).
:-use_module(library(lambda)).

%eq(Head,Cost,Calls,Cs)
%eq_ref(Head,Cost,NR_calls,R_calls,Calls,Cs,Info)
%these predicates are defined for both kinds of equations


ce_head(eq(Head,_,_,_),Head).
ce_head(eq_ref(Head,_,_,_,_,_,_),Head).
	
ce_equal(eq(Head,Cost_str,Calls,Cs),eq(Head,Cost_str2,Calls,Cs2)):-
         Cs==Cs2,
         Cost_str==Cost_str2.
         
ce_equal(eq_ref(Head,Cost_str,NR_calls,R_calls,Calls,Cs,Info),eq_ref(Head,Cost_str2,NR_calls,R_calls,Calls,Cs2,Info)):-
         Cs==Cs2,
         Cost_str==Cost_str2.

ce_more_general_than(eq(Head,Cost_str,Calls,Cs),eq(Head,Cost_str2,Calls,Cs2)):-
	Cost_str==Cost_str2,
	term_variables((Cs,Cs2),All_vars),
	nad_entails(All_vars,Cs2,Cs).

ce_more_general_than(eq_ref(Head,Cost_str,NR_calls,R_calls,Calls,Cs,Info),eq_ref(Head,Cost_str2,NR_calls,R_calls,Calls,Cs2,Info)):-
	Cost_str==Cost_str2,
	term_variables((Cs,Cs2),All_vars),
	nad_entails(All_vars,Cs2,Cs).


ce_calls(eq(_,_,Calls,_),Calls).
ce_calls(eq_ref(_,_,_,_,Calls,_,_),Calls).

ce_calls_cr(Eq,Head):-
	ce_calls(Eq,Calls),
	member(Head,Calls),!.
	
ce_get_edges_accum(F1/A1,Eq,Accum_set,Edges):-
	ce_calls(Eq,Calls),
	findall(F1/A1-F2/A2,
	        (member(Call, Calls),functor(Call,F2,A2)),
	       	Edges_aux),
	from_list_sl(Edges_aux,Edges_set), 
	union_sl(Edges_set,Accum_set,Edges). 
	

ce_calls_accum(Eq,Accum_set,Call_names_total):-
	ce_calls(Eq,Calls),
	findall(F2/A2,
	        (member(Call, Calls),functor(Call,F2,A2)),
	       	Call_names),
	from_list_sl(Call_names,Call_names_set), 
	union_sl(Call_names_set,Accum_set,Call_names_total). 

ce_is_cr_called_multiply(F/A,Eq):-
	ce_calls(Eq,Calls),
	functor(Head,F,A),
	select(Head,Calls,Calls1),
	select(Head,Calls1,_),!.	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%these predicates are only defined for the initial equations

ce_remove_undefined_calls(Defined_CRs,eq(Head,Cost,Calls,Cs),eq(Head,Cost,Calls2,Cs)):-
	remove_undefined_calls_1(Calls,Head,Defined_CRs,Calls2).
	
remove_undefined_calls_1([],_Head,_Defined,[]).
remove_undefined_calls_1([C|Calls],Head,Defined,[C|Calls1]) :-
	functor(C,Name,Arity),
	member(Name/Arity,Defined),!,
	remove_undefined_calls_1(Calls,Head,Defined,Calls1).
remove_undefined_calls_1([C|Calls],Head,Defined,Calls1) :-
	functor(C,Cname,C_arity),functor(Head,Headname,Head_arity),
	print_warning('Warning: Ignored call to ~p in equation ~p ~n',[Cname/C_arity,Headname/Head_arity]),
	remove_undefined_calls_1(Calls,Head,Defined,Calls1).

  
ce_substitute_head(New_name,CR_to_merge,
					eq(Head,Cost,Calls,Cs),
					eq(Head_new,Cost,Calls,Cs)
					):-
	get_new_head(Head,New_name,CR_to_merge,Head_new).

ce_substitute_calls(New_name,CR_to_merge,
					eq(Head,Cost,Calls,Cs),
					eq(Head,Cost,Calls2,Cs)
					):-
	maplist(substitute_call(New_name,CR_to_merge),Calls,Calls2).


substitute_call(New_name,CR_to_merge,Call,Call_new):-
	functor(Call,Old_name,_),
	member(Old_name/AI/AO,CR_to_merge),!,
	get_new_head(Call,New_name,Old_name/AI/AO,Call_new).
substitute_call(_,_,Call,Call).
        
        
 get_new_head(Head,New_name/New_AI/New_AO,Old_name/Old_AI/Old_AO,Head_new):-
	Extra_IA is New_AI-Old_AI,
	Extra_OA is New_AO-Old_AO,
	head_get_io_vars(Head,Old_name/Old_AI/Old_AO,Ivars,Ovars),
	length(Extra_Ivars,Extra_IA),
	length(Extra_Ovars,Extra_OA),
	append(Ivars,Extra_Ivars,New_Ivars),
	append(Ovars,Extra_Ovars,New_Ovars),
	append(New_Ivars,New_Ovars,New_vars),
	Head_new=..[New_name|New_vars],!.

head_get_io_vars(Head,Name/AI/AO,Ivars,Ovars):-
	length(Ivars,AI),
	length(Ovars,AO),
	append(Ivars,Ovars,Vars),
	Head=..[Name|Vars].       
        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cr_empty(Head,cr(Name/Arity,Empty_map,_Empty_loops,_Empty_chains,[])):-
	functor(Head,Name,Arity),
	empty_lm(Empty_map).



cr_add_eq_pair((Id,Eq),cr(Name/Arity,Map,Loops,Chains,Properties),cr(Name/Arity,Map2,Loops,Chains,Properties)):-
	insert_lm(Map,Id,Eq,Map2).
	
cr_add_eq(cr(Name/Arity,Map,Loops,Chains,Properties),Id,Eq,cr(Name/Arity,Map2,Loops,Chains,Properties),Id_next):-
	ce_head(Eq,Head),
	assertion(functor(Head,Name,Arity)),
	(cr_ce_is_subsumed(cr(Name/Arity,Map,Loops,Chains,Properties),Eq)->
		Map2=Map,
		Id_next=Id
	;
	 	exclude(\Pair^(
	 					Pair=(_,Eq_l),
	 					ce_more_general_than(Eq,Eq_l)
	 		),Map,Map_aux),
		insert_lm(Map_aux,Id,Eq,Map2),
		Id_next is Id+1	
	).

	
cr_ce_is_subsumed(cr(_,Map,_Loops,_Chains,_Properties),Eq):-
	values_lm(Map,Eqs),
	member(Eq1,Eqs),
	ce_equal(Eq,Eq1),!.

cr_ce_is_subsumed(cr(_,Map,_Loops,_Chains,_Properties),Eq):-
	values_lm(Map,Eqs),
	member(Eq1,Eqs),
	ce_more_general_than(Eq1,Eq),!.	
	
cr_get_ce_by_id(cr(_,Map,_Loops,_Chains,_),Id,Eq):-
	lookup_lm(Map,Id,Eq).
		
		
cr_save_IOvars(cr(Name/Arity,Map,Loops,Chains,Properties),ioVars(Head,Ivars,Ovars),cr(Name/Arity,Map,Loops,Chains,Properties3)):-
	assertion(functor(Head,Name,Arity)),
	(select(ioVars(Head,Ivars2,Ovars2),Properties,Properties2)->
		((Ivars2==Ivars,Ovars==Ovars2)->
			true
			;
			copy_term((input_output_vars(Head,Ivars,Ovars),input_output_vars(Head,Ivars2,Ovars2)),
				      (input_output_vars(Head_gr,Ivars_gr,Ovars_gr),input_output_vars(Head_gr,Ivars2_gr,Ovars2_gr))),
			numbervars(Head_gr,0,_),
  			print_warning('Warning: Incoherent annotation ~p and ~p ~n',
  				[input_output_vars(Head_gr,Ivars_gr,Ovars_gr),input_output_vars(Head_gr,Ivars2_gr,Ovars2_gr)])
  		)
  		;
  		Properties2=Properties
  	),
  	Properties3=[ioVars(Head,Ivars,Ovars)|Properties2].

cr_IOvars(cr(Name/Arity,_Map,_Loops,_Chains,Properties),IOvars_fresh):-
	(member(ioVars(Head,Ivars,Ovars),Properties)->
		true
		;
		%default value is that all variables are input variables
		functor(Head,Name,Arity),
		Head=..[Name|Ivars],
		Ovars=[]
	),
	copy_term(ioVars(Head,Ivars,Ovars),IOvars_fresh).
	
cr_IOvars_arities(cr(_/Arity,_Map,_Loops,_Chains,Properties),Iarity,Oarity):-
	(member(ioVars(_,Ivars,Ovars),Properties)->
		length(Ivars,Iarity),
		length(Ovars,Oarity)
		;
		%default value is that all variables are input variables
		Iarity=Arity,
		Oarity=0
	).
	
cr_head(cr(Name/Arity,_,_Loops,_Chains,_),Head):-
	functor(Head,Name,Arity).
cr_nameArity(cr(Name/Arity,_,_Loops,_Chains,_),Name/Arity).	
	

cr_get_edges_accum(cr(F1/A1,CEs_map,_Loops,_Chains,_),Accum,Edges):-
	values_lm(CEs_map,CEs),
	foldl(ce_get_edges_accum(F1/A1),CEs,Accum,Edges).
	
cr_get_ids(cr(_,Map,_Loops,_Chains,_),Ids):-
	keys_lm(Map,Ids).
	
cr_get_ceList(cr(_,Map,_Loops,_Chains,_),CE_list):-
	values_lm(Map,CE_list).
	
cr_get_ceList_with_id(cr(_,Map,_Loops,_Chains,_),Map).

cr_get_ce(cr(_,Map,_Loops,_Chains,_),CE):-
	values_lm(Map,CE_list),
	member(CE,CE_list).
	
cr_apply_all_ce(Pred,cr(NameArity,EqMap,Loops,Chains,Properties),cr(NameArity,EqMap2,Loops,Chains,Properties)):-
	map_values_lm(Pred,EqMap,EqMap2).

%cr_check_all_ce(Pred,cr(_NameArity,EqMap,_Loops,_Chains,_Properties)):-%
%	check_values_lm(Pred,EqMap).

cr_check_some_ce(Pred,cr(_NameArity,EqMap,_Loops,_Chains,_Properties)):-
	member((_,Eq),EqMap),
	call(Pred,Eq),!.


cr_is_cr_called_multiply(CR,Node):-
	cr_check_some_ce(ce_is_cr_called_multiply(Node),CR).


cr_unfold_in_cr(CR,CR_called,Counter,CR_final,Counter_final):-
	cr_head(CR_called,Called_head),
	cr_check_some_ce(\CE_l^ce_calls_cr(CE_l,Called_head),CR),!,
	cr_head(CR,Head),
	cr_empty(Head,CR_empty),
	cr_get_ceList(CR,CE_list),
	cr_get_ceList(CR_called,CE_list_called),
	foldl(add_combined_eq(CE_list),CE_list_called,(CR_empty,Counter),(CR_new,Counter_new)),
	cr_unfold_in_cr(CR_new,CR_called,Counter_new,CR_final,Counter_final).

cr_unfold_in_cr(CR,_CR_called,Counter,CR,Counter).



add_combined_eq(CE_list,CE_called,(CR_accum,C),(CR_accum2,C2)):-
	foldl(add_combined_eq_1(CE_called),CE_list,(CR_accum,C),(CR_accum2,C2)).

add_combined_eq_1(Callee,eq(Head_caller,Exp1,Calls1,Size1),(CR_accum,C),(CR_accum2,C2)):-
	copy_term(Callee,eq(Head_callee,Exp0,Calls0,Size0)),
	substitute_call_2(Calls1,Head_callee,Calls0,Calls1_sub),!,
	cstr_join(Exp1,Exp0,CombE),
 	nad_glb(Size1,Size0,CombS),
 	term_variables(eq(Head_caller,CombE,Calls1_sub,CombS),Total_vars),
 	term_variables(eq(Head_caller,CombE,Calls1_sub),Rest_vars),
 	(nad_consistent_constraints_group(Total_vars,CombS)->
 		nad_project_group(Rest_vars,CombS,CombSp),
 		cr_add_eq(CR_accum,C,eq(Head_caller,CombE,Calls1_sub,CombSp),CR_accum2,C2)	
 		;
 		CR_accum2=CR_accum,
 		C2=C
 	).
add_combined_eq_1(_Callee,eq(Head_caller,Exp1,Calls1,Size1),(CR_accum,C),(CR_accum2,C2)):-
	cr_add_eq(CR_accum,C,eq(Head_caller,Exp1,Calls1,Size1),CR_accum2,C2).
		


substitute_call_2([Head_callee|Calls1],Head_callee,Calls0,Calls1_sub):-
	append(Calls0,Calls1,Calls1_sub).
substitute_call_2([Other|Calls1],Head_callee,Calls0,[Other|Calls1_sub]):-
	substitute_call_2(Calls1,Head_callee,Calls0,Calls1_sub).
	
	
	
cr_set_loops(cr(NameArity,EqMap,_Loops,Chains,Properties),Loops_new,cr(NameArity,EqMap,Loops_new,Chains,Properties)).
cr_get_loops(cr(_NameArity,_EqMap,Loops,_Chains,_Properties),Loops).

cr_set_chains(cr(NameArity,EqMap,Loops,_Chains,Properties),Chains_new,cr(NameArity,EqMap,Loops,Chains_new,Properties)).
cr_get_chains(cr(_NameArity,_EqMap,_Loops,Chains,_Properties),Chains).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
crs_empty(Initial,crs(range(Initial,Initial),Empty_map)):-
	empty_lm(Empty_map).

crs_range(crs(Range,_CRs_map),Range).

crs_add_eq(crs(range(I,F),CRs_map),Eq,crs(range(I,F2),CRs_map2)):-
	ce_head(Eq,Head),
	functor(Head,Name,_),
	(lookup_lm(CRs_map,Name,CR)->
		cr_add_eq(CR,F,Eq,CR2,F2)
		;
		cr_empty(Head,Empty_CR),
		cr_add_eq(Empty_CR,F,Eq,CR2,F2)
		),
	insert_lm(CRs_map,Name,CR2,CRs_map2).




crs_get_ce_by_id(crs(range(I,F),CRs_map),Id,Eq):-
	assertion(((Id<F),(Id>=I))),
	values_lm(CRs_map,CR_list),
	find_ce_by_id(CR_list,Id,Eq).
	

find_ce_by_id([CR|CRs],Id,Eq):-
	(cr_get_ce_by_id(CR,Id,Eq)->
		true
		;
		find_ce_by_id(CRs,Id,Eq)
		).


crs_save_IOvars(crs(Range,CRs_map),ioVars(Head,IVars,OVars),crs(Range,CRs_map2)):-
	functor(Head,Name,_A),
	(lookup_lm(CRs_map,Name,CR)->
		cr_save_IOvars(CR,ioVars(Head,IVars,OVars),CR2)
		;
		cr_empty(Head,Empty_CR),
		cr_save_IOvars(Empty_CR,ioVars(Head,IVars,OVars),CR2)
		),
	insert_lm(CRs_map,Name,CR2,CRs_map2).

	
crs_get_cr(crs(_,CRs_map),Name,CR):-
	lookup_lm(CRs_map,Name,CR).
	
crs_remove_cr(crs(Range,CRs_map),Name,crs(Range,CRs_map2)):-
	delete_lm(CRs_map,Name,CRs_map2).

crs_update_cr(crs(Range,CRs_map),Name,New_CR,crs(Range,CRs_map2)):-
	update_lm(CRs_map,Name,_,New_CR,CRs_map2).
	
	
crs_IOvars(crs(_,CRs_map),Name,IOvars):-
	lookup_lm(CRs_map,Name,CR),
	cr_IOvars(CR,IOvars).
	
crs_IOvars_arities(crs(_,CRs_map),Name,Name/Iarity/Oarity):-
	lookup_lm(CRs_map,Name,CR),
	cr_IOvars_arities(CR,Iarity,Oarity).

crs_apply_all_ce(Pred,crs(Range,CRs_map),crs(Range,CRs_map2)):-
	map_values_lm(cr_apply_all_ce(Pred),CRs_map,CRs_map2).

	
% remove the calls to equations that are not defined (and show a warning)
crs_remove_undefined_calls(crs(Range,CRs_map),CRS2):-
	values_lm(CRs_map,CRs),
	maplist(cr_nameArity,CRs,Defined_CRs),
	crs_apply_all_ce(ce_remove_undefined_calls(Defined_CRs),crs(Range,CRs_map),CRS2).

	

crs_get_names(crs(_,CRs_map),Names):-
	values_lm(CRs_map,CRs),
	maplist(cr_nameArity,CRs,Names).
	
crs_get_graph(crs(_,CRs_map),call_graph(Graph)):-
	values_lm(CRs_map,CRs),
	foldl(cr_get_edges_accum,CRs,[],Graph).


crs_get_ce_by_name(crs(_,CRs_map),Name,CE):-
	lookup_lm(CRs_map,Name,CR),
	cr_get_ce(CR,CE).
	
crs_get_ce(crs(_,CRs_map),CE):-
	member((_,CR),CRs_map),
	cr_get_ce(CR,CE).
	
crs_get_ce_by_name_fresh(crs(_,CRs_map),Name,CE_fresh):-
	lookup_lm(CRs_map,Name,CR),
	cr_get_ce(CR,CE),
	copy_term(CE,CE_fresh).


crs_merge_cr_head(Cr_to_merge,New_name/AI/AO,CRS,CRS3):-
	Arity is AI+AO,
	functor(New_Head,New_name,Arity),
	cr_empty(New_Head,CR_new_empty),
	crs_merge_cr_head_1(Cr_to_merge,New_name/AI/AO,CRS,CR_new_empty,CRS2,CR_new),
	CRS2=crs(Range,CRs_map),
	insert_lm(CRs_map,New_name,CR_new,CRs_map2),
	CRS3=crs(Range,CRs_map2).
	
crs_merge_cr_head_1([],_New_name,CRS,CR_new,CRS,CR_new).
crs_merge_cr_head_1([Old_name/AI/AO|To_merge],New_name,crs(Range,CRs_map),CR_accum,CRS,CR_new):-
	lookup_lm(CRs_map,Old_name,CR),
	delete_lm(CRs_map,Old_name,CRs_map1),
	cr_get_ceList_with_id(CR,Map),
	map_values_lm(ce_substitute_head(New_name,Old_name/AI/AO),Map,Map2),
	foldl(cr_add_eq_pair,Map2,CR_accum,CR_accum2),
	crs_merge_cr_head_1(To_merge,New_name,crs(Range,CRs_map1),CR_accum2,CRS,CR_new).
	

crs_unfold_in_cr(crs(range(Min,Max),CRs_map),CR_name,CR_called,CRS):-
	crs_get_cr(crs(range(Min,Max),CRs_map),CR_name,CR),
	cr_unfold_in_cr(CR,CR_called,Max,CR2,New_max),
	crs_update_cr(crs(range(Min,New_max),CRs_map),CR_name,CR2,CRS).

crs_unfold_and_remove(CRS,Name,Name_called,CRS3):-
	crs_get_cr(CRS,Name_called,CR_called),
	crs_remove_cr(CRS,Name_called,CRS1),
	crs_unfold_in_cr(CRS1,Name,CR_called,CRS3).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Entries is a list of entry(Head,Polyhedron)
entry_name(entry(Head,_),F/A):-
	functor(Head,F,A).

crse_empty(Initial,crse(Entries_empty,CRS_empty)):-
	crs_empty(Initial,CRS_empty),
	Entries_empty=[].
	


crse_remove_undefined_calls(crse(Entries,CRS),crse(Entries,CRS2)):-
	crs_remove_undefined_calls(CRS,CRS2).


crse_merge_crs(New_name,CR_to_merge,CRSE,CRSE1):-	
	CRSE=crse(Entries,CRS),
	maplist(crs_IOvars_arities(CRS),CR_to_merge,CR_with_arities),
	get_max_arities(CR_with_arities,Arity_input,Arity_output),
	%Calls
	crs_apply_all_ce(ce_substitute_calls(New_name/Arity_input/Arity_output,CR_with_arities),CRS,CRS2),
	%heads
	crs_merge_cr_head(CR_with_arities,New_name/Arity_input/Arity_output,CRS2,CRS3),
	%io info
	length(Ivars,Arity_input),
	length(Ovars,Arity_output),
	append(Ivars,Ovars,Vars),
	Head=..[New_name|Vars],
	crs_save_IOvars(CRS3,ioVars(Head,Ivars,Ovars),CRS4),
	%entries
	substitute_entries(New_name/Arity_input/Arity_output,CR_with_arities,Entries,Entries1),
	CRSE1=crse(Entries1,CRS4).
	
get_max_arities([],0,0).
get_max_arities([_Name/Ai/Ao|Names],MaxI,MaxO):-
	get_max_arities(Names,Ai2,Ao2),
	MaxI is max(Ai,Ai2),
	MaxO is max(Ao,Ao2).
	
	
substitute_entries(New_name,CR_to_merge,Entries,Entries1):-
	maplist(substitute_entry(New_name,CR_to_merge),Entries,Entries1).
		
substitute_entry(New_name,CR_to_merge,entry(Head,Cs),entry(Head_new,Cs)):-
	functor(Head,F,_A),
	(member(F/AI/AO,CR_to_merge)->
		get_new_head(Head,New_name,F/AI/AO,Head_new)
	;
		Head_new=Head
	).
	
	