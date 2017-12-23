:- module(crs,[
		ce_head/2,
		ce_constraints/2,
		ce_calls/2,
		ce_rec_calls/2,
		ce_equal/2,
		ce_more_general_than/2,
		ce_calls_accum/3,
		ce_get_refined/2,
		ce_get_cost/2,
		ce_set_cost/3,
		ce_add_property/4,
	
			
		cr_empty/2,
		cr_get_ce_by_id/3,
		cr_get_ce_by_id_fresh/3,
		cr_head/2,
		cr_nameArity/2,
		cr_get_ids/2,
		cr_add_eq/5,
		cr_get_ce/2,
		cr_IOvars/2,
		cr_get_ceList/2,
		cr_get_ceList_with_id/2,
		cr_apply_all_ce/3,
		cr_apply_all_ce_with_id/3,
		cr_set_loops/3,
		cr_get_loops/2,
		cr_set_chains/3,
		cr_get_chains/2,
		cr_is_cr_called_multiply/2,
		cr_get_forward_invariant/2,
		cr_strengthen_with_ce_invs/5,
		cr_set_external_patterns/3,
		cr_get_external_patterns/2,
		
		crs_empty/2,
		crs_range/2,
		crs_add_eq/3,
		crs_get_ce_by_id/3,
		crs_get_ce_by_name/3,
		crs_get_ce/2,
		crs_get_cr/3,
		crs_save_IOvars/3,
		crs_IOvars/3,
		crs_IOvars_arities/3,
		crs_get_graph/2,
		crs_apply_all_ce/3,
		crs_get_names/2,
		crs_get_ce_by_name_fresh/3,	
		crs_unfold_in_cr/4,
		crs_unfold_and_remove/4,
		crs_remove_cr/3,
		crs_update_cr/4,
		crs_update_cr_forward_invariant/4,
		crs_update_forward_invariants_with_calls_from_cr/3,
		crs_get_cr_external_patterns/3,
		
		crse_empty/2,
		crse_remove_undefined_calls/2,
		crse_merge_crs/4,
		
		entry_name/2
	]).
 
 :-use_module('../refinement/invariants',[
  			  ce_invs_head/2,
		      ce_invs_map/2
		      ]).
		      
:-use_module(cofloco_utils,[zip_with_op3/5]).
:-use_module(cost_structures,[cstr_join/3]).
:-use_module('../IO/output',[print_warning/2]).
:-use_module(stdlib(numeric_abstract_domains),[nad_consistent_constraints/1,nad_entails/3,nad_glb/3,nad_lub/6,nad_project/3]).
:-use_module(polyhedra_optimizations,[nad_consistent_constraints_group/2,nad_project_group/3]).
:-use_module(stdlib(list_map)).
:-use_module(stdlib(set_list)).
:-use_module(library(lambda)).

%eq(Head,Cost,Calls,Cs)
%eq_ref(Head,Cost,NR_calls,R_calls,Calls,Cs,Info)
%these predicates are defined for both kinds of equations


ce_head(eq(Head,_,_,_),Head).
ce_head(eq_ref(Head,_,_,_,_,_,_),Head).

ce_constraints(eq(_Head,_,_,Cs),Cs).
ce_constraints(eq_ref(_Head,_,_,_,_,Cs,_),Cs).

ce_pair_is_feasible((_,CE)):-
	ce_constraints(CE,Cs),
	nad_consistent_constraints(Cs).
	
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

ce_rec_calls(eq_ref(_,_,_,Rec_calls,_,_,_),Rec_calls).

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


ce_accum_forward_invariants(eq_ref(_Head,_Cost_str,NR_calls,_R_calls,_Calls,Cs,_Info),Map,Map1):-
	copy_term((NR_calls,Cs),(NR_calls1,Cs2)),
	foldl(accum_forward_invariants(Cs2),NR_calls1,Map,Map1).
	
accum_forward_invariants(Cs,Call,Map,Map1):-
	Call=..[Name|Vars],
	nad_project(Vars,Cs,Fwd_inv),
	(lookup_lm(Map,Name,(Vars,Fwd_inv1))->
		nad_lub(Vars,Fwd_inv,Vars,Fwd_inv1,Vars,Fwd_inv2),
		insert_lm(Map,Name,(Vars,Fwd_inv2),Map1)
		;
		insert_lm(Map,Name,(Vars,Fwd_inv),Map1)
	).
	
ce_strengthen(eq_ref(Head,Cost_str,NR_calls,R_calls,Calls,Cs,Info),head,inv(Head,Inv),
			  eq_ref(Head,Cost_str,NR_calls,R_calls,Calls,Cs2,Info)):-!,
	nad_glb(Cs,Inv,Cs2).
	
ce_strengthen(eq_ref(Head,Cost_str,NR_calls,R_calls,Calls,Cs,Info),call,inv(Call,Inv),
			  eq_ref(Head,Cost_str,NR_calls,R_calls,Calls,Cs2,Info)):-
		foldl(strengthen_call,R_calls,(inv(Call,Inv),Cs),(_,Cs2)).
       

strengthen_call(Call,(inv(Head,Inv),Cs),(inv(Head,Inv),Cs2)):-
	copy_term(inv(Head,Inv),inv(Call,Inv2)),
	nad_glb(Cs,Inv2,Cs2).

ce_add_property(eq_ref(Head,Cost_str,NR_calls,R_calls,Calls,Cs,Info),Name,Value,eq_ref(Head,Cost_str,NR_calls,R_calls,Calls,Cs,Info2)):-
	insert_lm(Info,Name,Value,Info2).

ce_get_property(eq_ref(_Head,_Cost_str,_NR_calls,_R_calls,_Calls,_Cs,Info),Name,Value):-
	lookup_lm(Info,Name,Value).
	
ce_get_refined(Eq,Id):-
	ce_get_property(Eq,refined,refined(Id)).
	
ce_get_cost(Eq,Cost):-
	ce_get_property(Eq,cost,Cost).
	
ce_set_cost(Eq,Cost,Eq2):-
	ce_add_property(Eq,cost,Cost,Eq2).	

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
% cr(Name/Arity,map(Id,Eq),Properties)
% Properties can contain ioVars, loops, chains, external_patterns and fwd_inv
cr_empty(Head,cr(Name/Arity,Empty_map,[])):-
	functor(Head,Name,Arity),
	empty_lm(Empty_map).

cr_get_eq_map(cr(_,Map,_),Map).

cr_add_eq_pair((Id,Eq),cr(Name/Arity,Map,Properties),cr(Name/Arity,Map2,Properties)):-
	insert_lm(Map,Id,Eq,Map2).
	
cr_add_eq(cr(Name/Arity,Map,Properties),Id,Eq,cr(Name/Arity,Map2,Properties),Id_next):-
	ce_head(Eq,Head),
	assertion(functor(Head,Name,Arity)),
	(cr_ce_is_subsumed(cr(Name/Arity,Map,Properties),Eq)->
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

	
cr_ce_is_subsumed(cr(_,Map,_Properties),Eq):-
	values_lm(Map,Eqs),
	member(Eq1,Eqs),
	ce_equal(Eq,Eq1),!.

cr_ce_is_subsumed(cr(_,Map,_Properties),Eq):-
	values_lm(Map,Eqs),
	member(Eq1,Eqs),
	ce_more_general_than(Eq1,Eq),!.	
	
cr_get_ce_by_id(cr(_,Map,_),Id,Eq):-
	lookup_lm(Map,Id,Eq).
	
cr_get_ce_by_id_fresh(cr(_,Map,_),Id,Eq_fresh):-
	lookup_lm(Map,Id,Eq),
	copy_term(Eq,Eq_fresh).	
	
cr_head(cr(Name/Arity,_,_),Head):-
	functor(Head,Name,Arity).
cr_nameArity(cr(Name/Arity,_,_),Name/Arity).	
	

cr_get_edges_accum(cr(F1/A1,CEs_map,_),Accum,Edges):-
	values_lm(CEs_map,CEs),
	foldl(ce_get_edges_accum(F1/A1),CEs,Accum,Edges).
	
cr_get_ids(cr(_,Map,_),Ids):-
	keys_lm(Map,Ids).
	
cr_get_ceList(cr(_,Map,_),CE_list):-
	values_lm(Map,CE_list).
	
cr_get_ceList_with_id(cr(_,Map,_),Map).

cr_get_ce(cr(_,Map,_),CE):-
	values_lm(Map,CE_list),
	member(CE,CE_list).
	
cr_apply_all_ce(Pred,cr(NameArity,EqMap,Properties),cr(NameArity,EqMap2,Properties)):-
	map_values_lm(Pred,EqMap,EqMap2).
	
cr_apply_all_ce_with_id(Pred,cr(NameArity,EqMap,Properties),cr(NameArity,EqMap2,Properties)):-
	maplist(Pred,EqMap,EqMap2).
%cr_exclude_CEs(Pred,cr(NameArity,EqMap,Loops,Chains,Properties),cr(NameArity,EqMap2,Loops,Chains,Properties),Excluded):-
%	partition(second_is(Pred),EqMap,Excluded,EqMap2).

second_is(Pred,(_,Elem)):-
	call(Pred,Elem).

%cr_check_all_ce(Pred,cr(_NameArity,EqMap,_Loops,_Chains,_Properties)):-%
%	check_values_lm(Pred,EqMap).

cr_check_some_ce(Pred,cr(_NameArity,EqMap,_Properties)):-
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
	
	
cr_strengthen_with_ce_invs(cr(NameArity,EqMap,Properties),HeadCall,CE_invs,
							cr(NameArity,EqMap3,Properties),Discarded):-
	ce_invs_head(CE_invs,HeadInv),
	ce_invs_map(CE_invs,InvMap),
	zip_lm(EqMap,InvMap,Composed_map),
	map_values_lm(strengthen_pair(HeadCall,HeadInv),Composed_map,EqMap2),
	partition(ce_pair_is_feasible,EqMap2,EqMap3,Discarded_pairs),
	keys_lm(Discarded_pairs,Discarded).

strengthen_pair(HeadCall,HeadInv,both(Eq,Inv),Eq2):-!,	
	ce_strengthen(Eq,HeadCall,inv(HeadInv,Inv),Eq2).
%if there is no ce invariant the ce is not reachable
strengthen_pair(HeadCall,HeadInv,left(Eq),Eq2):-	
	ce_strengthen(Eq,HeadCall,inv(HeadInv,[1=0]),Eq2).	

cr_get_called_forward_invariants(CR,Map,Map1):-
	cr_get_ceList(CR,CEs),
	foldl(ce_accum_forward_invariants,CEs,Map,Map1).

cr_get_max_id(CR,Max_cr):-
	cr_get_eq_map(CR,Eq_map),
	once(append(_,[(Max_cr,_)],Eq_map)).	
	
cr_get_property(cr(_NameArity,_EqMap,Properties),Name,Property):-
	lookup_lm(Properties,Name,Property).
cr_set_property(cr(NameArity,EqMap,Properties),Name,Property,cr(NameArity,EqMap,Properties2)):-
	insert_lm(Properties,Name,Property,Properties2).

	
cr_save_IOvars(CR,ioVars(Head,Ivars,Ovars),CR2):-
	cr_nameArity(CR,Name/Arity),
	assertion(functor(Head,Name,Arity)),
	(cr_get_property(CR,ioVars,ioVars(Head,Ivars2,Ovars2))->
		CR2=CR,
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
  		cr_set_property(CR,ioVars,ioVars(Head,Ivars,Ovars),CR2)
  	).

cr_IOvars(CR,IOvars_fresh):-
	(cr_get_property(CR,ioVars,ioVars(Head,Ivars,Ovars))->
		true
		;	
		%default value is that all variables are input variables
		cr_nameArity(CR,Name/Arity),
		functor(Head,Name,Arity),
		Head=..[Name|Ivars],
		Ovars=[]
	),
	copy_term(ioVars(Head,Ivars,Ovars),IOvars_fresh).
	
cr_IOvars_arities(CR,Iarity,Oarity):-
	cr_IOvars(CR,ioVars(_,Ivars,Ovars)),
	length(Ivars,Iarity),
	length(Ovars,Oarity).
	
	
		
cr_set_loops(CR,Loops,CR2):-
	cr_set_property(CR,loops,Loops,CR2).
cr_get_loops(CR,Loops):-
	cr_get_property(CR,loops,Loops).

cr_set_chains(CR,Chains,CR2):-
	cr_set_property(CR,chains,Chains,CR2).
cr_get_chains(CR,Chains):-
	cr_get_property(CR,chains,Chains).

cr_set_external_patterns(CR,Ext_patt,CR2):-
	cr_set_property(CR,external_patterns,Ext_patt,CR2).
cr_get_external_patterns(CR,Ext_patt):-
	cr_get_property(CR,external_patterns,Ext_patt).

cr_update_cr_forward_invariant(CR,Head,Cs,CR2):-
	(cr_get_property(CR,fwd_inv,fwd_inv(Head,Cs2))->
		nad_lub(Cs,Cs2,Cs_lub),
		cr_set_property(CR,fwd_inv,fwd_inv(Head,Cs_lub),CR2)
		;
		cr_set_property(CR,fwd_inv,fwd_inv(Head,Cs),CR2)
	).	
cr_get_forward_invariant(CR,fwd_inv(Head,Cs)):-
	cr_get_property(CR,fwd_inv,fwd_inv(Head,Cs)).



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

crs_update_cr(crs(range(Min,Max),CRs_map),Name,New_CR,crs(range(Min,Max_new),CRs_map2)):-
	cr_get_max_id(New_CR,Max_cr),
	Max_new is max(Max_cr+1,Max),
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

crs_update_cr_forward_invariant(CRS,Head,Cs,CRS2):-
	functor(Head,Name,_),
	crs_get_cr(CRS,Name,CR),
	cr_update_cr_forward_invariant(CR,Head,Cs,CR2),
	crs_update_cr(CRS,Name,CR2,CRS2).
	
crs_update_forward_invariants_with_calls_from_cr(CRS,CR,CRS2):-
	empty_lm(Empty_map),
	cr_get_called_forward_invariants(CR,Empty_map,Map),
	foldl(\Pair^CRS_l^CRS_l2^(
				Pair=(Name,(Vars,Cs)),
				Head=..[Name|Vars],
				crs_update_cr_forward_invariant(CRS_l,Head,Cs,CRS_l2)
				),Map,CRS,CRS2).

crs_get_cr_external_patterns(CRS,Head,External_patt):-
	functor(Head,Name,_),
	crs_get_cr(CRS,Name,CR),
	cr_get_external_patterns(CR,External_patt).
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
	
	