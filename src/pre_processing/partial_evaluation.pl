/**  <module>  partial_evaluation

This module performs partial evaluation on a set of strongly connected components starting from an entry point
and obtaining direct recursion for each SCC.
The module uses the crs_btc/2 to know which equations have to be unfolded.

After the partial evaluation, it emits a warning with the SCC that are never called.

The module implementation is adapted from the module pubs_pe.pl in PUBS implemented by
  E.Albert, P.Arenas, S.Genaim, G.Puebla, and D.Zanardini
                        https://costa.ls.fi.upm.es

@author Antonio Flores Montoya

@copyright Copyright (C) 2014,2015 Antonio Flores Montoya

@license This file is part of CoFloCo. 
    CoFloCo is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    any later version.

    CoFloCo is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with CoFloCo.  If not, see <http://www.gnu.org/licenses/>.
*/
:- module(partial_evaluation,[partial_evaluation/4]).

:- use_module('SCCs',[scc_get_cover_points/2,
	scc_get_internal_callers/3,
	scc_update_unfold/4]).
:- use_module('../IO/output',[print_warning/2]).
:- use_module('../utils/cost_expressions',[cexpr_simplify_ctx_free/2]).
:- use_module('../utils/cost_structures',[cstr_join/3,cstr_or_compress/2]).
:- use_module('../utils/polyhedra_optimizations',[nad_normalize_polyhedron/2,nad_consistent_constraints_group/2,nad_project_group/3]).

:- use_module('../utils/crs',[
	entry_name/2,
	crs_empty/2,
	crs_get_ce_by_name_fresh/3,
	crs_get_ce/2,
	crs_add_eq/3,
	crs_get_cr/3,
	crs_remove_cr/3,
	crs_unfold_in_cr/4,
	cr_get_ids/2,
	ce_calls_accum/3,
	crs_get_names/2,
	crs_apply_all_ce/3,
	cr_is_cr_called_multiply/2
]).	
:- use_module(stdlib(numeric_abstract_domains),[nad_consistent_constraints/1,nad_project/3]).
:- use_module(stdlib(utils),[ut_varset/2,ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(counters),[counter_increase/3]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(terms)).
:-use_module(library(lambda)).

:-dynamic touched/1.

%! partial_evaluation is nondet
% for each entry, perform a partial evaluation (it has only been tried with one entry so far)
% after the partial evaluation, record the SCCs that are never called
% for SCCs that have recursive calls, add an auxiliary empty equation that will serve to simulate non-terminating chains
partial_evaluation(CRSE,SCCs,Ignored_set,CRSE2):-
	CRSE=crse(Entries,CRS),
	compute_residual_cr_names(Entries,SCCs,Residual_cr_names),
	retractall(touched(_)),
	compress_segments(SCCs,Residual_cr_names,CRS,CRS2),
	crs_empty(1,CRS_empty),
	maplist(entry_name,Entries,Entry_names),
	global_control(Entry_names,CRS2,Residual_cr_names,[],CRS_empty,CRS3),
	setof(Touched,touched(Touched),Touched_crs),
	
	CRSE2=crse(Entries,CRS3),
	crs_get_names(CRS,All_crs_names),
	difference_sl(All_crs_names,Touched_crs,Ignored_set),
	(Ignored_set\=[]->
		print_warning('Warning: the following predicates are never called:~p~n',[Ignored_set])
	;
		true
	).


	
	
compute_residual_cr_names(Entries,SCCs,Residual_set):-
	maplist(entry_name,Entries,Entry_names),
	maplist(scc_get_cover_points,SCCs,Cover_points),
	ut_flat_list([Cover_points,Entry_names],Residual),
	from_list_sl(Residual,Residual_set).
	
	
compress_segments([],_,CRS,CRS).
compress_segments([SCC|SCCs],Residual_cr_names,CRS,CRS_out):-	
	SCC=scc(recursive,Nodes,_,_,Info),!,
	from_list_sl(Nodes,Nodes_set),
	once(member(cover_points(Cover_points),Info)),
	difference_sl(Nodes_set,Cover_points,Unfoldable_nodes),
	exclude(contains_sl(Residual_cr_names),Unfoldable_nodes,Unfoldable_nodes_without_entries),
	compress_segments_in_scc(Unfoldable_nodes_without_entries,[],1,SCC,CRS,CRS1),
	compress_segments(SCCs,Residual_cr_names,CRS1,CRS_out).
	
compress_segments([SCC|SCCs],Residual_cr_names,CRS,CRS_out):-	
	SCC=scc(non_recursive,_Nodes,_,_,_Info),
	compress_segments(SCCs,Residual_cr_names,CRS,CRS_out).

		
	
compress_segments_in_scc([CR_name/A|Unfoldable_nodes],Not_compressed,Level,SCC,CRS,CRS_out):-
	crs_get_cr(CRS,CR_name,CR_to_unfold),
	
	%check if whe want to do it
	cr_get_ids(CR_to_unfold,Ids),
	length(Ids,N_eqs),
	N_eqs =< Level,

	scc_get_internal_callers(SCC,CR_name/A,QCallers),
	maplist(\QCaller_m^Caller_m^(QCaller_m=Caller_m/_),QCallers,Callers),
	%TODO get rid of this and do not make distinction
	maplist(crs_get_cr(CRS),Callers,CR_list),
	maplist(\CR_l^(\+cr_is_cr_called_multiply(CR_l,CR_name/A)),CR_list),
	
	!,	
	save_touched(CR_name/A),
	%remove cr
	crs_remove_cr(CRS,CR_name,CRS1),
	% and unfold the callers
	
	foldl(\Caller^CRS1_l^CRS2_l^crs_unfold_in_cr(CRS1_l,Caller,CR_to_unfold,CRS2_l),Callers,CRS1,CRS2),
	foldl(\Caller_l^SCC1_l^SCC2_l^scc_update_unfold(SCC1_l,Caller_l,CR_name/A,SCC2_l),QCallers,SCC,SCC1),
	%writeln(segment(F/A)),
	compress_segments_in_scc(Unfoldable_nodes,Not_compressed,Level,SCC1,CRS2,CRS_out).

		
compress_segments_in_scc([Node|Unfoldable_nodes],Not_compressed,Level,SCC,CRS,CRS_out):-
	compress_segments_in_scc(Unfoldable_nodes,[Node|Not_compressed],Level,SCC,CRS,CRS_out).



compress_segments_in_scc([],Not_compressed,Level,SCC,CRS,CRS_out):-
	Not_compressed\=[],!,
	(Level=10->
	  CRS=CRS_out
	 ;
	Level1 is Level +1,
	%writeln(level(Level1)),
	compress_segments_in_scc(Not_compressed,[],Level1,SCC,CRS,CRS_out)
	).
	
compress_segments_in_scc([],[],_Level,_SCC,CRS,CRS).

%! global_control(+Fs:list(term)) is det
% given a set of terms, unfold each one of them, collect new called terms and repeat
global_control([],_CRS,_Residual,_Done,CRS_new,CRS_new).
global_control([F|To_do],CRS,Residual,Done,CRS_accum,CRS_new):-
	insert_sl(Done,F,Done1),
	save_touched(F),
	unfold(F,CRS,Residual,New_eqs),
	foldl(\Eq_l^CRS_l^CRS_l2^crs_add_eq(CRS_l,Eq_l,CRS_l2),New_eqs,CRS_accum,CRS_accum2),
	collect_leaves(New_eqs,Leaves),
	difference_sl(Leaves,Done1,Pending),
	union_sl(To_do,Pending,To_do1),
	global_control(To_do1,CRS,Residual,Done1,CRS_accum2,CRS_new).
	
	
save_touched(Name):-
	touched(Name),!.
		
save_touched(Name):-
	assert(touched(Name)).

%! unfold(+Sg:term,-UnfClauses:list(cost_equation)) is det
%find all the partial evaluations of a term Sg
unfold(F,CRS,Residual,Eqs_new):-
	findall(Eq_new,resolve(F,CRS,Residual,Eq_new),Eqs_new).

%! resolve(+Sg:term,-UnfClause:cost_equations) is nondet
% partially evaluate one cost equation
resolve(Name/_Arity,CRS,Residual,UnfClause):-
	crs_get_ce_by_name_fresh(CRS,Name,eq(Head,Cost,Calls,Size)),
	Clause = pe_eq(Head,Cost,Calls,[],Size),
	derive(Clause,CRS,Residual,UnfClause).


% unfold each call to non_residual equations and collect the calls to the residual equations
derive(pe_eq(Sg,Exp,[],Residual,Size),_CRS,_Residual_names,ClauseC):-
	reverse(Residual,Calls),
	functor(Sg,F,A),
	split_calls(Calls,F,A,NR_calls,R_calls),
	nad_normalize_polyhedron(Size,Cs_normalized),
	ClauseC = eq_ref(Sg,Exp,NR_calls,R_calls,Calls,Cs_normalized,[]).
	

derive(pe_eq(Sg,Exp,[Call|Calls],Residual,Size),CRS,Residual_names,ClauseC):-
	functor(Call,Name,Arity),
	\+contains_sl(Residual_names,Name/Arity),!,
	save_touched(Name/Arity),
	crs_get_ce_by_name_fresh(CRS,Name,eq(Call,Exp0,Calls0,Size0)),
	append(Calls0,Calls,CCalls),
 	ClauseC0 = pe_eq(Sg,CombE,CCalls,Residual,CombSp),
    cstr_join(Exp,Exp0,CombE),
 	combine_size_relations(Size,Size0,CombS),
 	
 	%try to fail early
 %	/*
 	term_variables(Call,Vars),
 	nad_consistent_constraints_group(Vars,CombS),
 	term_variables((Sg,CombE,CCalls,Residual),Rest_vars),
 	nad_project(Rest_vars,CombS,CombSp),
 %*/
 %	CombSp=CombS,
	derive(ClauseC0,CRS,Residual_names,ClauseC).
	
derive(pe_eq(Sg,Exp,[Call|Calls],Residual,Size),CRS,Residual_names,ClauseC):-
	derive(pe_eq(Sg,Exp,Calls,[Call|Residual],Size),CRS,Residual_names,ClauseC).

combine_size_relations(S,CS,Tmp_CombS):-
	append(S,CS,CombS_u),
	from_list_sl(CombS_u,Tmp_CombS).


% get all the residual calls and refresh their variables
collect_leaves(Eqs,Leaves_set):-
	foldl(ce_calls_accum,Eqs,[],Leaves_set).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



split_calls([],_F,_A,[],[]).
split_calls([C|Calls],F,A,NR_Calls,R_Calls):-
	functor(C,F,A),
	!,
	R_Calls = [C|R_Calls0],
	split_calls(Calls,F,A,NR_Calls,R_Calls0).
split_calls([C|Calls],F,A,NR_Calls,R_Calls):-
	NR_Calls = [C|NR_Calls0],
	split_calls(Calls,F,A,NR_Calls0,R_Calls).



