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
:- module(partial_evaluation,[partial_evaluation/0]).

:- use_module('SCCs',[crs_btc/2,ignored_scc/1]).
:- use_module('../db',[entry_eq/2,eq_ph/7,non_terminating_stub/2, input_eq/5 ,add_eq_ph/3,cofloco_aux_entry_name/1]).


:- use_module('../utils/polyhedra_optimizations',[nad_consistent_constraints_group/2,nad_project_group/3]).
%:- use_module(stdlib(numeric_abstract_domains),[nad_project/3,nad_consistent_constraints/1]).
:- use_module(stdlib(utils),[ut_varset/2]).
:- use_module(stdlib(set_list)).





%! pe_eq(Head:term,Exp:cost_expression,Calls:list(term),Size:polyhedron)
% stores a partially evaluated cost equation
:- dynamic pe_eq/4.

%! partial_evaluation is nondet
% for each entry, perform a partial evaluation (it has only been tried with one entry so far)
% after the partial evaluation, record the SCCs that are never called
% for SCCs that have recursive calls, add an auxiliary empty equation that will serve to simulate non-terminating chains
partial_evaluation :-
	retractall(pe_eq(_,_,_,_)),
	entry_eq(Call,_),
	pe_aux(Call),%FIXME take the entry condition into account
	findall(F/A,
	        (crs_btc(F,A),functor(Head,F,A),\+pe_atom(Head),\+cofloco_aux_entry_name(F))
	        ,Ignored),
	(Ignored\=[]->
	   format('Warning: the following predicates are never called:~p~n',[Ignored]);true),
	 maplist(add_ignored_scc,Ignored),       
	add_non_terminating_stubs.

add_ignored_scc(X):-
	assert(ignored_scc(X)).
	
% for SCCs that have recursive calls, add an auxiliary empty equation that will serve to simulate non-terminating chains	
add_non_terminating_stubs:-
	eq_ph(Head,(_,0),_,_,[_|_],_,_),
	\+non_terminating_stub(Head,_),
	add_eq_ph(eq_ph(Head,0,0,[],[],[],[]),non_terminating,none),
	fail.
add_non_terminating_stubs.

pe_aux(Entry):-
	partially_evaluate_cost_rel([Entry]),
	replace_cost_relations.

partially_evaluate_cost_rel(Entries):-
	reset_atoms,
	global_control(Entries).
	
:- dynamic pe_atom/1.

reset_atoms:-
	retractall(pe_atom(_)).

add_atom(X):-
	asserta(pe_atom(X)).

is_done(X):-
	pe_atom(X).


%! global_control(+Fs:list(term)) is det
% given a set of terms, unfold each one of them, collect new called terms and repeat
global_control([]).
global_control([F|Fs]):-
	is_done(F),!,
	global_control(Fs).
global_control([F|Fs]):-
	add_atom(F),
	unfold(F,UnfClauses),
	collect_leaves(UnfClauses,Leaves),
	append(Fs,Leaves,NFs),
	global_control(NFs).

%! unfold(+Sg:term,-UnfClauses:list(cost_equation)) is det
%find all the partial evaluations of a term Sg
unfold(Sg,UnfClauses):-
	findall(UnfClause,resolve(Sg,UnfClause),UnfClauses).

%! resolve(+Sg:term,-UnfClause:cost_equations) is nondet
% partially evaluate one cost equation
resolve(Sg,UnfClause):-
	copy_term(Sg,NSg),
	get_initial_clause(NSg,Exp,Calls,Size),
	Clause = pe_eq(NSg,Exp,Calls,[],Size),
	derive(Clause,UnfClause),
	assertz(UnfClause).

get_initial_clause(NSg,Exp,Calls,Size):-
	input_eq(NSg,_,Exp,Calls,Size).

is_unfoldable(Ca):-
	functor(Ca,F,A),
	\+ crs_btc(F,A).

% unfold each call to non_residual equations and collect the calls to the residual equations
derive(pe_eq(Sg,Exp,[],Residual,Size),ClauseC):-
	reverse(Residual,RResidual),
	ClauseC = pe_eq(Sg,Exp,RResidual,Size).

derive(pe_eq(Sg,Exp,[Call|Calls],Residual,Size),ClauseC):-
	is_unfoldable(Call),!,
 	input_eq(Call,_,Exp0,Calls0,Size0),
	append(Calls0,Calls,CCalls),
 	ClauseC0 = pe_eq(Sg,CombE,CCalls,Residual,CombSp),
    combine_cost_expressions(Exp,Exp0,CombE),
 	combine_size_relations(Size,Size0,CombS),
 	
 	%try to fail early
 %	/*
 	term_variables(Call,Vars),from_list_sl(Vars,Vars_set),
 	nad_consistent_constraints_group(Vars,CombS),
 	term_variables((ClauseC0,CombS),Total_vars),from_list_sl(Total_vars,Total_vars_set),
 	term_variables(CombE,Essential_vars),from_list_sl(Essential_vars,Essential_vars_set),
 	difference_sl(Total_vars_set,Vars_set,Rest_vars),
 	union_sl(Rest_vars,Essential_vars_set,Rest_vars2),
 	nad_project_group(Rest_vars2,CombS,CombSp),
 %*/
 %	CombSp=CombS,
	derive(ClauseC0,ClauseC).
derive(pe_eq(Sg,Exp,[Call|Calls],Residual,Size),ClauseC):-
	derive(pe_eq(Sg,Exp,Calls,[Call|Residual],Size),ClauseC).

combine_size_relations(S,CS,Tmp_CombS):-
	append(S,CS,CombS_u),
	from_list_sl(CombS_u,Tmp_CombS).

combine_cost_expressions(Exp,Exp0,Exp+Exp0).


% get all the residual calls and refresh their variables
collect_leaves([],[]).
collect_leaves([Cl|Cls],Leaves):-
	get_leaves(Cl,L),
	append(L,Ls,Leaves),
	collect_leaves(Cls,Ls).

get_leaves(pe_eq(_,_,Calls,_),Leaves):-
	filter_all(Calls,Leaves).

filter_all([],[]).
filter_all([C|Cs],[FC|FCs]):-
	make_dynamic(C,FC),
	filter_all(Cs,FCs).

make_dynamic(C,FC):-
	functor(C,F,A),
	functor(FC,F,A).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! replace_cost_relations is det
% for each partially evaluated equation:
% * split the recursive and non-recursive calls
% * check it's feasible
% * store in the general database (db.pl)
replace_cost_relations:-
	retract(pe_eq(Head,Exp,Calls,Size)),
	functor(Head,F,A),
	split_calls(Calls,F,A,NR_Calls,R_Calls),
	ut_varset((Head,Exp,Calls),Vars),	
	(nad_consistent_constraints_group(Vars,Size) ->	    
	    nad_project_group(Vars,Size,P_Size),
	  % nad_project(Vars,Size,P_Size),
	    add_eq_ph(eq_ph(Head,0,Exp,NR_Calls,R_Calls,Calls,P_Size),terminating,none)
	;
	    true
	),
	fail.
replace_cost_relations.

split_calls([],_F,_A,[],[]).
split_calls([C|Calls],F,A,NR_Calls,R_Calls):-
	functor(C,F,A),
	!,
	R_Calls = [C|R_Calls0],
	split_calls(Calls,F,A,NR_Calls,R_Calls0).
split_calls([C|Calls],F,A,NR_Calls,R_Calls):-
	NR_Calls = [C|NR_Calls0],
	split_calls(Calls,F,A,NR_Calls0,R_Calls).


