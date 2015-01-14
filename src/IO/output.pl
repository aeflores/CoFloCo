/** <module> output

This module prints the results of the analysis

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


:- module(output,[print_help/0,
		  print_chains/1,
		  print_chain/2,
		  print_chains_entry/2,
		  print_results/2,
		  print_equations_refinement/2,
		  print_phase_termination_argument/4,
		  print_single_closed_result/2,
		  print_closed_results/2,
		  print_stats/0]).

:- use_module('../db',[eq_refined/2,loop_ph/4,eq_ph/7,upper_bound/4,closed_upper_bound/4,non_terminating_chain/2]).
:- use_module('../refinement/invariants',[backward_invariant/4]).
:- use_module('../refinement/chains',[chain/3]).

:- use_module('../utils/cost_expressions',[cexpr_add_list/2,get_asymptotic_class_name/2]).

:- use_module('../IO/params',[parameter_dictionary/3,get_param/2,
		      param_description/2]).

:- use_module(stdlib(profiling),[profiling_get_info/3]).
:- use_module(stdlib(counters),[counter_get_value/2]).



%! print_equations_refinement(+Head:term,+RefCnt:int) is det
% print the calls from the SCC Head in the refinement phase RefCnt
% if the verbosity is high enough
print_equations_refinement(Head,RefCnt):-
	get_param(v,[X]),X > 2,!,
	functor(Head,Name,Arity),
	format('Specialization of ~p ~n',[Name/Arity]),
	print_equations_refinement_1(Head,RefCnt).
print_equations_refinement(_,_).
	
print_equations_refinement_1(Head,RefCnt):-
	eq_ph(Head,(Eq_id,RefCnt),_,_,_,_,_),
	findall(Refined,
	        eq_refined(Eq_id,Refined),
	        Refined_list),
	maplist(get_non_rec_calls,Refined_list,Refined_pairs),
	(Refined_pairs=[First|Rest]->
		format('~p --> ~p ~n',[Eq_id,First]),
		maplist(print_specialized,Rest)
	    
	    ;
	    format('~p --> none ~n',[Eq_id])
	 ),fail.
print_equations_refinement_1(_,_):-nl.
	 
print_specialized(E):-
    format('    --> ~p ~n',[E]).
    	 
get_non_rec_calls(Id,Id:Calls):-
	eq_ph(_,(Id,_),_,NR_Calls,_,_,_),
	maplist(get_functor_call,NR_Calls,Calls).
get_functor_call((Call,Chain),(F/A,Chain)):-
	functor(Call,F,A).
	
%! print_phase_termination_argument(+Head:term,+Phase:phase,+Term_argument:termination_argument,+YesNo:flag) is det
% print the termination argument of Phase if Phase is an iterative phase and the verbosity
% is high enough
print_phase_termination_argument(Head,Phase,Term_argument,no):-
	get_param(v,[X]),X > 2,
	Phase=[_|_],
	copy_term((Head,Term_argument),(Head2,Term_argument2)),
	numbervars(Head2,0,_),
    format('~p: Phase ~p might not terminate:: ~p~n',[Head2,Phase,Term_argument2]).
print_phase_termination_argument(Head,Phase,Term_argument,yes):-
	get_param(v,[X]),X > 2,
	Phase=[_|_],
	copy_term((Head,Term_argument),(Head2,Term_argument2)),
	numbervars(Head2,0,_),
    format('~p: Phase ~p termination argument: ~p~n',[Head2,Phase,Term_argument2]).

print_phase_termination_argument(_Head,_Phase,_Term_argument,_).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_chains(+RefCnt:int) is det
%  print the inferred chains in the refinement phase RefCnt
print_chains(Ref_phase):-
	ansi_format([underline,bold],'Resulting Chains:~p ~n',[' ']),
	print_chains_1(Ref_phase).

print_chains_1(Ref_phase):-
	chain(Entry,Ref_phase,Pattern),
	numbervars(Entry,0,_),
	print_chain(Entry,Pattern),nl,
	fail.
print_chains_1(_).

%! print_chain(+Entry:term,Pattern:chain) is det
% print the chain Pattern
print_chain(Entry,Fusion):-
	Fusion=..[fusion|Chain_list],!,
	maplist(reverse,Chain_list,Chain_list_inv),
	(non_terminating_chain(Entry,Fusion)->
	   %Pattern=[_|Pattern1],
	   ansi_format([fg(red)],'~p:~p...',[Entry,fusion(Chain_list_inv)])
	 ;
	   ansi_format([],'~p:~p',[Entry,fusion(Chain_list_inv)])
	).
print_chain(Entry,Pattern):-
	reverse(Pattern,Pattern_inv),
	(non_terminating_chain(Entry,Pattern)->
	   %Pattern=[_|Pattern1],
	   ansi_format([fg(red)],'~p:~p...',[Entry,Pattern_inv])
	 ;
	   ansi_format([],'~p:~p',[Entry,Pattern_inv])
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_chains_entry(+Entry:term,+RefCnt:int) is det
% print the inferred chains in SCC Entry in the refinement phase RefCnt
print_chains_entry(Entry,RefCnt):-
	get_param(v,[X]),X > 2,
	numbervars(Entry,0,_),
	format('Resulting Chains of ~p ~n',[Entry]),
	print_chains_entry_1(RefCnt,Entry).
print_chains_entry(_,_).

print_chains_entry_1(RefCnt,Entry):-
	chain(Entry,RefCnt,Pattern),
	print_chain_simple(Pattern),nl,
	fail.
print_chains_entry_1(_,_):-nl.


print_chain_simple(Pattern):-
	reverse(Pattern,Pattern_inv),
	(non_terminating_chain(_,Pattern)->
	   %Pattern=[_|Pattern1],
	   ansi_format([fg(red)],'~p...',[Pattern_inv])
	 ;
	   ansi_format([],'~p',[Pattern_inv])
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_results(+Entry:term,+RefCnt:int) is det
% print the chains, invariants and uppuer bounds of SCC Entry in the refinement phase RefCnt
print_results(Entry,RefCnt):-
	numbervars(Entry,0,_),
	ansi_format([underline,bold],'Inferred cost of ~p: ~n',[Entry]),
	print_results_1(Entry,RefCnt).
print_results_1(Entry,RefCnt):-
	backward_invariant(Entry,(Chain,RefCnt),_,EPat),
 	upper_bound(Entry,Chain,_,CExp),
	print_chain(Entry,Chain),
	format(': ',[]),
	print_cost_structure(CExp),
	format(' when ~p ~n',[EPat]),
 	fail.
print_results_1(_Entry,_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_closed_results(+Entry:term,+RefCnt:int) is det
% print the chains, invariants and closed upper bounds of SCC Entry in the refinement phase RefCnt	
print_closed_results(Entry,RefCnt):-
	numbervars(Entry,0,_),
	ansi_format([underline,bold],'Solved cost expressions of ~p: ~n',[Entry]),
	(get_param(prolog_format,_)->
	  print_closed_results_prolog_format(Entry,RefCnt)
	  ;
	  print_closed_results_1(Entry,RefCnt)
	).

print_closed_results_1(Entry,RefCnt):-
	backward_invariant(Entry,(Chain,RefCnt),_,EPat),
 	closed_upper_bound(Entry,Chain,_,CExp),
	print_chain(Entry,Chain),
	format(': ~p  when ~p ~n',[CExp,EPat]),
 	fail.
print_closed_results_1(_Entry,_).

%! print_closed_results_prolog_format(+Entry:term,+RefCnt:int) is det
% print the chains, invariants and closed upper bounds of SCC Entry in the refinement phase RefCnt.  
% It prints the results in prolog terms.
print_closed_results_prolog_format(Entry,RefCnt):-
	backward_invariant(Entry,(Chain,RefCnt),_,EPat),
 	closed_upper_bound(Entry,Chain,_,CExp),
	format('eq(~p,~p,~p). ~n',[Entry,CExp,EPat]),
 	fail.
print_closed_results_prolog_format(_Entry,_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_single_closed_result(+Entry:term,+Expr:cost_expression) is det
% print the given upper bound Expr and its asymptotic bound
print_single_closed_result(Entry,Expr):-
	copy_term((Entry,Expr),(Entry2,Expr2)),
	get_asymptotic_class_name(Expr,Asym_class),
	numbervars(Entry2,0,_),
	ansi_format([underline,bold],'Maximum cost of ~p: ',[Entry2]),
	format('~p ~n',[Expr2]),
	format('Asymptotic class: ~p ~n',[Asym_class]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_cost_structure(cost(Exp,Loops,Conditions)):-
	print(Exp),
	print_cs_loops(Loops,1,_),nl,
	print_cs_conditions(Conditions).

print_cs_loops([],N,N).
print_cs_loops([loop(It_var,Exp,InternalLoops,Conds)|Loops],N,Nout):-
	it_var_name(It_var,N),
	N2 is N+1,
	format('+~p*(~p',[It_var,Exp]),
	print_cs_loops(InternalLoops,N2,N3),
	format(')',[]),
	print_cs_conditions(Conds),
	print_cs_loops(Loops,N3,Nout).

print_cs_conditions([]).
print_cs_conditions([C|Conditions]):-
	format(' such that ',[]),
	print_cs_conditions_1([C|Conditions]),
	nl.
print_cs_conditions_1([]).
print_cs_conditions_1([C|Cs]):-
	print_norm(C),
	format(',',[]),
	print_cs_conditions_1(Cs).

print_norm(norm(Its,E)):-
	atomic_list_concat(Its,'+',It),
	format('~p=<~p',[It,E]).

it_var_name(It_var,N):-
	atom_concat(it,N,It_var).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_help is det
% print information about the input parameters
print_help:-
	print_help_header,
	print_parameters_list.
%	format('~nExamples of use:~n~n',[]),
%	print_examples.

print_help_header:-
	format('~tCoFloCo~nUsage: cofloco [Options]~n where:~n',[]).

print_parameters_list:-
    param_description(Param,Description),
    findall(Name,parameter_dictionary(Name,Param,_),Names),
    format('~p  ~p ~n',[Names,Description]),
    fail.
print_parameters_list.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! print_stats is det
% print time statistics of the different phases of the analysis
print_stats:-
	profiling_get_info(pe,T_pe,_),
	profiling_get_info(inv,T_inv,_),
	profiling_get_info(unfold,T_unfold,_),
	profiling_get_info(ubs,T_ubs,_),

	profiling_get_info(loop_phases,T_loop_phases,_),
	profiling_get_info(chain_solver,T_chain_solver,_),
	profiling_get_info(equation_cost,T_equation_cost,_),
	profiling_get_info(flatten_loops,T_flatten,_),
	profiling_get_info(compress_or,T_compress_or,_),
	
	profiling_get_info(solver,T_solver,_),
	profiling_get_info(termination,T_termination,_),
	
	profiling_get_info(black_cost,T_black_cost,_),
	
	counter_get_value(compressed_phases1,N_compressed_phases1),
	counter_get_value(compressed_invs,N_compressed_invs),
	counter_get_value(compressed_chains,N_compressed_chains),
	format("Partial evaluation computed in ~0f ms.~n",[T_pe]),
	format("Invariants computed in ~0f ms.~n",[T_inv]),
	format("Refinement performed in ~0f ms.~n",[T_unfold]),
	format("Termination proved in ~0f ms.~n",[T_termination]),
	format("Upper bounds computed in ~0f ms.~n",[T_ubs]),
		format("----Phase cost structures ~0f ms.~n",[T_loop_phases]),
		format("--------Equation cost structures ~0f ms.~n",[T_equation_cost]),
		format("--------Inductive compression(1) ~0f ms.~n",[T_flatten]),
		format("--------Inductive compression(2) ~0f ms.~n",[T_compress_or]),
		format("--------Black Cost ~0f ms.~n",[T_black_cost]),
		format("----Chain cost structures ~0f ms.~n",[T_chain_solver]),
		format("----Solving cost expressions ~0f ms.~n",[T_solver]),
		
		format("~nCompressed phase information: ~p ~n",[N_compressed_phases1]),
		format("Compressed Chains: ~p ~n",[N_compressed_chains]),
		format("Compressed invariants: ~p ~n",[N_compressed_invs]).

print_stats.