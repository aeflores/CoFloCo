#!/usr/bin/prolog

/** <module> lisp2ces

Translate a list of lisp functions into a cost relation representation

@author Antonio Flores Montoya

@copyright Copyright (C) 2014-2016 Antonio Flores Montoya

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

:-set_prolog_flag(verbose, silent). 
:-include('../../src/search_paths.pl').

:-initialization main.

:-use_module(lisp_parser,[parse_lisp/2]).
:-use_module(basic_lisp,[eq/4]).

:- use_module(stdlib(utils),[ut_flat_list/2]).	
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).
:- use_module(stdlib(set_list),[insert_sl/3,contains_sl/2,difference_sl/3,remove_sl/3]).
:- use_module(stdlib(counters),[counter_initialize/2,counter_increase/3,counter_get_value/2]).

:-dynamic if_cnt/1.
:-dynamic atom_size/2.
	
main:-
    current_prolog_flag(argv, Args),
	Args=[File|_Rest],
	catch(
	  (
	  parse_lisp(File,S_expressions),
	  counter_initialize(if_cnt,0),
	  counter_initialize(atom_cnt,2),
	  maplist(defun2cost_exp,S_expressions,All_cost_relations),
	  ut_flat_list(All_cost_relations,All_cost_relations_flat),
	  compute_undefined_predicates(All_cost_relations_flat,Undefined_predicates),
	  load_basic_lisp(Basic_lisp_crs),
	  % print basic lisp functions that are referenced by the main program
	  print_basic_lisp(Basic_lisp_crs,Undefined_predicates)
	  ),Fail,writeln(Fail)),
	halt.



% main transformation predicate
% take a function definition and generate a list of cost relations (and print them)	
defun2cost_exp(['defun-simplified',Name,Args,Body_with_quotes],All_cost_relations):-
	%FIXME: quotes such as '(a b) are currently not parsed correcty
	fix_quotes(Body_with_quotes,Body),
	% create map from variable names to prolog variables
	make_dicc(Args,Args_abstract,Dicc),
	% obtain a set of calls from the body (and possibly cost relations defined inside)
	unroll_body(Dicc,Body,Body_unrolled,Res_var,Cost_relations),
	append(Args_abstract,[Res_var],All_args),
	Head=..[Name|All_args],
	% the main cost relation
	Cost_relation= eq(Head,1,Body_unrolled,[]),
	% we want closed-form bound for this cost relation
	ut_flat_list([Cost_relation|Cost_relations],All_cost_relations),
	maplist(print_cr,All_cost_relations),!.

defun2cost_exp(['defined-locally',Name,NArgs],[Entry]):-
	atom_number(NArgs,Nargs_number),
	NArgs1 is Nargs_number+1,
	length(Args,NArgs1),
	Head=..[Name|Args],
	Entry= entry(Head:[]),
	print_cr(Entry),!.
	
defun2cost_exp(Other,_):-
	format(user_error,'Failed translating S-expression: ~p~n',[Other]),
	throw(error('Failed translating S-expression',Other)).

% unroll_body process a body and extracts a set of calls that define its behavior
% it also generate a set of cost relations that are defined inside the body (in particular, 'if' cost relations)

% a variable	
unroll_body(Dicc,Var_name,[],Var,[]):-
	lookup_lm(Dicc,Var_name,Var).

% an atom	
unroll_body(_Dicc,Quoted_atom,[],Size,[]):-
	atom(Quoted_atom),
	atom_concat('\'',Atom,Quoted_atom),!,
	size_atom(Atom,Size).
	
unroll_body(_Dicc,Atom,[],Size,[]):-
	atom(Atom),!,
	size_atom(Atom,Size).
	

% if expression
unroll_body(Dicc,[if,Cond,Cond_yes,Cond_no],Body_unrolled,Res_var,Cost_relations):-!,
	%get a fresh name
	get_if_name(If_name),
	% get the calls in the condition, the 'then' branch and the 'else' branch
	unroll_body(Dicc,Cond,Cond_calls,Cond_bool,Cost_relations_cond),
	unroll_body(Dicc,Cond_yes,Yes_calls,Res_var_yes,Cost_relations_yes),
	unroll_body(Dicc,Cond_no,No_calls,Res_var_no,Cost_relations_no),
	%we generate two cost relations:
	% when the condition is true and when it is not
	append(Cond_calls,Yes_calls,Yes_calls_all),
	append(Cond_calls,No_calls,No_calls_all),
	get_args(Dicc,Args),
	append(Args,[Res_var_yes],All_args_yes),Head_if_yes=..[If_name|All_args_yes],
	append(Args,[Res_var_no],All_args_no),Head_if_no=..[If_name|All_args_no],
	append(Args,[Res_var],All_args),Head_if=..[If_name|All_args],
	Cost_relation_yes=eq(Head_if_yes,1,Yes_calls_all,[Cond_bool=1]),
	Cost_relation_no=eq(Head_if_no,1,No_calls_all,[Cond_bool=0]),
	ut_flat_list([Cost_relation_yes,Cost_relation_no,Cost_relations_cond,Cost_relations_yes,Cost_relations_no],Cost_relations),
	% for the body where the if appears, we generate a call to the if cost relation
	Body_unrolled=[Head_if].

% Let does not appear in simplified lisp
%unroll_body(Dicc,[let, Defs,Exp],Body_unrolled,Res_var,Cost_relations):-%
%	unroll_definitions(Defs,Dicc,Dicc1,Calls_defs,Cost_relations1),
%	unroll_body(Dicc1,Exp,Calls_exp,Res_var,Cost_relations2),
%	append(Calls_defs,Calls_exp,Body_unrolled),
%	append(Cost_relations1,Cost_relations2,Cost_relations).
	
% lambdas are used to express let expressions in simplified lisp	
unroll_body(Dicc,[[lambda,New_vars,Exp]| Def_exps],Body_unrolled,Res_var,Cost_relations):-
	couple_definitions(New_vars,Def_exps,Defs),
	unroll_definitions(Defs,Dicc,Dicc1,Calls_defs,Cost_relations1),
	unroll_body(Dicc1,Exp,Calls_exp,Res_var,Cost_relations2),
	append(Calls_defs,Calls_exp,Body_unrolled),
	append(Cost_relations1,Cost_relations2,Cost_relations).	

% coerce is type casting, for now we ignore it	
unroll_body(Dicc,[coerce,Exp,_Type],Body_unrolled,Res_var,Cost_relations):-
	unroll_body(Dicc,Exp,Body_unrolled,Res_var,Cost_relations).


%generic function call	
unroll_body(Dicc,[Function|Args],Body_unrolled,Res_var,Cost_relations):-
	atom(Function),
	maplist(unroll_body(Dicc),Args,Calls,Res_vars,Cost_relations),
	append(Res_vars,[Res_var],All_args),
	Top_call=..[Function|All_args],
	ut_flat_list([Calls,Top_call],Body_unrolled),!.

%something else
unroll_body(_Dicc,Expr,_Body_unrolled,_Res_var,_Cost_relations):-
	format(user_error,'Unknown Function format: ~p~n',[Expr]),fail.

% predicates to deal witht the lambda expressions and let

couple_definitions(Vars,Exps,Defs):-
	maplist(couple_definition,Vars,Exps,Defs).
couple_definition(Var,Exp,[Var, Exp]).

% update the variable map
unroll_definitions([],Dicc,Dicc,[],[]).
unroll_definitions([[Var_name,Exp]|Defs],Dicc,Dicc_final,Calls,Cost_relations):-
	unroll_body(Dicc,Exp,Calls_exp,Res_var,Cost_relations_exp),
	insert_lm(Dicc,Var_name,Res_var,Dicc1),
	unroll_definitions(Defs,Dicc1,Dicc_final,Calls_aux,Cost_relations_aux),
	append(Calls_exp,Calls_aux,Calls),
	append(Cost_relations_exp,Cost_relations_aux,Cost_relations).


	
size_atom(nil,0):-!.
size_atom(t,1):-!.
size_atom(Atom,Int):-
	atom_number(Atom,Int),!.
size_atom(String,Length):-
	atom_codes(String,[DoubleQuote|Codes]),
	atom_codes('"',[DoubleQuote]),!,
	length(Codes,N),
	Length is N-1.

size_atom(Atom,Size):-
	atom_size(Atom,Size),!.
size_atom(Atom,Size):-
	counter_increase(atom_cnt,1,Size),
	assert(atom_size(Atom,Size)),!.
	
size_atom(Atom,_Length):-
	format(user_error,'No size defined for atom: ~p~n',[Atom]),fail.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% complete the abstract program with the definitions of the basic functions (cdr, consp, etc.) that are referenced

compute_undefined_predicates(Eqs,Undefined):-
	foldl(get_defined,Eqs,[],Defined),
	foldl(get_called,Eqs,[],Called),
	difference_sl(Called,Defined,Undefined).

get_defined(eq(Head,_Cost,_Calls,_Cs),Defined,Defined1):-!,
	functor(Head,F,A),
	insert_sl(Defined,F/A,Defined1).
get_defined(_,Defined,Defined).

get_called(eq(_Head,_Cost,Calls,_Cs),Called,Called1):-!,
	foldl(get_called_aux,Calls,Called,Called1).
get_called(_,Called,Called).

get_called_aux(Call,Called,Called1):-
	functor(Call,F,A),
	insert_sl(Called,F/A,Called1).
	
	
load_basic_lisp(Crs):-
	findall(X,(eq(Head,Cost,Calls,Cs),X=eq(Head,Cost,Calls,Cs)),Crs).



print_basic_lisp(Basic_lisp_crs,Used):-
	print_basic_lisp_aux(Basic_lisp_crs,Used,Used).

print_basic_lisp_aux([],_Used,Undefined):-
	(Undefined\=[]->
	format(user_error,'Undefined functions: ~q ~n',[Undefined])
	; 
	true).

print_basic_lisp_aux([Cr|Crs],Used,Undefined):-
	Cr=eq(Head,_,_,_),
	functor(Head,F,A),
	remove_sl(Undefined,F/A,Undefined1),
	(contains_sl(Used,F/A)->
	  print_cr(Cr)
	  ;
	  true),
	  print_basic_lisp_aux(Crs,Used,Undefined1).
	  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% auxiliary predicates

fix_quotes(Atom,Atom):-
	atom(Atom),!.
fix_quotes([],[]).
fix_quotes([X|Xs],[Ls1|Xss_fixed]):-
    X=='\'',
    Xs=[Ls|Xss],
    Ls1=['quote'|Ls],!,
    fix_quotes(Xss,Xss_fixed).	

fix_quotes([X|Xs],[X_fixed|Xs_fixed]):-
    fix_quotes(X,X_fixed),
    fix_quotes(Xs,Xs_fixed).	
	
print_cr(Cr):-
	copy_term(Cr,Crp),
	numbervars(Crp,0,_),
	format('~q.~n',[Crp]).
	
make_dicc(nil,[],[]).	
make_dicc([],[],[]).
make_dicc([Name|Names],[Var|Vars],Map1):-
	make_dicc(Names,Vars,Map),
	insert_lm(Map,Name,Var,Map1).

get_if_name(If_name):-
	counter_increase(if_cnt,1,Id),
	atom_concat('if_',Id,If_name).
get_args(Dicc,Args):-
	maplist(tuple,Dicc,_,Args).
tuple((A,B),A,B).
