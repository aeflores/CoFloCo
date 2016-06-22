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
	  parse_lisp(File,S_expressions),!,
	  counter_initialize(if_cnt,0),
	  counter_initialize(atom_cnt,2),
	  maplist(defun2cost_exp,S_expressions,All_cost_relations), 
	  load_basic_lisp(Basic_lisp_crs),
	  ut_flat_list([Basic_lisp_crs,All_cost_relations],Total_crs),
	  compute_undefined_predicates(Total_crs,Selected_crs,Undefined_predicates),
	  % print the crs
	  maplist(print_cr([singletons]),Selected_crs),
	  format(user_error,'Undefined functions: ~q ~n',[Undefined_predicates])
	  ),Fail,writeln(Fail)),
	halt.




nat_constraints(Args,Constrs):-nat_constrs(Args,Constrs,0),!.

nat_constrs([],[],_).
nat_constrs([Arg|Args],Constrs,N):-
	(N rem 3) > 0,
	var(Arg),
	nat_constrs(Args,Constrs_next,N+1),
	Constrs=[Arg>=0|Constrs_next],!.
nat_constrs([_|Args],Constrs,N):-
	nat_constrs(Args,Constrs,N+1),!.


related_call_constrs([],[]).
related_call_constrs(['car'(_,Al,As,_,_,Bs1)|Calls],Constrs):-
	member('cdr'(_,Al2,As2,_,_,Bs2),Calls),
	Al==Al2,As==As2,
	related_call_constrs(Calls,Constrs_next),
	Constrs = [Bs1+Bs2+1=As|Constrs_next].
related_call_constrs(['cdr'(_,Al,As,_,_,Bs1)|Calls],Constrs):-
	member('car'(_,Al2,As2,_,_,Bs2),Calls),
	Al==Al2,As==As2,
	related_call_constrs(Calls,Constrs_next),
	Constrs = [Bs1+Bs2+1=As|Constrs_next].
related_call_constrs([_|Calls],Constrs):-
	related_call_constrs(Calls,Constrs).


% main transformation predicate
% take a function definition and generate a list of cost relations (and print them)	
defun2cost_exp(['defun-simplified','state-fix'|_],[]):-!,
	format(user_error,'For now, we ignore state-fix function~n',[]).


defun2cost_exp(['defun-simplified',Name,nil,Body_with_quotes],All_cost_relations):-
	defun2cost_exp(['defun-simplified',Name,[],Body_with_quotes],All_cost_relations).
defun2cost_exp(['defun-simplified',Name,Args,Body_with_quotes],All_cost_relations):-
	fix_quotes(Body_with_quotes,Body),
	expand_args(Args,Converted_args),
	% create map from variable names to prolog variables
	make_dicc(Converted_args,Args_abstract,Dicc),
	% obtain a set of calls from the body (and possibly cost relations defined inside)
	unroll_body(Dicc,Body,Body_unrolled,Res_vars,Cost_relations),
	append(Args_abstract,Res_vars,All_args),
	Head=..[Name|All_args],
	% the main cost relation
	nat_constraints(All_args,Nat_constrs),
	related_call_constrs(Body_unrolled,Rel_call_constrs),
	append(Nat_constrs,Rel_call_constrs,All_constrs),
	Cost_relation= eq(Head,1,Body_unrolled,All_constrs),
	% we want closed-form bound for this cost relation
	ut_flat_list([Cost_relation|Cost_relations],All_cost_relations),!.
	

defun2cost_exp(['defined-locally',Name,NArgs],[Entry]):-
	atom_number(NArgs,Nargs_number),
	NArgs1 is (Nargs_number+1)*3,
	length(Args,NArgs1),
	Head=..[Name|Args],
	Entry= entry(Head:[]),
	print_cr([],Entry),!.
	
defun2cost_exp(Other,_):-
	format(user_error,'Failed translating S-expression: ~p~n',[Other]),
	throw(error('Failed translating S-expression',Other)).

% unroll_body process a body and extracts a set of calls that define its behavior
% it also generate a set of cost relations that are defined inside the body (in particular, 'if' cost relations)

% a variable
unroll_body(Dicc,Var_name,[],Var,[]):-
	atom(Var_name),
	expand_args([Var_name],Conv_var_names),
	lookup_list_lm(Dicc,Conv_var_names,Var),
	!.

%a string
unroll_body(_Dicc,string(X),[],[_,Size,Size],[]):-
	length(X,Size),!.
% an atom	
unroll_body(_Dicc,Quoted_atom,[],Sizes,[]):-
	atom(Quoted_atom),
	atom_concat('\'',Atom,Quoted_atom),!,
	size_atom(Atom,Sizes).
	
unroll_body(_Dicc,Atom,[],Sizes,[]):-
	atom(Atom),!,
	size_atom(Atom,Sizes).
	
unroll_body(_Dicc,[quote,S_expression],[],Size,[]):-!,
	size_s_expression(S_expression,Size).


% if expression
unroll_body(Dicc,[if,Cond,Cond_yes,Cond_no],Body_unrolled,[Res_var_i,Res_var_l,Res_var_s],Cost_relations):-!,
	%get a fresh name
	get_if_name(If_name),
	% get the calls in the condition, the 'then' branch and the 'else' branch
	unroll_body(Dicc,Cond,Cond_calls,[Cond_bool,_,_],Cost_relations_cond),
	unroll_body(Dicc,Cond_yes,Yes_calls,Res_vars_yes,Cost_relations_yes),
	unroll_body(Dicc,Cond_no,No_calls,Res_vars_no,Cost_relations_no),
	%we generate two cost relations:
	% when the condition is true and when it is not
	append(Cond_calls,Yes_calls,Yes_calls_all),
	append(Cond_calls,No_calls,No_calls_all),
	get_args(Dicc,Args),
	append(Args,Res_vars_yes,All_args_yes),Head_if_yes=..[If_name|All_args_yes],
	append(Args,Res_vars_no,All_args_no),Head_if_no=..[If_name|All_args_no],
	Res_vars=[Res_var_i,Res_var_l,Res_var_s],
	append(Args,Res_vars,All_args),
	Head_if=..[If_name|All_args],
	nat_constraints(All_args_yes,Nat_constrs_yes),
	nat_constraints(All_args_no,Nat_constrs_no),
	related_call_constrs(Yes_calls_all,Rel_call_constrs_yes),
	related_call_constrs(No_calls_all,Rel_call_constrs_no),
	append(Rel_call_constrs_yes,Nat_constrs_yes,Constrs_yes),
	append(Rel_call_constrs_no,Nat_constrs_no,Constrs_no),
	Cost_relation_yes=eq(Head_if_yes,1,Yes_calls_all,[Cond_bool=1|Constrs_yes]),
	Cost_relation_no=eq(Head_if_no,1,No_calls_all,[Cond_bool=0|Constrs_no]),
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
unroll_body(Dicc,[[lambda,New_vars,Exp]| Def_exps],Body_unrolled,Res_vars,Cost_relations):-!,
  %  (New_vars=nil-> New_vars1=[]; New_vars1=New_vars),
	couple_definitions(New_vars,Def_exps,Defs),
	unroll_definitions(Defs,Dicc,Dicc1,Calls_defs,Cost_relations1),
	unroll_body(Dicc1,Exp,Calls_exp,Res_vars,Cost_relations2),
	append(Calls_defs,Calls_exp,Body_unrolled),
	append(Cost_relations1,Cost_relations2,Cost_relations).	
	

% coerce is type casting, for now we ignore it	
unroll_body(Dicc,[coerce,Exp,_Type],Body_unrolled,Res_vars,Cost_relations):-!,
	unroll_body(Dicc,Exp,Body_unrolled,Res_vars,Cost_relations).


%generic function call	
unroll_body(Dicc,[Function|Args],Body_unrolled,[Res_var_out_i,Res_var_out_l,Res_var_out_s],Cost_relations):-
	atom(Function),
	maplist(unroll_body(Dicc),Args,Calls,Res_vars,Cost_relations),
	ut_flat_list(Res_vars,Res_vars_flattened),
	Res_vars_out = [Res_var_out_i,Res_var_out_l,Res_var_out_s],
	append(Res_vars_flattened,Res_vars_out,All_args),
	Top_call=..[Function|All_args],
	ut_flat_list([Calls,Top_call],Body_unrolled),!.

%something else
unroll_body(_Dicc,Expr,_Body_unrolled,_Res_var,_Cost_relations):-
	format(user_error,'Unknown Function format: ~p~n',[Expr]),!,fail.

expand_args([],[]).
expand_args([Arg|Args],Converted_args):-!,
	expand_arg(Arg,['_i','_l','_s'],Converted_arg_lst),
	expand_args(Args,Converted_arg_lsts),
	append(Converted_arg_lst,Converted_arg_lsts,Converted_args).

expand_arg(_Arg,[],[]).
expand_arg(Arg,[App|Apps],Arg_convs):-!,
	atom_concat(Arg,App,AX),
	expand_arg(Arg,Apps,Arg_convs_next),
	Arg_convs=[AX|Arg_convs_next].


lookup_list_lm(_Dicc,[],[]).
lookup_list_lm(Dicc,[Key|Keys],[Val|Vals]):-
	lookup_lm(Dicc,Key,Val),
	lookup_list_lm(Dicc,Keys,Vals).

insert_list_lm(Dicc,[],[],Dicc).
insert_list_lm(Dicc,[Key|Keys],[Val|Vals],Dicc_new):-
	insert_lm(Dicc,Key,Val,Dicc_new1),
	insert_list_lm(Dicc_new1,Keys,Vals,Dicc_new).


% predicates to deal witht the lambda expressions and let

couple_definitions(Vars,Exps,Defs):-
	maplist(couple_definition,Vars,Exps,Defs),!.
couple_definitions(Vars,Exps,_Defs):-
	length(Vars,N1),
	length(Exps,N2),
	format(user_error,'Failed coupling variables: ~n~p and its definitions ~n~p in lambda expression. Different number ~p ~p~n',[Vars,Exps,N1,N2]),!,fail.
couple_definition(Var,Exp,[Var, Exp]).

% update the variable map
unroll_definitions([],Dicc,Dicc,[],[]).
unroll_definitions([[Var_name,Exp]|Defs],Dicc,Dicc_final,Calls,Cost_relations):-
	unroll_body(Dicc,Exp,Calls_exp,Res_vars,Cost_relations_exp),!,
	expand_args([Var_name],Var_names),
	insert_list_lm(Dicc,Var_names,Res_vars,Dicc1),
	unroll_definitions(Defs,Dicc1,Dicc_final,Calls_aux,Cost_relations_aux),
	append(Calls_exp,Calls_aux,Calls),
	append(Cost_relations_exp,Cost_relations_aux,Cost_relations).

unroll_definitions([[_Var_name,Exp]|_Defs],_Dicc,_Dicc_final,_Calls,_Cost_relations):-
	format(user_error,'Failed definition unrolling: ~p~n',[Exp]),!,fail.

	
size_atom(nil,[0,0,0]):-!.
size_atom(t,[1,0,0]):-!.
size_atom(Atom,[Int,_,_]):-
	atom_number(Atom,Int),!.
size_atom(String,[_,Length,Length]):-
	atom_codes(String,[DoubleQuote|Codes]),
	atom_codes('"',[DoubleQuote]),!,
	length(Codes,N),
	Length is N-1.

size_atom(Atom,[Atom_i,Atom_l,Atom_s]):-
	atom_size(Atom,[Atom_i,Atom_l,Atom_s]),!.
size_atom(Atom,[Size,Size,Size]):-
	counter_increase(atom_cnt,1,Size),
	assert(atom_size(Atom,[Size,Size,Size])),!.
	
size_atom(Atom,_Length):-
	format(user_error,'No size defined for atom: ~p~n',[Atom]),fail.

size_s_expression([],[_,0,0]):-!.
size_s_expression([X|Xs],[_,Length,Size]):-!,
	size_s_expression(X,[_,_L1,S1]),
	size_s_expression(Xs,[_,L2,S2]),
	Length is 1+L2,
	Size is S1+S2+1. % this is a cons, so +1
size_s_expression(_,[0,0,0]). %FIXME

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% complete the abstract program with the definitions of the basic functions (cdr, consp, etc.) that are referenced

compute_undefined_predicates(Terms,Crs_selected,Undefined):-
	partition(is_entry,Terms,Entries,Crs),
	foldl(init_called,Entries,[],Called_ini),
	compute_called(Crs,Called_ini,Called),
	foldl(get_defined,Crs,[],Defined),
	include(is_called(Called),Crs,Crs_selected),
	difference_sl(Called,Defined,Undefined).

get_defined(eq(Head,_Cost,_Calls,_Cs),Defined,Defined1):-!,
	functor(Head,F,A),
	insert_sl(Defined,F/A,Defined1).
get_defined(_,Defined,Defined).


is_entry(entry(_)).
is_called(Called,eq(Head,_,_,_)):-
	functor(Head,F,A),
	contains_sl(Called,F/A).

init_called(entry(Head:_),Called,Called1):-
	functor(Head,F,A),
	insert_sl(Called,F/A,Called1).
	
compute_called(Eqs,Called,Called1):-
	foldl(get_called_new,Eqs,Called,Called_aux),
	length(Called,N),
	length(Called_aux,N1),
	(N1 >N ->
	  compute_called(Eqs,Called_aux,Called1)
	  ;
	  Called1=Called_aux).

get_called_new(eq(Head,_Cost,Calls,_Cs),Called,Called1):-
	functor(Head,F,A),
	contains_sl(Called,F/A),!,
	foldl(get_called_aux,Calls,Called,Called1).
get_called_new(_,Called,Called).

get_called_aux(Call,Called,Called1):-
	functor(Call,F,A),
	insert_sl(Called,F/A,Called1).
	
	
load_basic_lisp(Crs):-
	findall(X,(eq(Head,Cost,Calls,Cs),X=eq(Head,Cost,Calls,Cs)),Crs).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% auxiliary predicates

fix_quotes(Atom,Atom):-
	atom(Atom),!.
fix_quotes(string(X),string(X)):-!.

fix_quotes([],[]).
fix_quotes([X|Xs],[[quote,Ls]|Xss_fixed]):-
    X=='\'',!,
    Xs=[Ls|Xss],
    fix_quotes(Xss,Xss_fixed).	
 
 fix_quotes([X|Xs],[['\\',Ls]|Xss_fixed]):-
    X=='\\',!,
    Xs=[Ls|Xss],
    fix_quotes(Xss,Xss_fixed).	  

fix_quotes([X|Xs],[X_fixed|Xs_fixed]):-
    fix_quotes(X,X_fixed),
    fix_quotes(Xs,Xs_fixed).	
	
print_cr(Opts,Cr):-
	copy_term(Cr,Crp),
	numbervars(Crp,0,_,Opts),
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
