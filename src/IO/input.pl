/** <module> input

This module reads cost equations and stores them in the database after normalizing them

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


:- module(input,[read_cost_equations/1,store_cost_equations/1]).
:- use_module('../db',[input_eq/5,
					entry_eq/2,reset_scc/1,
					cofloco_aux_entry_name/1,
					add_ground_equation_header/2]).
:- use_module('../utils/cofloco_utils',[normalize_constraint/2]).
:- use_module('../utils/cost_expressions',[is_linear_exp/1,parse_cost_expression/2]).
:- use_module('../utils/polyhedra_optimizations',[slice_relevant_constraints/4]).
:- use_module(stdlib(counters),[counter_increase/3]).
:- use_module(stdlib(utils),[ut_var_member_chk/2]).
:- use_module(stdlib(set_list),[from_list_sl/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_normalize/2]).

%! read_cost_equations(+File:filename) is det
%  read a set of cost equations from a file and call store_cost_equations/1.
read_cost_equations(File) :-
	read_crs(File,Eqs),
	store_cost_equations(Eqs).

%! store_cost_equations(+Eqs:list(cost_equation/(cost_equation,var_binding))) is det
%  * store the given equations in the database
%  * declare the first one as the main entry
%  * remove the calls to equations that are not defined (and show a warning)	
store_cost_equations(Eqs):-
	maplist(add_equation,Eqs),
	declare_entry,
	remove_undefined_calls.

%! declare_entry is det
% If there are entries, the auxiliary entry (cofloco_aux_entry_name) makes a call to each of them
% otherwise, the first cost equation becomes the entry
declare_entry:-
	findall(Entry,
	   entry_eq(Entry,_)
	   ,Entries),
	   Entries=[_|_],!,
	cofloco_aux_entry_name(Aux_Entry),
	normalize_input_equation(eq(Aux_Entry,0,Entries,[]),eq(Aux_Entry_Normalized,Expr_Normalized,Calls_Normalized,Cs_Normalized)),
	asserta(input_eq(Aux_Entry_Normalized,0,Expr_Normalized,Calls_Normalized,Cs_Normalized)).
declare_entry:-
	input_eq(Call,_,_,_,_),
	cofloco_aux_entry_name(Aux_Entry),
	normalize_input_equation(eq(Aux_Entry,0,[Call],[]),eq(Aux_Entry_Normalized,Expr_Normalized,[Call_Normalized],Cs_Normalized)),
	asserta(input_eq(Aux_Entry_Normalized,0,Expr_Normalized,[Call_Normalized],Cs_Normalized)),
	assertz(entry_eq(Call,[])).
	


%! read_crs(+File:filename,-EQs:list(cost_equation/(entry,variable_bindings))) is det
% read from the file Filename and returns a list of cost equations

read_crs(File,EQs) :-
	atom(File),
	!,
	open(File,read,S),
	read_crs_from_file(S,EQs),
	close(S).

read_crs(CRs,_EQs) :-
	throw(err(unknown_crs_format,read_crs/2,[crs=CRs])).


read_crs_from_file(S,EQs) :-
	catch(read_term(S,Term,[variable_names(Bindings)]),_,fail),
	( 
	  Term == end_of_file -> 
	    EQs = []
	;
	    EQs = [(Term,Bindings)|EQs_aux],
	    read_crs_from_file(S,EQs_aux)
	).

%! add_equation(+Cost_equation:cost_equation) is det
% @throws failed_to_add_equation 
% normalize the cost equation and add it to the database
add_equation((Eq,Var_binding)):-!,
   get_eq_head(Eq,Header),
   get_ground_term(Header,Var_binding,Ground_header),
   add_ground_equation_header(Header,Ground_header),
   add_equation(Eq).

	
add_equation(eq(Name,Vars,Exp,Body_Calls,Size_Rel)) :-!,
     Head=..[Name|Vars],
     add_equation(eq(Head,Exp,Body_Calls,Size_Rel)).
     

add_equation(eq(Head,Exp,Body_Calls,Size_Rel)) :-!,
	normalize_input_equation(eq(Head,Exp,Body_Calls,Size_Rel), eq(NHead,NExp,NCalls,NSize_Rel)), % Normalize the equation
	term_variables((NHead,NExp,NCalls),Relevant_Vars),
	%remove constraints that do not affect anything
	from_list_sl(Relevant_Vars,Relevant_Vars_set),
	from_list_sl(NSize_Rel,NSize_Rel_set),
	slice_relevant_constraints(Relevant_Vars_set,NSize_Rel_set,_,NSize_Rel_filtered),
	%check the equation doesn't exist yet
	((input_eq(NHead,_,NExp1,NCalls,NSize_Rel1),
	  NSize_Rel1==NSize_Rel_filtered,
	  NExp1==NExp
	)->
	 true
	;
	counter_increase(input_eqs,1,Id),% get new id
	assertz(input_eq(NHead,Id,NExp,NCalls,NSize_Rel_filtered))
	),			% add the equation to db
	!.
	
	
add_equation(entry(Term:Size_Rel)):-!,
	  normalize_entry(entry(Term:Size_Rel), Entry_Normalized),
	  assertz(Entry_Normalized).

add_equation(reset_scc(Head)):-!,
	  assertz(reset_scc(Head)).	  

% throw an exception on failure
add_equation(Eq) :-
	throw(cofloco_err(failed_to_add_equation,add_equation/1,[eq=Eq])).

%! get_eq_head(+Eq:cost_equation,-Head:term) is det
% get the head of the different types of input cost equations
get_eq_head(entry(Head:_),Head).
get_eq_head(reset_scc(Head),Head).
get_eq_head(eq(Name,Vars,_Exp,_Body_Calls,_Size_Rel),Head) :-	
     Head=..[Name|Vars].
get_eq_head(eq(Head,_Exp,_Body_Calls,_Size_Rel),Head).

%! get_ground_term(+Term:term,+Bindings:list(atom=var),-Ground_term:term) is det
% apply the bindings of Bindings to Term
get_ground_term(Term,Bindings,Ground_term):-
	copy_term((Term,Bindings),(Ground_term,Bindings2)),
	maplist(unify_eq,Bindings2).
	
unify_eq(X=X).



%! remove_undefined_calls is det
% remove the calls to equations that are not defined (and show a warning)
remove_undefined_calls :-
	retract(input_eq(Head,Id,Exp,Calls,Cs)),
	remove_undefined_calls_1(Calls,Head,Calls_1),
	assertz(input_eq(Head,Id,Exp,Calls_1,Cs)),
	fail.
remove_undefined_calls.

remove_undefined_calls_1([],_Head,[]).
remove_undefined_calls_1([C|Cs],Head,Cs_1) :-
	\+ input_eq(C,_,_,_,_), \+ C=Head,
	!,
	functor(C,Cname,C_arity),functor(Head,Headname,Head_arity),
	format('warning: Ignored call to ~p in equation ~p ~n',[Cname/C_arity,Headname/Head_arity]),
	remove_undefined_calls_1(Cs,Head,Cs_1).
remove_undefined_calls_1([C|Cs],Head,[C|Cs_1]) :-
	remove_undefined_calls_1(Cs,Head,Cs_1).
	
	
	
	
normalize_input_equation(EQ,EQ_Normalized) :-
    EQ = eq(Head,Cost_Expr,Body,Cs),
	normalize_atoms([Head|Body],[],[Head_Normalized|Body_Normalized],Cs_aux-Cs),
    maplist(transform_strict_inequality,Cs_aux,Cs_aux2),
    partition(is_linear_constr,Cs_aux2,Cs_aux_filtered,Cs_excluded),
    (Cs_excluded\=[]->
       copy_term((EQ,Cs_excluded),(EQ_print,Cs_excluded_print)),
       numbervars((EQ_print,Cs_excluded_print),0,_),
       format('WARNING: Excluded non-linear constraints:~p~n',[Cs_excluded_print])
       ;
       true
       ),
        nad_normalize(Cs_aux_filtered,Cs_aux_Normalized),
	parse_cost_expression(Cost_Expr,Expr_Normalized), %% replace by simplification
	EQ_Normalized = eq(Head_Normalized,Expr_Normalized,Body_Normalized,Cs_aux_Normalized).

normalize_entry(entry(Call:Cs), Entry_Normalized) :-
	normalize_atom(Call,[],Call_Normalized,_,Cs_aux-Cs),
    maplist(transform_strict_inequality,Cs_aux,Cs_aux2),
	Entry_Normalized = entry_eq(Call_Normalized,Cs_aux2).

transform_strict_inequality(A > B,A >= B+1):-!.
transform_strict_inequality(A < B,A+1 =< B):-!.
transform_strict_inequality(C,C).

is_linear_constr(Constr):-
	Constr=..[Op,C,C1],
	member(Op,[=<,>=,=]),
	is_linear_exp(C),is_linear_exp(C1).


normalize_size_rel([],[]).
normalize_size_rel([C|Cs],[NC|NCs]) :-
	normalize_constraint(C,NC),
	normalize_size_rel(Cs,NCs).

%%
%%
normalize_atoms([], _, [], T-T).
normalize_atoms([C|Cs], Used_Vars, NCalls, H-T) :-
	normalize_atom(C, Used_Vars, NC, Used_Vars_aux, H-T1),
	NCalls = [NC|NCalls_aux],
	normalize_atoms(Cs, Used_Vars_aux, NCalls_aux, T1-T).


normalize_atom(Atom, Used_Vars, NAtom, New_Used_Vars, H-T) :-
	Atom =.. [F|Vs],
	normalize_atom_args(Vs, NVs, Used_Vars, New_Used_Vars, H-T),
	NAtom =.. [F|NVs].

normalize_atom_args([],     [],      Used_Vars, Used_Vars,         T-T).
normalize_atom_args([V|Vs], [V|NVs], Used_Vars, [V|New_Used_Vars], H-T) :-
	var(V),
	\+ ut_var_member_chk(V,Vs),
	\+ ut_var_member_chk(V,Used_Vars),
	!,
	normalize_atom_args(Vs, NVs, Used_Vars, New_Used_Vars, H-T).
normalize_atom_args([V|Vs], [NV|NVs], Used_Vars, [V|New_Used_Vars], [NV=V|H]-T) :-
	normalize_atom_args(Vs, NVs, Used_Vars, New_Used_Vars, H-T).
