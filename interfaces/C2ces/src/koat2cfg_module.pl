#!/usr/bin/prolog

:-module(koat2cfg_module,[main_koat2cfg/0,main_bin_koat2cfg/0]).

:-dynamic rule_exist/2.
:-dynamic option/1.

main_koat2cfg:-
	set_prolog_flag(print_write_options,[quoted(false),numbervars(true)]),
    current_prolog_flag(argv, Args),
	Args=[File|Rest],
	process_args(Rest),
	catch(read_file(File),Fail,writeln(Fail)),
	halt.

main_bin_koat2cfg:-
    current_prolog_flag(argv, [_|Args]),
    Args=[File|Rest],
	process_args(Rest),
	catch(read_file(File),Fail,writeln(Fail)),
	halt.

process_args([]).
process_args(['-o',File|Args]):-!,
	assert(option(to_file(File))),
	process_args(Args).
process_args([tick_cost|Args]):-!,
	assert(option(tick_cost)),
	process_args(Args).
		
process_args([X|_Args]):-!,
	throw(invalid_parameter(X)).	

save_exec:-
	make,
	check,
	prolog_history(disable),
	qsave_program('koat2ces',[stand_alone(true),goal(main_bin),foreign(save)]),
	writeln('Binary package generated').

read_file(File) :-
   (File=stdin->
   	    read_stream_to_codes(user_input,Content),
        phrase(parse_koat(cfg(Entry,Rules)), Content)
        ;
   		phrase_from_file(parse_koat(cfg(Entry,Rules)), File)
   	),
   maplist(save_defined_rule,Rules),
   maplist(filter_undefined_rule,Rules,Rules2),
   put_entry_rules_first(Rules2,Entry,Rules3),
   (option(to_file(New_file))->
   		tell(New_file),
		pretty_print_rules(cfg(Rules3)),
		told
	;
   		pretty_print_rules(cfg(Rules3))
   	),!.

read_file(File) :-
	format('Failed translating: ~p~n',[File]).

put_entry_rules_first(Rules,no_entry,Rules):-!.
put_entry_rules_first(Rules,Entry,Rules2):-
	partition(is_entry_rule(Entry),Rules,Entry_rules,Others),
	append(Entry_rules,Others,Rules2).

is_entry_rule(F,e(Term,_,_,_)):-
	functor(Term,F,_).
	
save_defined_rule(e(Origin,_,_,_)):-
	functor(Origin,Name,Arity),
	(rule_exist(Name,Arity)->
	    true
	;
	   assert(rule_exist(Name,Arity))
	).

filter_undefined_rule(e(Origin,[D1,D2],_,Cons),e(Origin,DRest,Cost,Cons)):-
	option(tick_cost),
	D1=eval_tick_start(Cost),
	include(defined_rule,[D1,D2],[DRest]),!.

filter_undefined_rule(e(Origin,[D1,D2],Cost,Cons),e(Origin,DRest,Cost,Cons)):-
	include(defined_rule,[D1,D2],[DRest]),!.

filter_undefined_rule(e(Origin,Dest,Cost,Cons),e(Origin,Dest,Cost,Cons)):-
	Dest\=[_|_],!.
filter_undefined_rule(e(Origin,Dest,Cost,Cons),_):-
	throw(invalid_rule(e(Origin,Dest,Cost,Cons))).

defined_rule(Rule):-
	functor(Rule,Name,Arity),
	rule_exist(Name,Arity).

pretty_print_rules(cfg(Rules)):-
       format('cfg( [~n',[]),
       print_rules(Rules),
       format(']).~n',[]).

print_rules([Rule,R2|Rules]):-
       format('~p,~n',[Rule]),
       print_rules([R2|Rules]).

print_rules([Rule]):-
       format('~p~n',[Rule]).
   
parse_koat(cfg(Entry,Rules)) -->
   header,spaces,
   start_term(Entry),spaces,
   vars,spaces,"(RULES",
   rules(Rules),spaces,")",spaces.

header --> 
    "(GOAL COMPLEXITY)".
start_term(no_entry) -->
	"(STARTTERM CONSTRUCTOR-BASED)".
start_term(Entry) -->
	"(STARTTERM (FUNCTIONSYMBOLS",spaces,entry_name(Entry),"))".

vars -->"(VAR",spaces,var_names(_Names),")".
var_names([Name|Names]) --> 
         var_name(Name),!,
         spaces,
         var_names(Names).
var_names([]) --> [].

rules([Rule|Rules])-->
    rule(Rule),!,
    spaces,
    rules(Rules).
rules([])-->[].

rule(e(Origin,Dest,0,Cons))-->{option(tick_cost)},
     spaces,
     location(Origin),
     spaces,
     "->",spaces,
     rule_second_part(Dest,Cons).
rule(e(Origin,Dest,1,Cons))-->spaces,
     location(Origin),
     spaces,
     "->",spaces,
     rule_second_part(Dest,Cons).

rule_second_part(Dest,Cons)-->
     "Com_1(",spaces,
     location(Dest),spaces,
     ")",spaces,
     maybe_constraints(Cons).

rule_second_part([Dest,Dest2],Cons)-->
     "Com_2(",spaces,
     location(Dest),spaces,",",spaces,
     location(Dest2),spaces,
     ")",spaces,
     maybe_constraints(Cons).

location(Loc) -->
     loc_name(Name),"(",maybe_var_names_comma(Vars),")",{Loc=..[Name|Vars]}.

maybe_var_names_comma(Vars)-->var_names_comma(Vars).
maybe_var_names_comma([])-->[].
var_names_comma([Name|Names]) --> 
         spaces,
	 side(none,Name),spaces,
	 maybe_more_names_comma(Names).

maybe_more_names_comma(Names)-->
	 ",",!,
         var_names_comma(Names).
maybe_more_names_comma([])-->[].

maybe_constraints(Cons)-->
     ":|:",!,spaces,
      constraints(Cons).
maybe_constraints([])-->[].

constraints([C|Cs])-->
          constraint(C),
	  maybe_more_constraints(Cs).

maybe_more_constraints(Cs)-->
	 "&&",!,
          constraints(Cs).
maybe_more_constraints([])-->[].


constraint(C)-->spaces,
         side(none,L),spaces,
         relational_op(Op),spaces,
         side(none,R),spaces,
	     {C=..[Op,L,R]}.
  


side(Prev_summand,Exp)-->factors(none,Factor),
       {combine_summand(Prev_summand,Factor,Next_summand)},
       maybe_more_side(Next_summand,Exp).

maybe_more_side(Next_summand,Exp)-->
	spaces,arith_op(Op1),!,
	spaces,side((Next_summand,Op1),Exp).
maybe_more_side(Exp,Exp)-->[].


factors(Prev_fac,Factor)-->factor(F1),{combine_factor(Prev_fac,F1,Next_fact)},
	spaces,
	maybe_more_factors(Next_fact,Factor).
maybe_more_factors(Next_fact,Factor)-->"*",!,spaces,
	                   factors(Next_fact,Factor).
maybe_more_factors(Factor,Factor)-->[].

factor(Num)-->number_exp(Num).
factor(Factor)-->var_instance(Var),maybe_exp(Var,Factor).

maybe_exp(Var,Factor)-->"^",!,number_exp(Num),{repeat_n_times(Num,Var,Factor)}.
maybe_exp(Var,Var)-->[].



repeat_n_times(Num_atom,Var,Factor):-
	atom_number(Num_atom,Num),
	repeat_n_times_1(Num,Var,Factor).
repeat_n_times_1(1,Var,Var):-!.
repeat_n_times_1(N,Var,Var*Factor):-
	N1 is N-1,
	repeat_n_times_1(N1,Var,Factor).

combine_factor(None,F1,F1):-None==none,!.
combine_factor(F1,F2,F_comb):-F_comb=..['*',F1,F2].

combine_summand(none,F1,F1):-!.
combine_summand((F1,Op),F2,F_comb):-F_comb=..[Op,F1,F2].


arith_op('+')-->"+".
arith_op('-')-->"-".

relational_op('=')-->"=".
relational_op('=<')-->"<=".
relational_op('>=')-->">=".
relational_op('>')-->">".
relational_op('<')-->"<".

non_ops([X|Xs])-->non_op(X),!,non_ops(Xs).
non_ops([])-->[].
side_1(Exp)-->non_ops_1(Chars),{ atom_codes(Exp, Chars) }.
non_ops_1([X|Xs])-->non_op_1(X),!,non_ops_1(Xs).
non_ops_1([])-->[].

read_op([X|Xs])-->yes_op(X),!,read_op(Xs).
read_op([])-->[].

non_op(X)-->[X],{atom_codes('&=><\n',Ops),\+member(X,Ops)}.
non_op_1(X)-->[X],{atom_codes('&=><,)',Ops),\+member(X,Ops)}.
yes_op(X)-->[X],{atom_codes('&=><',Ops),member(X,Ops)}.


transform_op(Op,"=<"):-atom_codes('<=',Op),!.
transform_op(Op,"+1 =<"):-atom_codes('<',Op),!.
transform_op(Op,">= 1+"):-atom_codes('>',Op),!.
transform_op(Op,Op).
 
spaces --> space,!,spaces.
spaces -->[],!.

space --> [X],{ char_type(X,space)}.
space --> [X],{ char_type(X,white)}.

new_line --> [10].

var_instance(Neg)-->"-",var_name(Name),{Neg=..[-,Name]}.
var_instance(Name)-->var_name(Name).

var_name(Name1) -->
      chars([X|CHARS]), {char_type(X,to_lower(Y)),
      atom_codes(Name, CHARS),
       atom_concat(Y,Name,Name1) }.

loc_name(Name) -->
      chars(CHARS), {atom_codes(Name, CHARS)}.

entry_name(Entry) -->
    chars(CHARS), { atom_codes(Entry, CHARS) }.

number_exp(Number1) -->"-",
      numbers(CHARS), { number_codes(Number,CHARS),
			Number1 is 0 - Number }.
number_exp(Number) -->
      numbers(CHARS), { atom_codes(Number, CHARS) }.

chars([X|Y]) --> char(X), chars(Y).
chars([X]) --> char(X).
char(X) --> [X], { char_type(X,csym) }.
char(X) --> [Y], {atom_codes('.',[Y]),atom_codes('_',[X])}.
char(X) --> [Y], {atom_codes('\'',[Y]),atom_codes('_',[X])}.

numbers([X|Y]) --> number(X), numbers(Y).
numbers([X]) --> number(X).
number(X) --> [X], { char_type(X,digit) }.

