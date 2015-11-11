#!/usr/bin/prolog

:-set_prolog_flag(verbose, silent). 
:-initialization main.

:-dynamic rule_exist/2.
:-dynamic tick_cost/0.

main:-
    current_prolog_flag(argv, Args),
	Args=[File|Rest],
	(Rest=['tick_cost'|_]->
 	    assert(tick_cost)
	;
	    true
	),
	catch(read_file(File),Fail,writeln(Fail)),
	halt.

main_bin:-
    current_prolog_flag(argv, [_|Args]),
    Args=[File|Rest],
	(Rest=['tick_cost'|_]->
 	    assert(tick_cost)
	;
	    true
	),
	catch(read_file(File),Fail,writeln(Fail)),
	halt.

save_exec:-
	make,
	check,
	prolog_history(disable),
	qsave_program('koat2ces',[stand_alone(true),goal(main_bin),foreign(save)]),
	writeln('Binary package generated').

read_file(File) :-
   phrase_from_file(parse_koat(cfg(Rules)), File),
   maplist(save_defined_rule,Rules),
   maplist(filter_undefined_rule,Rules,Rules2),
   atom_concat(File,'.cfg',New_file),
   open(New_file,write,Fd),
   pretty_print_rules(cfg(Rules2),Fd),
   close(Fd),!.

read_file(File) :-
	format('Failed translating: ~p~n',[File]).


save_defined_rule(e(Origin,_,_,_)):-
	functor(Origin,Name,Arity),
	(rule_exist(Name,Arity)->
	    true
	;
	   assert(rule_exist(Name,Arity))
	).

filter_undefined_rule(e(Origin,[D1,D2],_,Cons),e(Origin,DRest,Cost,Cons)):-
	tick_cost,
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

pretty_print_rules(cfg(Rules),Fd):-
       format(Fd,'cfg( [~n',[]),
       print_rules(Rules,Fd),
       format(Fd,']).~n',[]).

print_rules([Rule,R2|Rules],Fd):-
       format(Fd,'~p,~n',[Rule]),
       print_rules([R2|Rules],Fd).

print_rules([Rule],Fd):-
       format(Fd,'~p~n',[Rule]).
   
parse_koat(cfg(Rules)) -->
   header,spaces,
   start_term,spaces,
   vars,spaces,"(RULES",
   rules(Rules),spaces,")",spaces.

header --> 
    "(GOAL COMPLEXITY)".
start_term -->
	"(STARTTERM CONSTRUCTOR-BASED)".
start_term -->
	"(STARTTERM (FUNCTIONSYMBOLS",spaces,entry_name(_Entry),"))".

vars -->"(VAR ",var_names(_Names),")".
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

rule(e(Origin,Dest,0,Cons))-->{tick_cost},
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
	maybe_more_factors(Next_fact,Factor).
maybe_more_factors(Next_fact,Factor)-->"*",!,
	                   factors(Next_fact,Factor).
maybe_more_factors(Factor,Factor)-->[].

factor(Num)-->number_exp(Num).
factor(Factor)-->var_instance(Var),maybe_exp(Var,Factor).

maybe_exp(Var,Factor)-->"^",!,number_exp(Num),{repeat_n_times(Num,Var,Factor)}.
maybe_exp(Var,Var)-->[].


repeat_n_times('2',Var,Var*Var).

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

