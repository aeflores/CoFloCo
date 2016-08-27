#!/usr/bin/prolog



:-nb_setval(compiled,true).
:-set_prolog_flag(verbose, silent). 
:-initialization main_script.
:- use_module('src/cfg2ces_module',[main_cfg2ces/0]).

:-set_prolog_stack(global, limit(2*10**9)).


main_script :-
	cfg2ces_module:main_cfg2ces.
