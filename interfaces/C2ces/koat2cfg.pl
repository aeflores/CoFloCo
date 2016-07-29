#!/usr/bin/prolog



:-nb_setval(compiled,true).
:-set_prolog_flag(verbose, silent). 
:-initialization main_script.
:- use_module('src/koat2cfg_module',[main_koat2cfg/0]).

:-set_prolog_stack(global, limit(2*10**9)).


main_script :-
	koat2cfg_module:main_koat2cfg.
