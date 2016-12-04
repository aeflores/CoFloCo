/** <module> params

This module defines:

  * the set of allowed parameters with the predicate parameter_dictionary/3.  
  * the desciption of each parameter with param_description/2.    

The module also takes care of parsing the input parameters and storing them.  

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

:- module(params,[clean_params/0,
		  set_default_params/0,
		  set_competition_params/0,
		  parse_params/1,
		  get_param/2,
		  parameter_dictionary/3,
		  param_description/2]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
%% param(+Param:atom,-Values:list) is nondet
% @arg Param is the name of the parameter
% @arg values is a list of values associated to each parameter
:-dynamic param/2.



%% parameter_dictionary(?External_name:atom,?Internal_name:atom,-Values:list) is nondet
% @arg external_name is the name of the parameter that is read from the input
% @arg internal_name is a list of values associated to each parameter
% @arg values is a list that determines how many values a parameter has and how they have to be parsed (the type)
% some of the possible types are: bool (a yes or no), number (an integer), in_file (a file with read permission)

parameter_dictionary('-h','help',[]).% print help information
parameter_dictionary('-help','help',[]).

parameter_dictionary('-input','input',[in_file]). %select abs source
parameter_dictionary('-i','input',[in_file]).

%out information
parameter_dictionary('-stats','stats',[]). 
parameter_dictionary('-s','stats',[]).

parameter_dictionary('-v','v',[number]).
parameter_dictionary('-verbosity','v',[number]).
parameter_dictionary('-debug','debug',[bool]).
parameter_dictionary('-no_warnings','no_warnings',[]).

parameter_dictionary('-competition','competition',[bool]).
parameter_dictionary('-assume_sequential','assume_sequential',[bool]).
parameter_dictionary('-n_candidates','n_candidates',[number]).

parameter_dictionary('-solve_fast','solve_fast',[bool]).

parameter_dictionary('-compress_chains','compress_chains',[number]).

parameter_dictionary('-only_termination','only_termination',[bool]).

parameter_dictionary('-compute_ubs','compute_ubs',[bool]).
parameter_dictionary('-compute_lbs','compute_lbs',[bool]).
parameter_dictionary('-conditional_ubs','conditional_ubs',[bool]).
parameter_dictionary('-conditional_lbs','conditional_lbs',[bool]).

parameter_dictionary('-incremental','incremental',[bool]).
parameter_dictionary('-context_sensitive','context_sensitive',[number]).

:-dynamic incompatible_parameters/2.

%% clean_params is det
% erase all the stored parameters
clean_params:-
	retractall(param(_,_)).

%% set_default_params is det
% store the default parameters:
%  * -v 2
%  * -n_rankings 2
%  * -maximize_fast 5
set_default_params:-
	parse_params(['-v','2',
		      '-n_candidates','1',
		      '-context_sensitive','1',
		      '-compute_ubs',
		      '-compute_lbs'
		      ]).

set_competition_params:-
		parse_params([
%			  '-v','3',
		      '-n_candidates','1',
		      '-context_sensitive','1',
		      '-compute_ubs',
		      '-compute_lbs','no',
		      '-solve_fast',
		      '-compress_chains','2'
		      ]).	      
%% parse_params(Params:list(atoms)) is det
%  parse a given list of Params and store the parsed values so they can be accesed form any part of the code
parse_params([]):-!.
parse_params([Param|Rest]):-
	parameter_dictionary(Param,Internal_repr,ArgsOpts),!,
	process_args(ArgsOpts,Rest,Args,New_rest),
	(Args==[no]->
	  retractall(param(Internal_repr,[]))
	  ;
	(Args==[yes]->
	 add_param(Internal_repr,[])
	;
	add_param(Internal_repr,Args)
	)
	),
	parse_params(New_rest).
parse_params([Bad_param|_Rest]):-
	throw(illegal_argument(Bad_param)).

% one of [bool,no,yes,number,out_file,in_file]
process_args([],Rest,[],Rest).

process_args([bool|More],[Value|Vs],[Processed_value|Pvs],Rest):-
	atom_to_term(Value,Processed_value,_),
	member(Processed_value,[yes,no]),!,
	process_args(More,Vs,Pvs,Rest).
process_args([bool|More],Vs,[yes|Pvs],Rest):-
	process_args(More,Vs,Pvs,Rest).
	
process_args([atom|More],[Value|Vs],[Processed_value|Pvs],Rest):-
	atom_to_term(Value,Processed_value,_),!,
	process_args(More,Vs,Pvs,Rest).

process_args([number|More],[Value|Vs],[Processed_value|Pvs],Rest):-

	atom_to_term(Value,Processed_value,_),
    number(Processed_value),
	
	!,
	process_args(More,Vs,Pvs,Rest).

process_args([in_file|More],[Value|Vs],[Value|Pvs],Rest):-
	access_file(Value,read),!,
	process_args(More,Vs,Pvs,Rest).
process_args([out_file|More],[Value|Vs],[Value|Pvs],Rest):-
	access_file(Value,write),!,
	process_args(More,Vs,Pvs,Rest).


process_args([no|More],[Value|Vs],[Value|Pvs],Rest):-
	process_args(More,Vs,Pvs,Rest).

process_args([Type|_More],[Value|_Vs],_,_):-
	error_message(Type,Value,Message),
	throw(illegal_argument_value(Message)).

error_message(yes,Value,Message):-
	atom_concat('Illegal argument:',Value,Message).
error_message(in_file,Value,Message):-
	atom_concat('Illegal argument, could not read file:',Value,Message).
error_message(out_file,Value,Message):-
	atom_concat('Illegal argument, cannot write file:',Value,Message).

error_message(number,Value,Message):-
	atom_concat('Illegal argument, not a number:',Value,Message).

add_param(Key,_Value):-
	retract(param(Key,_)),
	fail.
add_param(Key,Value):-
	check_param_incompatibility(param(Key,Value),param(Key2,Value2)),!,
	throw(incompatible_arguments((Key,Value),(Key2,Value2))).

add_param(Key,Value):-
	assert(param(Key,Value)).	

check_param_incompatibility(Param,param(Key,Val)):-
	incompatible_parameters(Param,param(Key,Val)),
	get_param(Key,Val).
check_param_incompatibility(Param,param(Key,Val)):-
	incompatible_parameters(param(Key,Val),Param),
	get_param(Key,Val).
%% get_param(+Param:atom,-Values:list(values)) is nondet
% consult the stored values of the parameter Param
get_param(Param,Values):-
	param(Param,Values).
	
%% param_description(+Internal_name:atom,-Description:string) is det
%  provides a description of each parameter so it can be printed in the help

param_description('help',':Display help information').
param_description('input','filename: Selects input program.').
param_description('stats','Show some basic statistics').
param_description('debug','Show debug information').
param_description('v','0-3 : selects the level of verbosity ').
param_description('no_warnings','Do not print any warnings').
param_description('competition','Set output and settings for complexity competition').
param_description('n_candidates',' nat : (default 1) Sets the maximum number of candidates considered for a strategy').
param_description('context_sensitive',' nat : (default 1) How context sensitive the bound computation is
 1. Each phase is solved only once with invariants valid for all its appearances in different chains
 2. Each phase is solved individually for each chain taking the specific invariants of that chain into account').

param_description('assume_sequential',
'Assume that the calls performed in a cost equation are done sequentially
It is important for non-terminating programs').
param_description('compute_ubs',
'Obtain closed-form upper bounds').
param_description('compute_lbs',
'Obtain closed-form lower bounds (If disabled, additional simplifications can be made on cost structures)').
param_description('conditional_ubs',
'Generate a set of conditional upper bounds (whose preconditions are mutually exclusive) instead of a single unconditional one').
param_description('conditional_lbs',
'Generate a set of conditional lower bounds (whose preconditions are mutually exclusive) instead of a single unconditional one').

param_description('compress_chains',
'0-2 : (default 0) Join chains that have the same precondition. It can increase performance greatly but also affect precission').