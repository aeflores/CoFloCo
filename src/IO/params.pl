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
		  parse_params/1,
		  get_param/2,
		  parameter_dictionary/3,
		  param_description/2]).

:- use_module(stdlib(utils),[ut_number_to_atom/2]).

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

parameter_dictionary('-assume_sequential','assume_sequential',[bool]).
parameter_dictionary('-n_rankings','n_rankings',[number]).

parameter_dictionary('-maximize_fast','maximize_fast',[number]).

parameter_dictionary('-no_compression','no_compression',[bool]).%TODO

parameter_dictionary('-only_termination','only_termination',[bool]).
parameter_dictionary('-prolog_format','prolog_format',[bool]).

parameter_dictionary('-conditional_ubs','conditional_ubs',[]).
%% clean_params is det
% erase all the stored parameters
clean_params:-
	retractall(param(_,_)).

%% set_default_params is det
% store the default parameters:
%  * -v 2
%  * -n_rankings 2
%  * -solve_fast 4
%  * -maximize_fast 2
set_default_params:-
	parse_params(['-v',2,
		      '-n_rankings',2,
		      '-maximize_fast',5
		      ]).
		      
%% parse_params(Params:list(atoms)) is det
%  parse a given list of Params and store the parsed values so they can be accesed form any part of the code
parse_params([]):-!.
parse_params([Param|Rest]):-
	parameter_dictionary(Param,Internal_repr,ArgsOpts),!,
	process_args(ArgsOpts,Rest,Args,New_rest),
	(Args==[no]->
	  true;
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
	term_to_atom(Processed_value,Value),
	member(Processed_value,[yes,no]),!,
	process_args(More,Vs,Pvs,Rest).
process_args([bool|More],Vs,[yes|Pvs],Rest):-
	process_args(More,Vs,Pvs,Rest).
	
process_args([yes|More],[Value|Vs],[Processed_value|Pvs],Rest):-
	term_to_atom(Processed_value,Value),!,
	process_args(More,Vs,Pvs,Rest).

process_args([number|More],[Value|Vs],[Processed_value|Pvs],Rest):-

	term_to_atom(Processed_value,Value),
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
	assert(param(Key,Value)).

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
%param_description('visual',_,'Launch the upper bound graphical visualizer ').
param_description('break_chains','Attempt to break phases').
param_description('fill_base_cases','If a SCC does not have a base case (non-recursive equation), one is added').

param_description('n_rankings',' nat : (default 2) Sets the maximum number of ranking functions that are considered for each cost equation ').
param_description('assume_sequential',
'Assume that the calls performed in a cost equation are done sequentially
It is important for non-terminating programs').

%param_description('solve_precise',
%' nat : (default not active) The  maximum number of extra constraints that can be considered when solving cost structures').

param_description('maximize_fast',
'nat : (default 5) The  maximum number of upper bound of a cost expression that the maximize operation can return').
