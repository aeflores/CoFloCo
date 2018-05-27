/** <module> db

This module acts as a database that stores:

  * the set of cost equations in different stages of refinement
  * the external call patterns, that summarize the possible call patterns to a refined SCC
  * the loops (which are fragments of cost equations)
  * the generated closed-form bounds

@author Antonio Flores Montoya

@copyright Copyright (C) 2014-2018 Antonio Flores Montoya

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

:- module(db,[
       init_db/0,
       init_timers/0,
	   add_ground_equation_header/2,
	   ground_equation_header/1,
	   reset_scc/3
]).
:- use_module('IO/params',[get_param/2]).

:- use_module('utils/cofloco_utils',[assign_right_vars/3]).
:- use_module('utils/structured_cost_expression',[strexp_simplify_max_min/2,strexp_to_cost_expression/2]).
:- use_module('utils/cost_expressions',[cexpr_simplify/3]).


:- use_module(stdlib(utils),[ut_var_member/2]).
:- use_module(stdlib(counters),[counter_initialize/2,counter_increase/3,counter_get_value/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_entails/3,nad_glb/3,nad_list_lub/2,nad_lub/6,nad_project/3]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_get_info/3,
				 profiling_stop_timer/2,profiling_stop_timer_acum/2]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(terms)).

%! ground_equation_header(Head:term)
% A ground version of the cost equation header that records the original names of the variables in the input file.
% it is used to print the results according to those names
:- dynamic ground_equation_header/1. 

%! reset_scc(Head:term,Vars:list(var),Type:flag)
% specify that the scc whose header is Head has to be compressed keeping
% only the information related to Vars
% Type can be 'weak' or 'strong' 
:-dynamic reset_scc/3.





%! init_db is det
% erase the database and initialize counters
init_db:-
	retractall(ground_equation_header(_)),
	retractall(reset_scc(_,_,_)),
	counter_initialize(ubs,0),
	counter_initialize(costs,0).
	
%! init_timers is det
% initialize timers
init_timers:-
	profiling_start_timer(comp_sccs),profiling_stop_timer_acum(comp_sccs,_),
	profiling_start_timer(pe),profiling_stop_timer_acum(pe,_),
	profiling_start_timer(inv),profiling_stop_timer_acum(inv,_),
	profiling_start_timer(unfold),profiling_stop_timer_acum(unfold,_),
	profiling_start_timer(ubs),profiling_stop_timer_acum(ubs,_),
	profiling_start_timer(loop_phases),profiling_stop_timer_acum(loop_phases,_),
	profiling_start_timer(chain_solver),profiling_stop_timer_acum(chain_solver,_),
	profiling_start_timer(equation_cost),profiling_stop_timer_acum(equation_cost,_),
	profiling_start_timer(flatten_loops),profiling_stop_timer_acum(flatten_loops,_),
	profiling_start_timer(compress_or),profiling_stop_timer_acum(compress_or,_),
	profiling_start_timer(solver),profiling_stop_timer_acum(solver,_),
	profiling_start_timer(black_cost),profiling_stop_timer_acum(black_cost,_),
	profiling_start_timer(termination),profiling_stop_timer_acum(termination,_).



	

%! add_ground_equation_header(+Non_ground:term,+Ground:term) is det
% store the ground term Ground if there is no ground_equation_header that can be unified with Non_ground.
% that is, we store on ground_equation_header per cost equation header
add_ground_equation_header(Non_ground,_Ground):-
	copy_term(Non_ground,Non_ground2),
	ground_equation_header(Non_ground2),!.
	
add_ground_equation_header(_Non_ground,Ground):-
	assertz(ground_equation_header(Ground)).
