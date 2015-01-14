/*
    Copyright (C) 2009  E.Albert, P.Arenas, S.Genaim, G.Puebla, and D.Zanardini
                        https://costa.ls.fi.upm.es

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/
:- module(profiling,
	[profiling_start_timer/1,
	 profiling_stop_timer/1,
	 profiling_stop_timer/2,
	 profiling_get_info/3,
%	 profiling_info/3, % no longer exported
	 profiling_initialize/0,
	 profiling_add_entry/3,
	 profiling_stop_timer_acum/2,
	 profiling_get_all_entries/1]).

:- use_module(stdlib(utils),[ut_cputime/1]).


:- dynamic timer/2, profiling_info/3.


profiling_initialize :-
	retractall(timer(_,_)),
	retractall(profiling_info(_,_,_)).


profiling_get_info(Tag, Value, Other_Info):-
	profiling_info(Tag, Value, Other_Info).

profiling_start_timer(Timer_Tag) :-
	ut_cputime(T),
	retractall(timer(Timer_Tag,_)),
	assertz(timer(Timer_Tag,T)).


profiling_stop_timer(Timer_Tag) :-
	profiling_stop_timer(Timer_Tag,_T).

% returns in T the absolute time associated to the Timer_Tag
profiling_stop_timer(Timer_Tag,T) :-
	ut_cputime(T2),
	retract(timer(Timer_Tag,T1)),
	T is T2 - T1,
	retractall(profiling_info(Timer_Tag,_,_)),
	assertz(profiling_info(Timer_Tag,T,[start=T1,end=T2])).

profiling_stop_timer_acum(Timer_Tag,T) :-
	ut_cputime(T2),
	retract(timer(Timer_Tag,T1)),
	T is T2 - T1,
	(profiling_info(Timer_Tag,TAcum,_)->
	    TFinal is T + TAcum;
	    TFinal is T),
	retractall(profiling_info(Timer_Tag,_,_)),
	assertz(profiling_info(Timer_Tag,TFinal,[])).



profiling_add_entry(Tag, Value, Other_Info) :-
	retractall(profiling_info(Tag,_,_)),
	assertz(profiling_info(Tag,Value,Other_Info)).


% allows collecting in a list all profiling information available
% it requires initializing profiling info before each benchmark
profiling_get_all_entries(Entries) :-
	findall(t(Tag,Value,Other_Info), 
	        profiling_info(Tag,Value,Other_Info),
                Entries_u),
	pretty_print_entries(Entries_u,Entries).

pretty_print_entries([],[]).
pretty_print_entries([t(Tag,Value,[start=_,end=_])|Entries_u],[T|Entries]):- !,
	functor(Tag,F,_),
	RoundedTime is round(Value),
	T = time(F,RoundedTime),
	pretty_print_entries(Entries_u,Entries).
pretty_print_entries([t(Tag,Value,Other_Info)|Entries_u],[T|Entries]):-
	functor(Tag,F,_),
	functor(T,F,2),
	arg(1,T,Value),
	arg(2,T,Other_Info),
	pretty_print_entries(Entries_u,Entries).
