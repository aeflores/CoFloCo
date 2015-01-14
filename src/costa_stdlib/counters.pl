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
:- module(counters,[counter_initialize/2, counter_get_value/2, counter_increase/3]).


:- dynamic counter/2.


counter_initialize(C_Id,Init_Value) :-
	retractall(counter(C_Id,_)),
	assertz(counter(C_Id,Init_Value)),
	!.

counter_get_value(C_Id, Value) :-
	counter(C_Id,Value),
	!.

counter_increase(C_Id, I, New_Value) :-
	retract(counter(C_Id, Curr_Value)),
	New_Value is Curr_Value+I,
	assertz(counter(C_Id,New_Value)),
	!.
