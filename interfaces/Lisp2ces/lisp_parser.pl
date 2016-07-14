/** <module> lisp_parser

Read a file with a sequence of S-expressions and express them as nested lists

@author Antonio Flores Montoya

@copyright Copyright (C) 2014-2016 Antonio Flores Montoya

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

:- module(lisp_parser,[
		parse_lisp/2
	]).

	
parse_lisp(File,S_expressions) :-
   phrase_from_file(s_expressions(S_expressions), File).

parse_lisp(File,_) :-
	throw(error('Failed parsing file',File)).	

s_expressions([Sexp|Sexps])-->
    spaces,
    s_expression(Sexp),!,
    spaces,
    s_expressions(Sexps).	
	
s_expressions([])-->spaces,[].


spaces --> space,!,spaces.
spaces -->[],!.

space --> [X],{ char_type(X,space)}.
space --> [X],{ char_type(X,white)}.

s_expression(E) --> is_atom(E).    
s_expression(E) --> "(",spaces, s_expressions(Exps),spaces,")",{E=Exps}.  

is_atom(string(String))-->"\'\"",anything_but_quotes(String),"\"".

is_atom(Name_lower) -->
      "|",anything_but_pipes(CHARS),"|",{atom_codes(Name,CHARS),downcase_atom(Name,Name_lower)}.

is_atom(Name_lower) -->
      chars(CHARS), {atom_codes(Name, CHARS),downcase_atom(Name,Name_lower)}.

anything_but_quotes([X|Y]) --> anything_but_quote(X), anything_but_quotes(Y).
anything_but_quotes([]) --> [],!.
anything_but_quote(X) --> [X], {\+atom_codes('\"',[X])}.

anything_but_pipes([X|Y]) --> anything_but_pipe(X), anything_but_pipes(Y).
anything_but_pipes([]) --> [],!.
anything_but_pipe(X) --> [X], {\+atom_codes('|',[X])}.


chars([X|Y]) --> char(X), chars(Y).
chars([X|Y]) --> "\\", [X], chars(Y).
chars([X]) --> "\\", [X].
chars([X]) --> char(X).
%char(X) --> [X], { char_type(X,csym) }.
char(X) --> "#\\",[X],!.
char(X) --> [X], {\+char_type(X,space),
				  \+char_type(X,white),
				  \+atom_codes('(',[X]),
				  \+atom_codes(')',[X])}.
