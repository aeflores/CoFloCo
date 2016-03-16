/** <module> basic_lisp

Size relations of the basic lisp functions

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
:- module(basic_lisp,[
		eq/4
	]).

eq('or'(1,_,1),1,[],[]).
eq('or'(_,1,1),1,[],[]).

eq('and'(1,1,1),1,[],[]).
eq('and'(A,B,0),1,[],[A+B=<1]).

eq('-'(A,B,C),1,[],[C=A-B]).
eq('+'(A,B,C),1,[],[C=A+B]).
eq('1+'(A,B),1,[],[B=A+1]).
eq('1-'(A,B),1,[],[B=A-1]).

eq('='(A,A,1),1,[],[]).
eq('='(A,B,0),1,[],[A>=B+1]).
eq('='(A,B,0),1,[],[A+1=<B]).

eq('eql'(A,A,1),1,[],[]).
eq('eql'(A,B,0),1,[],[A>=B+1]).
eq('eql'(A,B,0),1,[],[A+1=<B]).

eq('>'(A,B,1),1,[],[A>=B+1]).
eq('>'(A,B,0),1,[],[A=<B]).

eq('<'(A,B,1),1,[],[A+1 =< B]).
eq('<'(A,B,0),1,[],[A >= B]).


eq('endp'(A,1),1,[],[A=0]).
eq('endp'(A,0),1,[],[A>=1]).

eq('not'(A,1),1,[],[A=0]).
eq('not'(A,0),1,[],[A=1]).

eq('zp'(A,1),1,[],[A=0]).
eq('zp'(A,0),1,[],[A>=1]).

eq('car'(A,B),1,[],[A=0,A=B]).
eq('car'(A,B),1,[],[A>=1,B+1=<A]).

eq('cdr'(A,B),1,[],[A=0,A=B]).
eq('cdr'(A,B),1,[],[A>=1,B+1=<A]).




eq('binary-+'(A,B,C),1,[],[C=A+B]).
eq('binary--'(A,B,C),1,[],[C=A-B]).
eq('unary--'(A,B),1,[],[B=A-1]).

eq('ash'(A,B,A),1,[],[B=0]).
eq('ash'(A,B,C),1,[],[B>=1,2*C=<A]).
eq('ash'(A,B,C),1,[],[B+1=<0,C>=2*A]).

eq('cons'(A,B,C),1,[],[C=A+B+1]).
eq('consp'(A,1),1,[],[A>=1]).
eq('consp'(A,0),1,[],[A=0]).

eq('atom'(A,0),1,[],[A>=1]).
eq('atom'(A,1),1,[],[A=0]).

eq('quote'(A,1),1,[],[A>=1]).



eq('null'(0,1),1,[],[]).
eq('null'(A,0),1,[],[A>=1]).
eq('null'(A,0),1,[],[A+1=<0]).

%type check, we assume for now that it never fails
eq('the-check'(_A,_B,C,C),1,[],[]).
%eq('the-check'(A,_B,C,C),1,[],[A=1]).
%eq('the-check'(A,B,_C,B),1,[],[A=0]).

eq('nfix'(A,A),1,[],[A>=0]).
eq('nfix'(A,0),1,[],[A+1=<0]).

eq('lnfix$inline'(A,A),1,[],[]).

%undefined
eq('return-last'(_A,_B,_C,_D),1,[],[]).
eq('unary-/'(_A,_B),1,[],[]).
eq('integerp'(_A,_B),1,[],[]).
eq('characterp'(_A,_B),1,[],[]).
eq('stringp'(_A,_B),1,[],[]).
eq('binary-*'(_A,_B,_C),1,[],[]).
eq('equal'(_A,_B,_C),1,[],[]).
eq('eq'(_A,_B,_C),1,[],[]).
eq('<<'(_A,_B,_C),1,[],[]).
