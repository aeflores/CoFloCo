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


eq('cons'(_Ai,Al,As,_Bi,Bl,Bs,_Ci,Cl,Cs),1,[],[Cl=1+Bl,Cs=As+Bs+1,Al>=0,As>=0,Bl>=0,Bs>=0,Cl>=0,Cs>=0]).

eq('consp'(_Ai,Al,As,1,0,0),1,[],[Al=<As,Al>=1,As>=1]).
eq('consp'(_Ai,Al,As,0,0,0),1,[],[Al=<As,Al=0,As=0]).

eq('atom'(_Ai,Al,As,0,0,0),1,[],[Al=<As,Al>=1,As>=1]).
eq('atom'(_Ai,Al,As,1,0,0),1,[],[Al=<As,Al=0,As=0]).

%eq('endp'(_Ai,Al,_As,0,0,0),1,[],[Al>=1]).
eq('endp'(_Ai,Al,As,0,0,0),1,[],[Al=<As,Al>=1,As>=1]).
eq('endp'(_Ai,Al,As,1,0,0),1,[],[Al=<As,Al=0,As=0]).

eq('car'(_Ai,Al,As,_Bi,Bl,Bs),1,[],[Al=<As,Al>=1,Bs+1=<As,As>=0,Bl>=0,Bs>=0]).
eq('car'(_Ai,Al,As,0,0,0),1,[],[Al=<As,Al=0,As=0]).
eq('cdr'(_Ai,Al,As,_Bi,Bl,Bs),1,[],[Al=<As,Bl+1=Al,Bs+1=<As,Al>=0,As>=0,Bl>=0,Bs>=0]).
eq('cdr'(_Ai,Al,As,0,0,0),1,[],[Al=<As,Al=0,As=0]).

eq('or'(1,_,_,_,_,_,1,0,0),1,[],[]).
eq('or'(_,_,_,1,_,_,1,0,0),1,[],[]).

eq('and'(1,_,_,1,_,_,1,0,0),1,[],[]).
eq('and'(A,_,_,B,_,_,0,0,0),1,[],[A+B=<1]).

eq('-'(Ai,_Al,_As,Bi,_Bl,_Bs,Ci,0,0),1,[],[Ci=Ai-Bi]).
eq('+'(Ai,_Al,_As,Bi,_Bl,_Bs,Ci,0,0),1,[],[Ci=Ai+Bi]).
eq('1+'(Ai,_Al,_As,Bi,0,0),1,[],[Bi=Ai+1]).
eq('1-'(Ai,_Al,_As,Bi,0,0),1,[],[Bi=Ai-1]).

eq('='(Ai,0,0,Ai,0,0,1,0,0),1,[],[]).
eq('='(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai>=Bi+1]).
eq('='(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai+1=<Bi]).

eq('>'(Ai,_Al,_As,Bi,_Bl,_Bs,1,0,0),1,[],[Ai>=Bi+1]).
eq('>'(Ai,_Al,_As,Bi,_Bl,_Bs,0,0,0),1,[],[Ai=<Bi]).

eq('<'(Ai,_Al,_As,Bi,_Bl,_Bs,1,0,0),1,[],[Ai+1=<Bi]).
eq('<'(Ai,_Al,_As,Bi,_Bl,_Bs,0,0,0),1,[],[Ai>=Bi]).

eq('binary-+'(Ai,_Al,_As,Bi,_Bl,_Bs,Ci,0,0),1,[],[Ci=Ai+Bi]).
eq('binary--'(Ai,_Al,_As,Bi,_Bl,_Bs,Ci,0,0),1,[],[Ci=Ai-Bi]).
eq('unary--'(Ai,_Al,_As,Bi,0,0),1,[],[Bi=0-Ai]).

%make them as multually exclusive as possible
eq('integerp'(_Ai,Al,As,0,0,0),1,[],[Al>=1,As>=1]).
eq('integerp'(_Ai,Al,As,Bi,0,0),1,[],[Al=0,As=0,Bi>=0,Bi=<1]).
eq('rationalp'(_Ai,Al,As,0,0,0),1,[],[Al>=1,As>=1]).
eq('rationalp'(_Ai,Al,As,Bi,0,0),1,[],[Al=0,As=0,Bi>=0,Bi=<1]).

eq('not'(A,_,_,1,0,0),1,[],[A=0]).
eq('not'(A,_,_,0,0,0),1,[],[A=1]).

eq('zp'(A,_,_,1,0,0),1,[],[A=0]).
eq('zp'(A,_,_,0,0,0),1,[],[A=1]).

eq('ash'(A,_,_,B,_,_,A,0,0),1,[],[B=0]).
eq('ash'(A,_,_,B,_,_,C,0,0),1,[],[B>=1,2*C=<A]).
eq('ash'(A,_,_,B,_,_,C,0,0),1,[],[B+1=<0,C>=2*A]).

eq('null'(Ai,0,0,0,0,0),1,[],[Ai>=1]).
eq('null'(Ai,0,0,0,0,0),1,[],[Ai+1=<0]).
eq('null'(0,0,0,1,0,0),1,[],[]).
eq('null'(_Ai,Al,As,0,0,0),1,[],[Al>=1,As>=1]).

%type check, we assume for now that it never fails
eq('the-check'(_Ai,_,_,_Bi,_,_,Ci,Cl,Cs,Ci,Cl,Cs),1,[],[]).

eq('nfix'(Ai,0,0,Ai,0,0),1,[],[Ai>=0]).
eq('nfix'(Ai,_,_,0,0,0),1,[],[Ai+1=<0]).
% we make the as mutually exclusive as possible
eq('nfix'(_,1,As,0,0,0),1,[],[As>=1]).
eq('nfix'(_,Al,_,0,0,0),1,[],[Al>=1]).

eq('hide'(Ai,Al,As,Ai,Al,As),1,[],[]).   % identity function
eq('coerce'(Ai,Al,As,Ai,Al,As),1,[],[]).   % for now, also treat this as id

eq('return-last'(_Ai,_,_,_Bi,_,_,Ci,Cl,Cs,Ci,Cl,Cs),1,[],[]).

% included for completeness and to avoid warnings, but not currently functional
eq('unary-/'(Ai,_Al,_As,Bi,0,0),1,[],[Ai>=1,Bi=1/Ai]).
eq('unary-/'(Ai,_Al,_As,Bi,0,0),1,[],[Ai+1=<0,Bi=1/Ai]).
eq('binary-*'(Ai,_Al,_As,Bi,_Bl,_Bs,Ci,0,0),1,[],[Ci=Ai*Bi]).

eq('eq'(Ai,0,0,Ai,0,0,1,0,0),1,[],[]).
eq('eq'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai+1=<Bi]).
eq('eq'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai>=Bi+1]).
% we would have to distinguish also the cases where A has bigger length but smaller size than B and vice-versa
% we just behave non-deterministically and improve performance
%eq('eq'(_,Al,As,_,Bl,Bs,0,0,0),1,[],[As>=Bs+1,Al>=Bl+1]).
%eq('eq'(_,Al,As,_,Bl,Bs,0,0,0),1,[],[As=<Bs-1,Al=<Bl+1]).
eq('eq'(_,Al,As,_,Bl,Bs,ZeroOne,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0,0=<ZeroOne,ZeroOne=<1]).
%eq('eq'(_,Al,As,_,Bl,Bs,1,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0]).

eq('equal'(Ai,0,0,Ai,0,0,1,0,0),1,[],[]).
eq('equal'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai+1=<Bi]).
eq('equal'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai>=Bi+1]).
% we would have to distinguish also the cases where A has bigger length but smaller size than B and vice-versa
% we just behave non-deterministically and improve performance
%eq('equal'(_,Al,As,_,Bl,Bs,0,0,0),1,[],[As>=Bs+1,Al>=Bl+1]).
%eq('equal'(_,Al,As,_,Bl,Bs,0,0,0),1,[],[As=<Bs-1,Al=<Bl+1]).
eq('equal'(_,Al,As,_,Bl,Bs,ZeroOne,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0,0=<ZeroOne,ZeroOne=<1]).
%eq('equal'(_,Al,As,_,Bl,Bs,1,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0]).

eq('eql'(Ai,0,0,Ai,0,0,1,0,0),1,[],[]).
eq('eql'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai+1=<Bi]).
eq('eql'(Ai,0,0,Bi,0,0,0,0,0),1,[],[Ai>=Bi+1]).
eq('eql'(_,Al,As,_,Bl,Bs,ZeroOne,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0,0=<ZeroOne,ZeroOne=<1]).
%eq('eql'(_,Al,As,_,Bl,Bs,1,0,0),1,[],[Al>=0,As>=0,Bl>=0,Bs>=0]).

%undefined
eq('acl2-numberp'(_Ai,_Al,_As,_Bi,0,0),1,[],[]).
eq('characterp'(_Ai,_Al,_As,_Bi,0,0),1,[],[]).
eq('stringp'(_Ai,_Al,_As,_Bi,0,0),1,[],[]).
eq('symbolp'(_Ai,_Al,_As,_Bi,0,0),1,[],[]).
eq('char-code'(_Ai,_Al,_As),1,[],[]).
eq('code-char'(_Ai,_Al,_As),1,[],[]).
eq('<<'(_Ai,_Al,_As,_Bi,_Bl,_Bs,_Ci,0,0),1,[],[]).
