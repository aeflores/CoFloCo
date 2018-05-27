:- module(cost_structures_test,[
		
	]).

:-begin_tests(cost_structures).


:-use_module(cost_structures).
test(cstr_simplify1):-
	
	Cost=cost([bound(ub,[(_,1)]+0,[s(1),s(2)])],
     [bound(lb,[]+0,[s(2)]),bound(lb,[]+0,[s(1)])],
     [],
     [(s(1),1),(s(2),1)],
     1),
     cstr_simplify(Cost,Cost_simple),
     assertion(Cost_simple=cost([bound(ub,[(_,1)]+0,[s(1),s(2)])],
     [],
     [],
     [(s(1),1),(s(2),1)],
     1)).
     
test(cstr_simplify2):-
	init_cost_structures,
	Cost=cost([ bound(ub,[]+0,[s(4)]),
       bound(ub,[]+0,[s(2)]),
       bound(ub,[(A,1)]+0,[s(1),s(3)])
     ],
     [ bound(lb,[(A,-1)]+0,[s(4)]),
       bound(lb,[(A,-1)]+0,[s(2)]),
       bound(lb,[]+0,[s(3)]),
       bound(lb,[]+0,[s(1)])
     ],
     [],
     [(s(1),1),(s(2),-1),(s(3),1),(s(4),-1)],
     1),
	cstr_simplify(Cost,Cost_simple),
	
	assertion(Cost_simple=cost([
       bound(ub,[(A,1)]+0,[s(1),s(3)])
     ],
     [],
     [],
     [(s(1),1),(s(3),1)],
     1)).



:-end_tests(cost_structures).