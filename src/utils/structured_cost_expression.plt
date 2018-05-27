:- module(structured_cost_expression_test,[]).

:-begin_tests(structured_cost_expression).

:-use_module('../main_cofloco').
:-use_module(structured_cost_expression).

/*
prolog:assertion_failed(Reason,Goal):-
	throw(assertion_error(Reason,Goal)).
	
test(nonterm_bug,[error(assertion_error(fail,_))]):-
		structured_cost_expression:strexp_simplify_max_min(
		min([add([mult([], 0), 
			  mult([add([])], 10), 
			  mult([add([])], 0), 
			  mult([nat(add([mult([nat(A)], -1)]))], 1)]),
		
			add([mult([], 1), 
				mult([add([])], 10),
				mult([add([])], 0),
				mult([nat(add([mult([], 1), mult([nat(A)], -1)]))], 1)
			]), 
			add([mult([], 10), 
		 		mult([add([])], 10), 
		 		mult([add([])], 0), 
		 		mult([nat(add([mult([nat(A)], -1)]))], 1)
		 	])
	]), _).
*/	
	
:-end_tests(structured_cost_expression).