Usage information
------------------
Usage: cofloco [Options]
 where Options are:
* [-h,-help]  :Display help information 
* [-input,-i]  filename: Selects input program. 
* [-stats,-s]  Show some basic statistics 
* [-debug]  Show debug information 
* [-v,-verbosity]  0-3 : selects the level of verbosity  
* [-no_warnings]  Do not print any warnings 
* [-competition]  Set output and settings for complexity competition 
* [-incremental]  The usual analysis performs the control-flow refinement of the  complete cost relation system first and all the bound computation later. 
  With this option, the refinement and the bound computation are done bottom up for one cost relation at a time 
* [-n_candidates]   nat : (default 1) Sets the maximum number of candidates considered for a strategy 
* [-context_sensitive]   nat : (default 1) How context sensitive the bound computation is
 1. Each phase is solved only once with invariants valid for all its appearances in different chains
 2. Each phase is solved individually for each chain taking the specific invariants of that chain into account 
* [-assume_sequential]  Assume that the calls performed in a cost equation are done sequentially
It is important for non-terminating programs 
* [-compute_ubs]  Obtain closed-form upper bounds 
* [-compute_lbs]  Obtain closed-form lower bounds (If disabled, additional simplifications can be made on cost structures) 
* [-conditional_ubs]  Generate a set of conditional upper bounds (whose preconditions are mutually exclusive) instead of a single unconditional one 
* [-conditional_lbs]  Generate a set of conditional lower bounds (whose preconditions are mutually exclusive) instead of a single unconditional one 
* [-solve_fast]  Solve cost structures into closed form bounds with a greedy strategy instead of an exhaustive search
* [-compress_chains]  0-2 : (default 0) Join chains that have the same precondition. It can increase performance greatly but also affect precision 

### Example:
 The following command will analyze the file EXAMPLE_FILE with verbosity set to 3
 and it will generate a set of conditional upper bounds
   
    ./cofloco -i EXAMPLE_FILE -v 3 -conditional_ubs

Input format
------------------
A cost relation system is a list of cost equations. 
The syntax of the cost equations (Equation) is defined below.

### Cost equations format

    Equation::= eq(Head, CostExpression, ListOfCalls, ListOfSizeRelations).

    Head::= Name | Name(Arguments) 

    Arguments ::= Variable | Variable,Arguments

    ListOfCalls ::= [] |[Head|ListOfCalls]

    ListOfSizeRelations ::= [] | [SizeRelation|ListOfSizeRelations]

    SizeRelation ::= Variable Oper LinearExpression

    Oper ::=  >= | <= | = | < | >

    CostExpression :: = LinearExpression | nat(LinearExpression)

    LinearExpression ::= Variable | RationalNumber | 
                     LinearExpression + LinearExpression |
                     LinearExpression - LinearExpression |
                     RationalNumber   * LinearExpression |
                     LinearExpression / RationalNumber


* A "Name" can be either a sequence of characters between quotes or any
  sequence of consecutive characters (only letters and numbers) 
  beginning with a lower letter. Examples of valid names are:
 
       'function factorial'
       factorial
       factorial1

  Examples of invalid names are:

       Factorial
       1factorial
       function factorial

* Variables follows Prolog syntax, i.e., are sequences of characters
  (letters or numbers) beginning with a capital letter. Examples of
  valid variables are:

      X
      Variable1

### Entries
You can specify one or several entry points i.e. where the execution
starts. If you do not specify any, the first cost equation is considered to 
be the entry point. The syntax for the entries is:

    Entry ::= entry(Head:Precondition).

    Precondition ::= ListOfSizeRelations

### Defining the input and output variables
You can also specify for each cost relation which variables are input variables 
and which ones are output variables. This can be important to avoid obtaining closed-form
bounds expressed in terms of output variables.
The syntax to define the input and output variables of a cost relation is:

    InputOutputVariables ::= input_output_variables(Head,ListOfInputVariables,ListOfOutputVariables).

    ListOfInputVariables ::= ListOfVariables
    ListOfOutputVariables ::= ListOfVariables

    ListOfVariables ::= [] | [Variable|ListOfVariables]

Note:the input and output variables should be disjunt and their union should account
for all the variables in the Head.

### Example

    % You can have comments preceded by %
    % We have a cost relation system representing a simple nested loop

    % whileLoop is the entry of our cost relation system
    % it will be analyzed taking the precondition [N>=0,M>=0] into account

    entry(whileLoop(N,M):[N>=0,M>=0]).

    % the cost relation representing the outer loop
    eq(whileLoop(N,M),0,[],[N=0]).
    eq(whileLoop(N,M),1,[innerLoop(M,Mout),whileLoop(N2,Mout)],[1=<N,N2=N-1]).
    % in the recursive references, you can have simple expression such as N-1
    % so you could substitute the second equation by 
    %
    % eq(whileLoop(N,M),1,[innerLoop(M,Mout),whileLoop(N-1,Mout)],[1=<N]).

    % the cost relation of the inner loop
    eq(innerLoop(M,Mout),1,[innerLoop(M-1,Mout)],[1=<M]).
    eq(innerLoop(M,Mout),0,[],[M=0,M=Mout]).

    % you can also have implicit equalities by reusing variable names or having constant
    % values instead of variables
    % the last equation is equivalent to:
    % eq(innerLoop(M,M),0,[],[M=0]).
    % or
    % eq(innerLoop(0,0),0,[],[]).
    

