Creating a statically linked binary
==================================

It is not easy to create a statically linked binary in Prolog and things don't get easier when you have libraries like ppl that are usually dinamically linked.

This Makefile works in my system:
 * Ubuntu 64 bits
 * ppl 1.1-1.2
 * Swi-prolog 6.6.6 and Swi-prolog 7.4.2
 
But there is no guarantee that it will work elsewhere.
Are you feeling lucky? then type:
  
  `make`
  
You might get many errors regarding the predicates of the ppl library. In principle you can ignore those errors. Those predicates are missing at this point but they will be statically liked (hopefully).

The make should generate a binary `cofloco_static` that should work if everything went as planned.

### Problems (with Swi-prolog 6.6.6):


An error that I encountered is that I could obtain a working binary that would print the following error message at the beginning nonetheless:

`ERROR: /usr/lib/swi-prolog/library/filesex.pl:57: Initialization goal raised exception:`

`ERROR: '$open_shared_object'/3: files: cannot open shared object file: No such file or directory`

This is because the library filesex gets autoloaded and this library tries to load some libraries dinamically (using the use_foreign_library predicate).
A very bad solution (but a solution anyway) is:
 * Comment the line that loads these libraries temporarily (in my case, line 57).
   This breaks this library but luckily it is not needed by CoFloCo.
 * Compile the binary 
 * Uncomment the line again to restore your swi-prolog copy.


