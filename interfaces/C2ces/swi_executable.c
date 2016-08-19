#include <stdio.h>
#include <SWI-Prolog.h>

#define MAXLINE 1024




int
main(int argc, char **argv)
{
  int rval;

  /* initialise Prolog */

  if ( !PL_initialise(argc, argv) )
    PL_halt(1);

  

  predicate_t pred = PL_predicate("main", 0, "user");
  rval = PL_call_predicate(NULL, PL_Q_NORMAL, pred, 0);

 

  PL_halt(rval ? 0 : 1);

  return 0;
}
