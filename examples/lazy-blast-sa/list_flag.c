/*
 * Variation on example 0: use a (non-deterministic) boolean
 * flag to set the value of the elements in the list before
 * 3 to a value depending on the flag, and check later on
 * that the list is what has been built just before.
 * (TVLA cannot handle it properly because it would be too
 *  imprecise because of the summary done between the cases
 *  where the flag is true or false)
 */
/*#include <stdlib.h>
  #include "assert.h"*/

void exit(int s) {
 _EXIT: goto _EXIT;
}

typedef struct node {
  int h;
  struct node *n;
} *List;

void main() {
  int __BLAST_NONDET;
  int flag = __BLAST_NONDET;
  List p, a, t;

  /* Build a list of the form x->x->x->...->x->3
   * with x depending on some flag
   */
  a = (List) malloc(sizeof(struct node));
  if (a == 0) exit(1);
  p = a;
  while (__BLAST_NONDET) {
    if (flag) {
      p->h = 1;
    } else {
      p->h = 2;
    }
    /*** TVLA forgets at this point the dependence
	 between p->h and the value of flag        ***/
    t = (List) malloc(sizeof(struct node));
    if (t == 0) exit(1);
    p->n = t;
    p = p->n;
  }
  p->h = 3;
    
  /* Check it */
  p = a;
  if (flag)
    while (p->h == 1)
      p = p->n;
  else
    while (p->h == 2)
      p = p->n;
  if (p->h != 3)
    ERROR: goto ERROR;
}
