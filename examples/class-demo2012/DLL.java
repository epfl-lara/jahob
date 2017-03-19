/*
INTERACTIVE DEMO SUMMARY:

Before starting,
* remove invariant from addLast (make it "True")
* for remove, leave only these two statements:
   n.prev.next = n.next;
   n.next.prev = n.prev;

Draw the assumptions about tree structure and the graphical
interpretation of invariants (without showing invariants).

Interactively discover the invariant

1) Explain addLast procedure. 
2) Run verifier (get null derefence).
3) Fix it with "r ~= null". Get postcondition violation.
4) Help come up with "r : content" as the invariant.

5) What is 'content'? Explan the definition and the syntax.
6) Explain the meaning of invariants. They are conjoined to pre and post.
7) Interactively develop remove from the common case.
   Help interpret the error messages and identify possible preconditions
   for which things go wrong.
   Use "assume false" to block branches that we did not develop yet.
8) Discuss that invariants need to be reestablished. Explain what
   'tree' invariant means.

 */

class Node {
    public /*: claimedby DLL */ Node next;
    public /*: claimedby DLL */ Node prev;
}
class DLL
{
   private static Node root;
   
   /*: public static specvar content :: objset;
       private vardefs "content == 
        {x. (root,x) : {(u,v). next u = v}^*  & x ~= null}";
   
       invariant tree: "tree [next]";
   
       invariant rootFirst: "root = null | 
                             (ALL n. n..next ~= root)";
   
       invariant noNextOutside: "ALL x y. x ~= null & y ~= null 
                               & x..next = y --> y : content";

       invariant prevDef: "ALL x y. prev x = y --> 
             (x ~= null & (EX z. next z = x) --> next y = x) &
             (((ALL z. next z ~= x) | x = null) --> y = null)";
   */

   public static void addLast(Node n)
      /*: 
	requires "n ~: content & n ~= null & n..prev = null & n..next = null"
	modifies content
	ensures "content = old content Un {n}";
      */
   {
      if (root == null) {
        root = n;
        n.next = null; 
        n.prev = null;
        return;
      }

      Node r = root;
      while //: inv "r : content"
       (r.next != null) {
	 r = r.next;
      }
      r.next = n; 
      n.prev = r;
   }

   public static void remove(Node n)
  /*: requires "(n : content)"
      modifies content
      ensures "content = old content - {n}"
   */
   {

       if (n == root) {
	   root = n.next;           
           if (root != null) {
	       root.prev = null;
	   }
	   n.next = null;
       } else {
	   n.prev.next = n.next;
	   if (n.next != null) {
	       n.next.prev = n.prev;
	       n.next = null;
	   }
	   n.prev = null;
       }
   }

}



