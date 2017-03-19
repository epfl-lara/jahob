public final class Node {
    public /*: claimedby Simple */ Node next;
    public /*: claimedby Simple */ Node prev;
}
public class Simple
{
   private static Node first;

   private static void add(Node n)
   /*: modifies next, first, prev
       ensures "True"
    */
   {
       /*: assume "n ~= null & next n = null & prev n = null";
	   assume "first ~= null --> prev first = null";
           assume "ALL x y. (x : alloc & y : alloc & 
prev x = y --> 
            (y ~= null --> next y = x) & 
            (y = null & x ~= null --> (ALL z. next z ~= x)))";
       */
      if (first == null) {
	  first = n;
	  n.next = null;
	  n.prev = null;
      } else {
	  //n.next = first;
	 first.prev = n;
	 first = n;
      }
      /*:
           assert backForth: "ALL x y. prev x = y --> 
            (y ~= null --> next y = x) & 
            (y = null & x ~= null --> (ALL z. next z ~= x))";
      */
   }
}
