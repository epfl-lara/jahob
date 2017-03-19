public final class Node {
    public /*: claimedby Simple */ Node next;
    public /*: claimedby Simple */ Node prev;
}
public class Simple
{
   private static Node first;

   private static void add(Node n)
   {
       /*: assume "n ~= null & n..next = null & n..prev = null";
	   assume "first ~= null --> first..prev ~= null";
           assume "ALL x y. x..prev = y --> 
            (y ~= null --> Node.next y = x) & 
            (y = null & x ~= null --> (ALL z. z..next ~= x))";
       */
      if (first == null) {
	 first = n;
	 n.next = null;
	 n.prev = null;
      } else {
	 n.next = first;
	 first.prev = n;
	 n.prev = null;
	 first = n;
      }
      /*:
           assert backForth: "ALL x y. x..prev = y --> 
            (y ~= null --> Node.next y = x) & 
            (y = null & x ~= null --> (ALL z. z..next ~= x))";
	   assume "first ~= null --> first..prev ~= null";
      */
   }
}
