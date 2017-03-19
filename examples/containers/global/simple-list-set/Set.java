// The simplest possible stack
public /*: claimedby Set */ class Node {
    public Node next;
}
class Set {
    private static Node first;

    /*: public static specvar content :: objset;
      private vardefs "content == 
      {x. rtrancl_pt (% x y. Node.next x = y) first x & x ~= null}";
   
      invariant tree: "tree [Node.next]";
      
      invariant reallyFirst: "first = null | (ALL n. n..Node.next ~= first)";
   
      invariant noNextOutside: "ALL x y. x ~= null & y ~= null & x..Node.next = y --> y : content";
     */

    public static void add(Node x)
    /*: requires "x ~: content & x ~= null"
	modifies content
	ensures "content = old content Un {x}" */
    {
	x.next = first;
	first = x;
    }
}
