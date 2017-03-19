public class List {
    private Node head;

    /*:
      private ghost specvar nodes :: "int => obj";
      private ghost specvar len :: int;
     */

    private int max() 
    /*:
      requires "len >= 0 &
	       nodes 0 = head &
	       (ALL (j::int). (j >= 0 --> nodes (j+1) = (nodes j)..next)) &
	       nodes len = null &
	       (ALL (j::int). (j >= 0 & j < len --> nodes j != null)) &
	       (ALL (k::int) (j::int).
	        (k ~= j & k >= 0 & j >= 0 & k <= len & j <= len --> nodes k ~= nodes j))"
       ensures "(ALL (j::int). (j >= 0 & j < len --> result >= (nodes j)..val )) &
                (len > 0 --> (EX (j::int). (j >= 0 & j < len & result = (nodes j)..val)))"

     */
    {
	if ( head == null ) return 0;
	Node t = head;
	int max = t.val;
	while /*: inv "EX (k::int). ( k >= 0 & k < len & t = nodes k & 
		    (ALL (j::int). (j >= 0 & j <= k --> max >= (nodes j)..val)) &
		    (EX (j::int). (j >= 0 & j <= k & max = (nodes j)..val)))" */
	    ( t.next != null ) {
	    t = t.next;
	    if ( t.val > max ) max = t.val;
	}
	return max;
    }
}

class Node {
    public Node next;
    public int val;    
}
