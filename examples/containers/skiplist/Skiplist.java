public class Skiplist 
{
    private static Node root;
    
    /*: 
      public static specvar content :: objset;
     
      private static specvar reach :: "obj => obj => bool";
      vardefs "reach == (% a b. rtrancl_pt (% x y. x..Node.next = y) a b)";
 
      private vardefs "content == {x. (root,x) : {(x,y). x..next = y}^* & x ~= null}";
   
      invariant "tree [Node.next]";
   
      invariant "ALL x y. Node.nextSub x = y --> ((x = null --> y = null) 
                            & (x ~= null --> (Node.next x,y) : {(x,y). x..next = y}^*))";

      invariant "ALL x. x ~= null & (root,x) ~: {(x,y). x..next = y}^* --> 
                           Node.next x = null &
                           (ALL y. y ~= null --> Node.next y ~= x)";
    */

    /*
      private static boolean randomBit() 
      {
        return false;
      }
    */
   
   public static void add(Node e) 
   /*: requires "e ~= null & e ~: content"
       modifies content
       ensures "content = old content Un {e}" 
   */
    {
        if (root==null) {
            root = e;
        } else {
            int v = e.v;
            Node sprev = root;
            Node scurrent = root.nextSub;

            while ((scurrent != null) && (scurrent.v < v)) {
                sprev = scurrent;
                scurrent = scurrent.nextSub;
            }
            // found place in sublist, now search from
            // sprev to scurrent in list
            Node prev = sprev;
            Node current = sprev.next;
            while ((current != scurrent) && (current.v < v)) {
                prev = current;
                current = current.next;
            }
            e.next = current;
            prev.next = e;

            if (v > 0) {
                sprev.nextSub = e;
                e.nextSub = scurrent;
            } else {
                e.nextSub = null;
            }
        }
    }
}
