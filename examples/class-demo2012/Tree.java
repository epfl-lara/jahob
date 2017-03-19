/* Global tree without checking sortedness.

PLUS:
  given loopinvs, all automated by mona
  
MINUS:
  very slow (say, 16minutes without parallelization), as MONA is slow
  no sorting, so contains is either partially specified or must be implemented naively

 */

public final class Node {
   public /*: claimedby Tree */ Node left;
   public /*: claimedby Tree */ Node right;
   public /*: claimedby Tree */ Node parent;
   public /*: claimedby Tree */ int v;
}

public class Tree
{
   private static Node root;
   
   /*: public static specvar content :: objset;
       private vardefs "content == 
        {x. x ~= null & 
            (root,x) : {(x,y). x..left = y | x..right = y}^*}";
   
       invariant TreeInv: "tree [left, right]";
   
       invariant RootInv: "root = null | 
        (ALL n. n..left ~= root & n..right ~= root)";
   
       invariant ContentInv: 
        "ALL x. x ~: content & x ~= null --> 
              (x..left = null & x..right = null &
              (ALL y. y..left ~= x & y..right ~= x))";

       invariant ParentInv:
         "ALL x y. parent x = y -->
           ((x ~: content | x = root) --> y = null) &
 	   (x : content & x ~= root --> y ~= null &
           (y..left = x | y..right = x))";
   */

   public static void add(Node e)
      /*: 
	requires "e ~= null & e ~: content"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      boolean wentLeft = false;
      while /*: inv "((p = null & n = null) --> root = null) &
		     (p ~= null --> p : content) &
		     (n ~= null --> n : content) &
		     (p ~= null & wentLeft --> p..Node.left = n) &
		     (p ~= null & ~wentLeft --> p..Node.right = n)"
	     */
	  (n != null) {
	 p = n;
	 if (e.v < n.v) {
	    wentLeft = true;
            n = n.left;
	 } else {
	    wentLeft = false;
	    n = n.right;
	 }
      }
      if (p == null) {
	 root = e;
      } else {
	 e.parent = p;
	 if (wentLeft) {
            p.left = e;
	 } else {
            p.right = e;
	 }
      }
   }
}
 
