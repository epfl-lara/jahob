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
	    (rtrancl_pt (% x y. x..Node.left = y | x..Node.right = y) root x)}";
   
       invariant TreeInv: "tree [Node.left, Node.right]";
   
       invariant RootInv: "root = null | 
                           (ALL n. n..Node.left ~= root & n..Node.right ~= root)";
   
       invariant ContentInv: 
        "ALL x. x ~: content & x ~= null --> 
                    (x..Node.left = null & 
                     x..Node.right = null &
                     (ALL y. y..Node.left ~= x & y..Node.right ~= x))";

       invariant ParentInv:
         "ALL x y. Node.parent x = y -->
           ((x ~: content | x = root) --> y = null) &
 	   (x : content & x ~= root --> y ~= null &
                                        (y..Node.left = x | y..Node.right = x))";
   */
    /*
       invariant ApparentlyWeakerParentInv:
        "ALL x y. Node.parent x = y -->
	 ((x : content -->
           (y = null --> x = root) &
           (y ~= null --> (y..Node.left = x | y..Node.right = x))) &
           (x ~: content --> y = null))";

       invariant ThomasParentInv:
         "ALL x y. Node.parent x = y -->
	  ((x ~= null & (EX z. z..Node.left = x | z..Node.right = x)) --> (y..Node.left = x | y..Node.right = x)) & 
	  (x = null | ((ALL z. z..Node.left ~= x & z..Node.right ~= x) --> y = null))";
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

   public static boolean contains(Node n)
   /*: requires "n ~= null"
       ensures "result --> n : content"
    */
   {
       Node curr = root;

       while /*: inv "curr ~= null --> curr : content"
	      */
	   (curr != null) {
	   if (curr == n) {
	       return true;
	   } else {
	       if (n.v < curr.v) {
		   curr = curr.left;
	       } else {
		   curr = curr.right;
	       }
	   }
       }
       return false;
   }

   public static boolean slowContains(Node n)
   /*: requires "n ~= null"
       ensures "result = (n : content)"
    */
   {
       return slowContainsRec(root, n);
   }

   private static boolean slowContainsRec(Node r, Node n)
   /*: requires "theinvs & n ~= null & (r ~= null --> r : content)"
       ensures "theinvs & result = 
       (rtrancl_pt (% x y. x..Node.left = y | x..Node.right = y) r n)"
    */
   {
       return (r != null) && ((r == n) || (slowContainsRec(r.left, n)) ||
	       (slowContainsRec(r.right, n)));
   }

   // This version is more readable.
   private static boolean slowContainsRecAlt(Node r, Node n)
   /*: requires "theinvs & n ~= null & (r ~= null --> r : content)"
       ensures "theinvs & result = 
       (rtrancl_pt (% x y. x..Node.left = y | x..Node.right = y) r n)"
    */
   {
       if (r == null) {
	   return false;
       } else if (r == n) {
	   return true;
       } else {
	   return (slowContainsRec(r.left, n)) ||
	       (slowContainsRec(r.right, n));
       }
   }

   public static Node extractMax()
   /*: modifies content
       ensures "(result = null --> (ALL x. (x ~: content))) &
                (result ~= null --> content = old content - {result})"
    */
   {
       Node curr = root;

       while /*: inv "(curr ~= null --> curr : content) &
	              (curr = null --> curr = root)"
	      */
	   (curr != null && curr.right != null) {
	   curr = curr.right;
       }

       if (curr != null) {
	   remove_int(curr);
       }

       return curr;
   }

   public static Node extractMin()
   /*: modifies content
       ensures "(result = null --> (ALL x. (x ~: content))) &
                (result ~= null --> content = old content - {result})"
    */
   {
       Node curr = root;

       while /*: inv "(curr ~= null --> curr : content) &
	              (curr = null --> curr = root)"
	      */
	   (curr != null && curr.left != null) {
	   curr = curr.left;
       }

       if (curr != null) {
	   remove_int(curr);
       }

       return curr;
   }

   private static Node removeMax(Node n)
   /*: requires "theinvs & n ~= null & n : content & n..Node.left ~= null"
       modifies content, "Node.left", "Node.right", "Node.parent"
       ensures "theinvs & content = old content - {result} & 
                result : old content & result ~= n"
    */
   {
       Node e = n.left;

       while /*: inv "e ~= null & e : content &
	              (rtrancl_pt (% x y. x..Node.right = y) (n..Node.left) e)"
	      */
	   (e.right != null) {
	   e = e.right;
       }

       if (e.parent.right == e) {
	   e.parent.right = e.left;
       } else {
	   e.parent.left = e.left;
       }

       if (e.left != null) {
	   e.left.parent = e.parent;
       }

       e.parent = null;
       e.left = null;
       return e;
   }

   // swap took over an hour to verify on tmi, but probably requires
   // less time on a faster machine
   private static void swap(Node toRemove, Node toAdd)
   /*: requires "toRemove ~= null & toRemove : content & 
                 toAdd ~= null & toAdd ~: content & theinvs"
       modifies content, "root", "Node.parent", "Node.right", "Node.left"
       ensures "content = old content - {toRemove} Un {toAdd} & theinvs"
   */
   {
       if (toRemove.parent == null) {
	   root = toAdd;
       } else if (toRemove.parent.left == toRemove) {
	   toRemove.parent.left = toAdd;
       } else {
	   toRemove.parent.right = toAdd;
       }

       toAdd.parent = toRemove.parent;
       toRemove.parent = null;
	   
       toAdd.left = toRemove.left;
       toRemove.left = null;

       toAdd.right = toRemove.right;
       toRemove.right = null;

       if (toAdd.left != null) {
	   toAdd.left.parent = toAdd;
       }

       if (toAdd.right != null) {
	   toAdd.right.parent = toAdd;
       }
   }
   
   public static void remove(Node e)
   /*: requires "e ~= null & e : content"
       modifies content, "Node.parent", "Node.right", "Node.left"
       ensures "content = old content - {e}"
   */
   {
       remove_int(e);
   }

   private static void remove_int(Node e)
   /*: requires "e ~= null & e : content & theinvs"
       modifies content, "root", "Node.parent", "Node.right", "Node.left"
       ensures "content = old content - {e} & theinvs"
    */
   {
       if (e.left == null) {
	   if (e.right == null) {
	       // e has no children
	       if (e.parent == null) {
		   // e is the root node
		   root = null;
	       } else if (e.parent.left == e) {
		   // e is a left child
		   e.parent.left = null;
	       } else {
		   // e is a right child
		   e.parent.right = null;
	       }
	   } else {
	       // e has a right child but no left child
	       if (e.parent == null) {
		   // e is the root node
		   root = e.right;
	       } else {
		   if (e.parent.left == e) {
		       // e is a left child
		       e.parent.left = e.right;
		   } else {
		       // e is a right child
		       e.parent.right = e.right;
		   }
	       }
	       e.right.parent = e.parent;
	       e.right = null;
	   }
           e.parent = null;
       } else {
	   if (e.right == null) {
	       // e has a left child but no right child
	       if (e.parent == null) {
		   // e is the root node
		   root = e.left;
	       } else {
		   if (e.parent.left == e) {
		       // e is a left child
		       e.parent.left = e.left;
		   } else {
		       // e is a right child
		       e.parent.right = e.left;
		   }
	       }
	       e.left.parent = e.parent;
	       e.left = null;
               e.parent = null;
	   } else {
	       // e has both a left and a right child
               Node r = removeMax(e);
               swap(e, r);
	   }
       }
   }

   // The code below is just for debugging
    /*
   
   private static void openP() { System.out.print("("); }
   private static void closeP() { System.out.print(")"); }
   private static void println() { System.out.println(); }  
   public static void printFrom(Node n)
   {
     //openP();
     if (n != null) {
       printFrom(n.left);
       System.out.print(n.v + " ");
       printFrom(n.right);
     }
     //closeP();
   }  
   public static void print()
   {
     printFrom(root);
     println();
   }
    */
}
 
