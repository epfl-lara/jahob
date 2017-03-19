public /*: claimedby BinarySearchTree */ final class Node {
   public /*: claimedby BinarySearchTree */ Node left;
   public /*: claimedby BinarySearchTree */ Node right;
   public /*: claimedby BinarySearchTree */ Node parent;
   public /*: claimedby BinarySearchTree */ int v;

   /*: public specvar subtree :: objset;
       public vardefs "subtree ==
        {n0. n0 \<noteq> null \<and> (this,n0) \<in> {(x,y). x..left=y \<or> x..right=y}^*}"; */
}

public class BinarySearchTree
{
   private static Node root;
   
   /*: public static specvar content :: objset;
       private vardefs "content == root..subtree";
   
       invariant TreeInv: "tree [Node.left, Node.right]";
   
       invariant RootInv: "root = null \<or>
                           (\<forall> n. n..left \<noteq> root & n..right \<noteq> root)";
   
       invariant ContentInv: 
        "\<forall> x. x \<notin> content & x \<noteq> null \<longrightarrow>
             (x..left = null \<and> x..right = null \<and>
              (\<forall> y. y..left \<noteq> x \<and> y..right \<noteq> x))";

       invariant ParentInv:
         "\<forall> x y. parent x = y \<longrightarrow>
          ((x \<notin> content \<or> x = root) \<longrightarrow> y = null) \<and>
          (x \<in> content & x \<noteq> root \<longrightarrow> y \<noteq> null \<and> (y..left = x \<or> y..right = x))";
      invariant LeftOrderingInv:
         "\<forall> x y. y \<in> x..left..subtree \<longrightarrow> y..v < x..v";

       invariant RightOrderingInv:
         "\<forall> x y. y \<in> x..right..subtree \<longrightarrow> y..v \<ge> x..v";
   */

   public static void add(Node e)
      /*: 
	requires "e \<noteq> null & e \<notin> content"
	modifies content
	ensures "content = old content \<union> {e}";
      */
   {
      Node n = root, p = null;
      boolean wentLeft = false;
      while /*: inv "(p = null \<and> n = null \<longrightarrow> root = null) \<and>
	             (p = null \<longrightarrow> n = root) \<and>
		     (p \<noteq> null \<longrightarrow> p \<in> content) \<and>
		     (n \<noteq> null \<longrightarrow> n \<in> content) \<and>
		     (p \<noteq> null \<and> wentLeft \<longrightarrow> p..left = n) \<and>
		     (p \<noteq> null \<and> \<not> wentLeft \<longrightarrow> p..right = n) \<and>
		     (comment ''WentLeftLInv''
		       (p \<noteq> null \<and> wentLeft \<longrightarrow> e..v < p..v)) \<and>
		     (comment ''WentRightLInv''
		       (p \<noteq> null \<and> \<not> wentLeft \<longrightarrow> e..v \<ge> p..v)) \<and>
		     (comment ''LOrderLInv''
                       (\<forall> x. p \<in> x..left..subtree \<and> p \<noteq> null \<and>
		             p \<noteq> x \<longrightarrow> e..v < x..v)) \<and>
		     (comment ''ROrderLInv''
                       (\<forall> x. p \<in> x..right..subtree \<and> p \<noteq> null \<and>
		             p \<noteq> x \<longrightarrow> e..v \<ge> x..v))" */
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
       ensures "result = (n : content)"
    */
   {
       Node curr = root;

       while /*: inv "(curr ~= null --> curr : content) &
	              (comment ''InContentLInv''
		      (n : content) = (n : curr..Node.subtree))"
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

   public static Node extractMax()
   /*: modifies content
       ensures "(result = null --> (ALL x. (x ~: content))) &
                (result ~= null --> content = old content - {result}) &
		(result ~= null -->
		(ALL x. x : old content --> result..Node.v >= x..Node.v))"
    */
   {
       //: private static ghost specvar smaller :: objset;
       Node curr = root;

       //: smaller := "{}";
       while /*: inv "(curr ~= null --> curr : content) &
	              (curr = null --> curr = root) &
		      (content = smaller Un curr..Node.subtree) &
		      (comment ''SmallerLInv''
		      (ALL x. x : smaller --> curr..Node.v >= x..Node.v))"
	     */
	   (curr != null && curr.right != null) {
	   //: smaller := "smaller Un {curr} Un curr..Node.left..Node.subtree";
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
                (result ~= null --> content = old content - {result}) &
		(result ~= null -->
		(ALL x. x : old content --> result..Node.v <= x..Node.v))"
    */
   {
       //: private static ghost specvar bigger :: objset;
       Node curr = root;

       //: bigger := "{}";
       while /*: inv "(curr ~= null --> curr : content) &
	              (curr = null --> curr = root) &
		      (content = bigger Un curr..Node.subtree) &
		      (comment ''BiggerLInv''
		      (ALL x. x : bigger --> curr..Node.v <= x..Node.v))"
	      */
	   (curr != null && curr.left != null) {
	   //: bigger := "bigger Un {curr} Un curr..Node.right..Node.subtree";
	   curr = curr.left;
       }

       if (curr != null) {
	   remove_int(curr);
       }

       return curr;
   }

   private static Node removeMin(Node n)
   /*: requires "theinvs & n ~= null & n : content & n..Node.right ~= null"
       modifies content, "Node.left", "Node.right", "Node.parent", 
                "Node.subtree"
       ensures "theinvs & content = old content - {result} & 
                result : old content & result ~= n &
		(ALL y. y : n..Node.left..Node.subtree --> 
		y..Node.v < result..Node.v) &
		(ALL y. y : n..Node.right..Node.subtree -->
		result..Node.v <= y..Node.v) &
		(ALL x. n : x..Node.left..Node.subtree -->
		result..Node.v < x..Node.v) &
		(ALL x. n : x..Node.right..Node.subtree -->
		x..Node.v <= result..Node.v) &
		Node.v = (old Node.v)"
   */
   {
       //: private static ghost specvar bigger :: objset;
       Node e = n.right;
       
       //: bigger := "{}";
       while /*: inv "e ~= null & e : content &
	              (rtrancl_pt 
		      (% x y. x..Node.left = y) (n..Node.right) e) &
		      (n..Node.right..Node.subtree = 
		      bigger Un e..Node.subtree) &
		      (comment ''BiggerLInv''
		      (ALL x. x : bigger --> e..Node.v < x..Node.v)) &
		      (e : n..Node.right..Node.subtree)"
	     */
	   (e.left != null) {
	   //: bigger := "bigger Un {e} Un e..Node.right..Node.subtree";
	   e = e.left;
       }

       if (e.parent.left == e) {
	   e.parent.left = e.right;
       } else {
	   e.parent.right = e.right;
       }

       if (e.right != null) {
	   e.right.parent = e.parent;
       }

       e.parent = null;
       e.right = null;

       return e;
   }

   private static Node removeMax(Node n)
   /*: requires "theinvs & n ~= null & n : content & n..Node.left ~= null"
       modifies content, "Node.left", "Node.right", "Node.parent", 
                "Node.subtree"
       ensures "theinvs & content = old content - {result} & 
                result : old content & result ~= n &
		(ALL x. x : n..Node.left..Node.subtree --> 
		x..Node.v <= result..Node.v) &
		(ALL x. x : n..Node.right..Node.subtree -->
		x..Node.v >= result..Node.v)"
   */
   {
       //: private static ghost specvar smaller :: objset;
       Node e = n.left;
       
       //: smaller := "{}";
       while /*: inv "e ~= null & e : content &
	              (rtrancl_pt 
		      (% x y. x..Node.right = y) (n..Node.left) e) &
		      (n..Node.left..Node.subtree = 
		      smaller Un e..Node.subtree) &
		      (comment ''SmallerLInv''
		      (ALL x. x : smaller --> e..Node.v >= x..Node.v)) &
		      (e : n..Node.left..Node.subtree)"
	     */
	   (e.right != null) {
	   //: smaller := "smaller Un {e} Un e..Node.left..Node.subtree";
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

   private static void swap(Node toRemove, Node toAdd)
   /*: requires "toRemove ~= null & toRemove : content & 
                 toAdd ~= null & toAdd ~: content &
		 (comment ''LOPreS''
		 (ALL x. x : toRemove..Node.left..Node.subtree -->
		 x..Node.v < toAdd..Node.v)) &
		 (comment ''ROPreS''
		 (ALL x. x : toRemove..Node.right..Node.subtree -->
		 toAdd..Node.v <= x..Node.v)) &
		 (comment ''LOPreR''
		 (ALL x. toRemove : x..Node.left..Node.subtree -->
		 toAdd..Node.v < x..Node.v)) &
		 (comment ''ROPreR''
		 (ALL x. toRemove : x..Node.right..Node.subtree -->
		 x..Node.v <= toAdd..Node.v)) & theinvs"
       modifies content, root, "Node.subtree", "Node.parent", "Node.right",
                "Node.left"
       ensures "content = old content - {toRemove} Un {toAdd} &
                Node.v = (old Node.v) & theinvs"
   */
  {

       if (toRemove.parent == null) {
	   root = toAdd;
       } else {
	   if (toRemove.parent.left == toRemove) {
	       toRemove.parent.left = toAdd;
	   } else {
	       toRemove.parent.right = toAdd;
	   }
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
       modifies content
       ensures "(content = old content - {e}) & Node.v = (old Node.v)"
    */ 
   {
       remove_int(e);
   }
   
   private static void remove_int(Node e)
   /*: requires "e ~= null & e : content & theinvs"
       modifies content, "Node.subtree", root, "Node.parent", "Node.right",
                "Node.left"
       ensures "(content = old content - {e}) & Node.v = (old Node.v) & theinvs"
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
               Node r = removeMin(e);
               swap(e, r);
	   }
       }
   }
}
 
