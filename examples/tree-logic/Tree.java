public class Tree
{
   private static Node root;
   
   /*: public static specvar content :: objset;
       private vardefs "content == 
         {x. x = null | root ~= null & rtrancl_pt (% x y. x..Node.parent = y) x root}";
         //{x. rtrancl_pt (% x y. x..Node.right = y | x..Node.left = y) root x}";
   
       static specvar reach :: "obj => obj => bool"
       vardefs "reach == (% x y. rtrancl_pt (% a b. a..left = b | a..right = b) x y)";

       static specvar parentReach :: "obj => obj => bool"
       vardefs "parentReach == (% x y. rtrancl_pt (% a b. a..parent = b) x y)";

       invariant "ptree parent [left, right]";

       invariant "root..parent = null";
   
       invariant "ALL x y. y ~= null & (x..Node.parent = y) --> x : content";

   */
    

   public static void add(Node e, int v) 
      /*: 
	requires "e ~: content"
	modifies content
	ensures "True"//"content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      boolean wentLeft = false;
      while (n != null) {
	 p = n;
	 if (v < n.v) {
	    wentLeft = true;
            n = n.left;
	 } else {
	    wentLeft = false;
	    n = n.right;
	 }
      }
      e.v = v;
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

   public static void leftRotation(Node e) 
   /*: 
        requires "e : content & e ~= null "
        modifies content
	ensures "True"
	//ensures " e..Node.parent = (old e)..Node.right & e : content";
   */ 
    {
	Node lch=e.left, rch=e.right, rlch = null, par=e.parent;
	if ( lch != null) 
	    lch.parent = e;
	if ( rch != null) {
	    rch.parent = e;
	    rlch = rch.left;
	    if ( e == root ) {
		root = rch;
		rch.parent = null;
	    }
	    else { 
		if ( e.v == 0 ) // 1 meaning is right child
		    par.right = rch;
		else
		    par.left = rch;
		rch.parent = par;
	    }
	    rch.left = e;
	    ////:noteThat "reach rch e";
	    e.parent = rch;
	    e.right = rlch;
	    if (rlch != null)
		rlch.parent = e;	    
	}
	////:assert "reach rch e | rch = null";
	////:assert "reach e rlch | rlch = null";

	////:assert "reach e rch --> rch = null";
	////:assert "reach e rch";
    }

   public static void addAnnot(Node e, int v) 
      /*: 
	requires "e ~: content"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      boolean wentLeft = false;
      while /*: inv "ptree parent [left, right] &
	            ((p = null & n = null) --> root = null) &
                     (p : content) &
                     (n : content) &
                     (p ~= null & wentLeft --> p..Node.left = n) &
                     (p ~= null & ~wentLeft --> p..Node.right = n) &
		      e ~= null &
		      e ~: content"
	    */
          (n != null) {
	 p = n;
	 if (v < n.v) {
	    wentLeft = true;
            n = n.left;
	 } else {
	    wentLeft = false;
	    n = n.right;
	 }
      }
      e.v = v;
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
   





   // The code below is just for debugging
   
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
}
 
