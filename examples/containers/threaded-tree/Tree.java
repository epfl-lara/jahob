public final class Node {
   public /*: claimedby Tree */ Node right;
   public /*: claimedby Tree */ Node left;
   public /*: claimedby Tree */ Node next;
   public /*: claimedby Tree */ int v;
}
public class Tree
{
   private static Node root;
   private static Node first;

   /*: public static specvar content :: objset;
       private vardefs "content == 
        {x. rtrancl_pt (% x y. x..left = y | x..right = y) root x}";
   
       invariant "tree [left, right]";
   
       invariant "root ~= null --> (ALL n. n..left ~= root & n..right ~= root)";
       invariant "first ~= null --> (ALL n. n..next ~= first)";
       invariant "(first,root) : {(x,y). x..next = y}^*";

       invariant "ALL x y. x ~= null & y ~= null & (x..right = y | x..left = y) --> y : content";
       invariant "ALL x y. x..next = y <->
          (x ~= null -->
	    (x..right = null --> 
               ((EX z. z..left = x) --> y..left = x) &
	       ((ALL z. z..left ~= x) --> 
	           (((ALL z. (left z, x) ~: {(x1,x2). x1..right = x2}^*)) & (y = null) | 
		   (left y, x) : {(x1,x2). x1..right = x2}^*))) &
	    (x..right ~= null -->
	       y..left = null & y ~= null & (right x, y) : {(x1, x2). x1..left = x2}^*)) &
	  (x = null --> y = null)";
       //invariant "ALL x. x : content & x ~= null & x..next ~= null --> x..v <= x..next..v";
       
   */
    
   public static void add(Node e) 
      /*: 
	requires "e ~: content"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      Node pred = null;
      Node succ = null;
      boolean wentLeft = false;
      while (n != null) {
	 p = n;
	 if (e.v < n.v) {
	    wentLeft = true;
	    succ = n;
            n = n.left;
	 } else {
	    wentLeft = false;
	    pred = n;
	    n = n.right;
	 }
      }
      if (p == null) {
	 root = e;
      } else {
	 if (wentLeft) {
            p.left = e;
	 } else {
            p.right = e;
	 }
      }
      e.next = succ;
      if (pred != null) pred.next = e;
   }
    public static void add2(Node e) 
      /*: 
	requires "e ~: content"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      /*:
	specvar root_left_star :: objset;
	specvar pred_left_star :: objset;
	vardefs "root_left_star == {x. (root,x) : {(x1,x2). x1..left = x2}^*}"
	vardefs "pred_left_star == {x. (pred..right,x) : {(x1,x2). x1..left = x2}^*}"
      */
      Node n = root, p = null;
      Node pred = null;
      boolean wentLeft = false;
      while 
      (n != null) {
	 /*
	   //track(root_left_star);
	   track(pred_left_star);
	  */
	 p = n;
	 if (e.v < n.v) {
	    wentLeft = true;
            n = n.left;
	 } else {
	    wentLeft = false;
	    pred = n;
	    n = n.right;
	 }
      }
      if (p == null) {
	 root = e;
      } else {
	 if (wentLeft) {
            p.left = e;
	 } else {
            p.right = e;
	 }
      }
      
      if (pred != null) {
	 e.next = pred.next;
	 pred.next = e;
      } else {
	 e.next = p;
      }
   }
   public static void add_annotated(Node e) 
      /*: 
	requires "e ~: content"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      Node pred = null;
      Node succ = null;
      boolean wentLeft = false;
      while 
	 /*: inv "((p = null & n = null) --> root = null) &
                   p : content &
                   n : content &
                   (p ~= null & wentLeft --> p..Node.left = n) &
                   (p ~= null & ~wentLeft --> p..Node.right = n) &
		   e ~= null &
		   succ : content &
		   pred : content &
		   ((wentLeft | p = null) <-> succ = p) &
		   (~wentLeft <-> pred = p) &
		   (pred = null --> (root, p) : {(x1,x2). x1..left = x2}^*) &
		   (pred = null --> (root, n) : {(x1,x2). x1..left = x2}^*) &
		   ((root, p) : {(x1,x2). x1..left = x2}^* & wentLeft --> pred = null) &
		   (n ~= null & (root, n) : {(x1,x2). x1..left = x2}^* --> pred = null) &
		   (pred ~= null --> (pred..right,n) : {(x1,x2). x1..left = x2}^*) &
		   (pred ~= null & p ~= pred --> (pred..right,p) : {(x1,x2). x1..left = x2}^*) &
		   (succ = null --> (root, p) : {(x1,x2). x1..right = x2}^*) &
		   (succ = null --> (root, n) : {(x1,x2). x1..right = x2}^*) &
		   ((root, p) : {(x1,x2). x1..right = x2}^* & ~wentLeft --> succ = null) &
		   (n ~= null & (root, n) : {(x1,x2). x1..right = x2}^* --> succ = null) &
		   (succ ~= null --> (succ..left,n) : {(x1,x2). x1..right = x2}^*) &
		   (succ ~= null & p ~= succ --> (succ..left,p) : {(x1,x2). x1..right = x2}^*) &
		   (pred ~= null --> pred..v <= e..v) &
		   (succ ~= null --> e..v < succ..v)"
             */
      (n != null) {
	 p = n;
	 if (e.v < n.v) {
	    wentLeft = true;
	    succ = n;
            n = n.left;
	 } else {
	    wentLeft = false;
	    pred = n;
	    n = n.right;
	 }
      }
      if (p == null) {
	 root = e;
      } else {
	 if (wentLeft) {
            p.left = e;
	 } else {
            p.right = e;
	 }
      }
      e.next = succ;
      if (pred != null) pred.next = e;
      else first = e;
      //: noteThat "content = old content Un {e}"
   }
    public static void add_annotated2(Node e) 
      /*: 
	requires "e ~: content"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      Node pred = null;
      boolean wentLeft = false;
      while 
	 /*: inv "((p = null & n = null) --> root = null) &
                   p : content &
                   n : content &
                   (p ~= null & wentLeft --> p..Node.left = n) &
                   (p ~= null & ~wentLeft --> p..Node.right = n) &
		   e ~= null &
		   pred : content &
		   (~wentLeft <-> pred = p) &
		   (pred = null --> (root, p) : {(x1,x2). x1..left = x2}^*) &
		   (pred = null --> (root, n) : {(x1,x2). x1..left = x2}^*) &
		   ((root, p) : {(x1,x2). x1..left = x2}^* & wentLeft --> pred = null) &
		   (n ~= null & (root, n) : {(x1,x2). x1..left = x2}^* --> pred = null) &
		   (pred ~= null --> (pred..right,n) : {(x1,x2). x1..left = x2}^*) &
		   (pred ~= null & p ~= pred --> (pred..right,p) : {(x1,x2). x1..left = x2}^*)"
             */
      (n != null) {
	 p = n;
	 if (e.v < n.v) {
	    wentLeft = true;
            n = n.left;
	 } else {
	    wentLeft = false;
	    pred = n;
	    n = n.right;
	 }
      }
      if (p == null) {
	 root = e;
      } else {
	 if (wentLeft) {
            p.left = e;
	 } else {
            p.right = e;
	 }
      }
      
      if (pred != null) {
	 e.next = pred.next;
	 pred.next = e;
      } else {
	 e.next = p;
	 first = e;
      }
   }

   public static void remove_annotated(Node e)
    /*: requires "e ~= null" 
      modifies content 
      ensures " True " 
     */
    {
	/* ghost specvar oldparent :: obj; 
	   noteThat "(EX x. x ~= null & x : nodes root)";
	*/

	Node p = null;
	Node n = root;
	Node pred = null;
	boolean wentLeft = false;

	while /*: inv " 
		((p = null & n = null) --> root = null) &
		p : content &
		n : content &
		(p ~= null & wentLeft --> p..Node.left = n) &
		(p ~= null & ~wentLeft --> p..Node.right = n) &
	        pred : content &
		(~wentLeft <-> pred = p) &
		(pred = null --> (root, p) : {(x1,x2). x1..left = x2}^*) &
		(pred = null --> (root, n) : {(x1,x2). x1..left = x2}^*) &
		((root, p) : {(x1,x2). x1..left = x2}^* & wentLeft --> pred = null) &
		(n ~= null & (root, n) : {(x1,x2). x1..left = x2}^* --> pred = null) &
		(pred ~= null --> (pred..right,n) : {(x1,x2). x1..left = x2}^*) &
		(pred ~= null & p ~= pred --> (pred..right,p) : {(x1,x2). x1..left = x2}^*) &
		(n ~= root --> ( n = p..Node.left | n = p..Node.right ) )
		";
	      */

	    /*
	      (root ~= null --> n ~= null  )
	      (smt_reach first n) 
	    */

	    ( n != null && n != e) {
	    wentLeft = (e.v < n.v);
	    // noteThat " reach (n..left) e | reach (n..right) e ";
	    if (wentLeft) {
		// noteThat " reach (n..left) e";
		p = n;
		n = n.left;
		// noteThat " ";
	    } else {
		// noteThat " reach (n..right) e";
		pred = n;
		p = n;
		n = n.right;
	    }
	    // noteThat " reach n e ";
	    // noteThat " n ~= null "; 
	}

	// assume "False";
	// noteThat "n = e";

	if (n == null) return;

	//: noteThat "n = e";
	Node newSubroot = null;
	Node newSubrootParent = null;

	if (n.left != null ) {
	    newSubroot = n.left;
	    while  /*: inv " 
		    (newSubrootParent ~= null --> newSubrootParent..Node.right = newSubroot) &
		    (newSubrootParent = null --> newSubroot = n..Node.left) &
		    (newSubroot : content) &
		    (newSubrootParent ~= null --> newSubrootParent : content) &
		    newSubroot ~= null
		    ";
		  */
		(newSubroot.right != null) {
		newSubrootParent = newSubroot;
		newSubroot = newSubroot.right;
	    }
	    pred = newSubroot;
	}

	// assume "False";

	if (n.left != null && n.right != null) {
	    if (newSubrootParent != null) {
		newSubrootParent.right = newSubroot.left;
		newSubroot.left = n.left;
	    } else {
		//: assume "False";
	    }
	    newSubroot.right = n.right;
	} else if (n.left == null) {
	    //: assume "False";
	    newSubroot = n.right;
	} else if (n.right == null) {
	    //: assume "False";
	    newSubroot = n.left;
	}

	// assume "False";

	
	// noteThat "n ~= null --> n = e";
	// noteThat "n = e --> n : smt_content";
	if ( pred != null ) {
	    pred.next = n.next;
	    // noteThat "pred..Node.next != n";
	}
	else  {
	    //: assume "False";
	    first = n.next;
	    // noteThat "first != n";
	}
	// noteThat "~(smt_reach first n)";
	// noteThat "n ~: smt_content";
	// assume "False";
	
	n.left = null;
	n.right = null;
	n.next = null;
	
	if (p == null) {
	    root = newSubroot;
	    //: assume "False";
	} else if (wentLeft) {
	    p.left = newSubroot;
	    // noteThat "p..Node.left ~= n ";
	} else {
	    // assume "False";
	    p.right = newSubroot;
	    // noteThat "p..Node.right ~= n ";
	}

	// noteThat "~(reach root n)";
	// noteThat "~(reach root e)";
	// noteThat "n = e --> content = old content - {n}";
	// noteThat "n = e --> smt_content = old smt_content - {n}";
	// assume "False";
	// checkpoint

	/* assume "ALL x y. x..next = y <->
          (x ~= null --> 
	    (x..right = null -->  
               ((EX z. z..left = x) --> y..left = x) & 
	       ((ALL z. z..left ~= x) -->  
	           (((ALL z. (left z, x) ~: {(x1,x2). x1..right = x2}^*)) & (y = null) |  
		   (left y, x) : {(x1,x2). x1..right = x2}^*))) & 
	    (x..right ~= null --> 
	       y..left = null & y ~= null & (right x, y) : {(x1, x2). x1..left = x2}^*)) & 
	  (x = null --> y = null)"; 
	*/
    }
}