public final class Node {
   public /*: claimedby Tree */ Node right;
   public /*: claimedby Tree */ Node left;
   public /*: claimedby Tree */ Node next;
    public /*: claimedby Tree */ Node parent;
   public /*: claimedby Tree */ int v;
}
public class Tree
{
   private static Node root;
   private static Node first;

   /*: 
       public static specvar content :: objset;
       // private vardefs " content == 
       //         {x. rtrancl_pt (% x y. x..next = y ) first x}";
	       
       //       public ghost specvar parent :: "obj => obj";
       
       private vardefs " content == 
                         {x. rtrancl_pt (% x y. x..left = y | x..right = y) root x}";


       static specvar reach :: "obj => obj => bool"
       vardefs "reach == (% x y. rtrancl_pt (% a b. a..left = b | a..right = b) x y)";
       
       static specvar smt_reach :: "obj => obj => bool"
       vardefs "smt_reach == (% x y. rtrancl_pt (% a b. a..next = b ) x y)"; 


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
	
	invariant  "parent null = null"
	invariant  "left null = null"
	invariant  "right null = null"

       
       invariant "root ~= null --> (ALL n. n..left ~= root & n..right ~= root)";
       invariant "first ~= null --> (ALL n. n..next ~= first)";
       invariant "(root,first) : {(x,y). x..left = y}^*";
       
       invariant "root ~= null --> first ~= null & first..left = null";
       invariant "smt_reach first null";

       invariant "ptree parent [left, right]";

       invariant "ALL x y. x ~= null & y ~= null & (x..right = y | x..left = y) --> y : content";
       invariant "ALL x y. x ~= null & y ~= null & x..Node.next = y --> y : content";
       
       invariant "ALL x y. smt_reach x y & x ~= null & y ~= null & x ~= y --> x..v < y..v";
       invariant "ALL x y. x..v = y..v --> x = y"; 

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

       //some not so gut invariants
       invariant "(first,root) : {(x,y). x..next = y}^*";


   */

    
       /*
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
	 /*: inv " ptree parent [left, right] &
	           ((p = null & n = null) --> root = null) &
                   p : content &
                   n : content &
                   (p ~= null & wentLeft --> p..Node.left = n) &
                   (p ~= null & ~wentLeft --> p..Node.right = n) &
		   e ~= null &
		   succ : content &
		   pred : content &
		   ((wentLeft | p = null) <-> succ = p) &
		   (~wentLeft <-> pred = p) &
		   (p ~= null & pred = null --> (root, p) : {(x1,x2). x1..left = x2}^*) &
		   (pred = null --> (root, n) : {(x1,x2). x1..left = x2}^*) &
		   (pred ~= null --> (pred..right,n) : {(x1,x2). x1..left = x2}^*) &
		   (pred ~= null & p ~= pred --> (pred..right,p) : {(x1,x2). x1..left = x2}^*) &
		   (p ~= null & succ = null --> (root, p) : {(x1,x2). x1..right = x2}^*) &
		   (succ = null --> (root, n) : {(x1,x2). x1..right = x2}^*) &
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
	 if ( n != null )
	     n.parent = p;
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
      e.parent = p;
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


    public static boolean member(Node e)
    /*: requires "e ~= null" 
        ensures " result = (e : content) " 
    */
    {
	Node p = null;
	Node n = root;
	Node pred = null;
	Node succ = null;
	boolean wentLeft = false;

	//: noteThat "ALL x. x..left : content & x..left ~= null --> smt_reach (x..left) x";
        //: noteThat "ALL x. smt_reach first x --> smt_reach x (x..right)";
	//: noteThat "(first,root) : {(x,y). x..next = y}^*";

	while /*: inv "  ptree parent [left, right] &
		p : content &
		n : content &
	        pred : content &
		succ : content &

		(first,root) : {(x,y). x..next = y}^* &
		((root, p) : {(x1,x2). x1..left = x2}^* & wentLeft --> pred = null) &
		(n ~= null & (root, n) : {(x1,x2). x1..left = x2}^* --> pred = null) &
		((root, p) : {(x1,x2). x1..right = x2}^* & ~wentLeft --> succ = null) &
		(n ~= null & (root, n) : {(x1,x2). x1..right = x2}^* --> succ = null) &	


		(ALL x. x..left : content & x..left ~= null --> smt_reach (x..left) x) & 
		(ALL x. x : content --> smt_reach x (x..right)) &
		( (pred ~= null | succ ~= null) --> ( pred ~= succ ) ) &
		(null..next = null) &
		
		((p = null & n = null) --> root = null) &
		(p ~= null & wentLeft --> p..Node.left = n) &
		(p ~= null & ~wentLeft --> p..Node.right = n) &
		(p = null --> n = root ) &
		(~wentLeft <-> pred = p) &
		(p ~= null --> (wentLeft <-> succ = p) ) &
		(p ~= null --> (( (p..v < n..v) --> smt_reach p n ) | ( (p..v >= n..v) --> smt_reach n p) ) ) &
		
		(wentLeft --> (e..Node.v < p..Node.v )  ) &
		(~wentLeft & p ~= null --> ( p..Node.v < e..Node.v )  )  &
		(wentLeft & n ~= null --> smt_reach n p ) &
		(wentLeft & n ~= null & p ~= null --> ~(smt_reach p n) ) &
		(wentLeft & n..Node.left = null & pred ~= null & n ~= null --> pred..Node.next = n ) & 		   
		(~wentLeft & n..Node.right = null & succ ~= null & n ~= null --> n..Node.next = succ ) &
	
		(ALL x y. smt_reach x y & x ~= null & y ~= null & x ~= y --> x..v < y..v) &
		(ALL x. smt_reach first x  & x ~= null & x..next = null & e..Node.v > x..v --> e ~: content) &		
		(ALL x y. ( x : content & x..next = y & x..v < e..Node.v & y..v > e..Node.v & y ~= null 
		              & x ~=null ) --> e ~: content) &
		(ALL x. x : content & x..next = null & x ~= null & x..v < e..v --> e ~: content) &

		(pred = null --> (root, p) : {(x1,x2). x1..left = x2}^*) &
		(succ = null --> (root, p) : {(x1,x2). x1..right = x2}^*) &
		(pred = null --> (root, n) : {(x1,x2). x1..left = x2}^*) &
		(succ = null --> (root, n) : {(x1,x2). x1..right = x2}^*) &
		(pred ~= null --> (pred..right,n) : {(x1,x2). x1..left = x2}^*) &
		(succ ~= null --> (succ..left,n) : {(x1,x2). x1..right = x2}^*) &
		(pred ~= null & p ~= pred --> (pred..right,p) : {(x1,x2). x1..left = x2}^*) &
		(succ ~= null & p ~= succ --> (succ..left,p) : {(x1,x2). x1..right = x2}^*) &		
		(pred ~= null & n ~= null & n..Node.left = null --> pred..Node.next = n ) &
		(succ ~= null & ~wentLeft & n..Node.right = null & n ~= null --> n..Node.next = succ ) &		
		(pred ~= null --> smt_reach pred n) &
		(pred ~= null --> smt_reach pred succ) &
		(succ ~= null & n ~= null  --> smt_reach n succ ) &
		(pred ~= null & e..v < pred..v --> e ~: content ) &
		(succ ~= null & e..v >= succ..v --> e ~: content ) &
		(pred ~= null --> pred..v < e..v) &
		(succ ~= null --> e..v < succ..v) &
		
		(n ~= null & (root, n) : {(x1,x2). x1..right = x2}^* --> succ = null) &
		(n ~= root --> ( n = p..Node.left | n = p..Node.right ) ) &
		(n ~= null --> (smt_reach first e | e ~: content)) &		
		
		(first ~= null & n ~= null --> first..Node.v <= n..Node.v) &
		(e..Node.v < first..Node.v --> e ~: content ) &

		(root = null --> n = null) &
		(root = n & n != e --> root ~= e) &
		(root ~=n --> e ~= root ) &
		(root ~= null & root..Node.right = null --> root..Node.next = null) &
		(root ~= null & root..Node.right ~= null  --> root..Node.next != null) &
	
		( p ~= null --> p ~= e )

		";
	      */

	    
	    ( (n != null) && (n != e) ) {
	    wentLeft = (e.v < n.v);
	    if (wentLeft) {
		succ = n;
		p = n;
		n = n.left;
	    } else {
		pred = n;
		p = n;
		n = n.right;
	    }
	    n.parent = pred;
	}

	//: noteThat "ALL x. x..left : content & x..left ~= null --> smt_reach (x..left) x";
        //: noteThat "ALL x. x : content --> smt_reach x (x..right)";
	
	if (n == e) {
	    return true;
	}
	else {
	    //: noteThat " wentLeft & p ~= null --> p = succ & (pred ~= null --> pred..next = p)"; 
	    //: noteThat " ~wentLeft & p ~= null --> p = pred & (succ ~= null --> p..next = succ)";
	    //: noteThat "pred ~= null --> pred..next = succ";
	    return false;
	}

    }


   public static void remove_annotated(Node e)
   /*: requires "e ~= null" 
       modifies content
       ensures " e ~: content " 
     */
    {
	Node p = null;
	Node n = root;
	Node pred = null;
	Node succ = null;
	boolean wentLeft = false;

	//: noteThat "ALL x. x..left : content & x..left ~= null --> smt_reach (x..left) x";
        //: noteThat "ALL x. x : content --> smt_reach x (x..right)";
	//: noteThat "(first,root) : {(x,y). x..next = y}^*";

	// assume "False";

	while /*: inv " 
		p : content &
		n : content &
	        pred : content &
		succ : content &

		(first,root) : {(x,y). x..next = y}^* &
		(ALL x. x..left : content & x..left ~= null --> smt_reach (x..left) x) & 
		(ALL x. x : content --> smt_reach x (x..right)) &
		( (pred ~= null | succ ~= null) --> ( pred ~= succ ) ) &
		
		((p = null & n = null) --> root = null) &
		(p ~= null & wentLeft --> p..Node.left = n) &
		(p ~= null & ~wentLeft --> p..Node.right = n) &
		(p = null --> n = root ) &

		(~wentLeft <-> pred = p) &
		(p ~= null --> (wentLeft <-> succ = p) ) &

		(pred = null --> (root, p) : {(x1,x2). x1..left = x2}^*) &
		(pred = null --> (root, n) : {(x1,x2). x1..left = x2}^*) &
		((root, p) : {(x1,x2). x1..left = x2}^* & wentLeft --> pred = null) &
		(n ~= null & (root, n) : {(x1,x2). x1..left = x2}^* --> pred = null) &
		(pred ~= null --> (pred..right,n) : {(x1,x2). x1..left = x2}^*) &
		(pred ~= null & p ~= pred --> (pred..right,p) : {(x1,x2). x1..left = x2}^*) &
		(n ~= root --> ( n = p..Node.left | n = p..Node.right ) ) &
		
		(null..next = null) &
		(p ~= null --> (( (p..v < n..v) --> smt_reach p n ) | ( (p..v >= n..v) --> smt_reach n p) ) ) &
		(pred ~= null & n ~= null & n..Node.left = null --> pred..Node.next = n ) &
		(ALL x y. smt_reach x y & x ~= null & y ~= null --> x..v <= y..v) &
		
		(pred ~= null --> smt_reach pred n) &
		(succ ~= null & n ~= null  --> smt_reach n succ ) &

		(wentLeft --> (e..Node.v < p..Node.v )  ) &
		(p ~= null & ~wentLeft --> ( p..Node.v < e..Node.v )  )  &
		(wentLeft & n ~= null --> smt_reach n p ) &
		(first ~= null & n ~= null --> first..Node.v <= n..Node.v) &
		(n ~= null --> (smt_reach first e | e ~: content)) &
		(e..Node.v < first..Node.v --> e ~: content )
 
		& (ALL x. smt_reach first x  & x ~= null & x..next = null & e..Node.v > x..v --> e ~: content) 		
		& (ALL x y. ( x : content & x..next = y & x..v < e..Node.v & y..v > e..Node.v & y ~= null 
		              & x ~=null ) --> e ~: content) 
		& (root = null --> n = null)
		& (wentLeft & p ~= null & n ~= null --> ~(smt_reach p n) ) &
		
		((pred ~= null & e..v < pred..v) --> e ~: content ) &
		((succ ~= null & e..v >= succ..v) --> e ~: content ) &

		(succ = null --> (root, p) : {(x1,x2). x1..right = x2}^*) &
		(succ = null --> (root, n) : {(x1,x2). x1..right = x2}^*) &
		((~wentLeft & n..Node.right = null & succ ~= null & n ~= null) --> n..Node.next = succ ) &
		(n ~= null & (root, n) : {(x1,x2). x1..right = x2}^* --> succ = null) &
		(succ ~= null --> (succ..left,n) : {(x1,x2). x1..right = x2}^*) &
		(succ ~= null & p ~= succ --> (succ..left,p) : {(x1,x2). x1..right = x2}^*) &
		(pred ~= null --> pred..v < e..v) &
		(succ ~= null --> e..v < succ..v) &
	 	
		((root = n & n != e) --> root ~= e) &
		((n ~= root --> e ~= root )  ) &
	


		((root ~= null & root..Node.right = null ) --> root..Node.next = null) &
		((root ~= null & root..Node.right ~= null ) --> root..Node.next != null) &
		((~wentLeft & n..Node.right = null & succ ~= null & n ~= null) --> n..Node.next = succ ) &
		((wentLeft & n..Node.left = null & pred ~= null & n ~= null) --> pred..Node.next = n ) 		   

		& ( p ~= null --> p ~= e )

		";
	      */

	    /*
		(ALL x y. smt_reach x y & x ~= null & y ~= null & x..next = y --> x..v < y..v) &	     

	    */

	    ( n != null && n.v != e.v ) {
	    wentLeft = (e.v < n.v);
	    if (wentLeft) {
		p = n;
		succ = n;
		n = n.left;
	    } else {
		pred = n;
		p = n;
		n = n.right;
	    }
	}

	// assume "False";
	// noteThat "n != e --> n = null";

	if (n == null) {
	    //: noteThat "pred ~= null --> pred..next = succ"
	    //: noteThat "pred = null --> succ = first"
	    // noteThat "( (p ~= null & p..Node.right = null & e..Node.v > p..Node.v) --> p..Node.next = succ  )";
	    // noteThat "((~wentLeft & n..Node.right = null & succ ~= null ) --> n..Node.next = succ )";
	    //: noteThat "( (wentLeft & p ~= null) --> ( e..Node.v < p..Node.v & ( smt_reach e p | e ~: content)  ) )";
	    //: noteThat "( (~wentLeft & p ~= null) -->( e..Node.v > p..Node.v & ( smt_reach p e | e ~: content)  ) )";
	    //: noteThat "n ~= root";

	    return;
	}

	// noteThat "n = e";
	//: assume "False";
	
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
	    // assume "False";
	    newSubroot = n.left;
	}

	// assume "False";
	if ( pred != null ) {
	    pred.next = n.next;
	}
	else  {
	    // assume "False";
	    first = n.next;
	    // noteThat "first != n";
	}
	// assume "False";
	
	n.left = null;
	n.right = null;
	n.next = null;
	
	if (p == null) {
	    root = newSubroot;
	    // assume "False";
	} else if (wentLeft) {
	    p.left = newSubroot;
	    // noteThat "p..Node.left ~= n ";
	} else {
	    // assume "False";
	    p.right = newSubroot;
	    // noteThat "p..Node.right ~= n ";
	}


    }
}
