public final class Node {
    public /*: claimedby List */ Node next;
    public /*: claimedby List */ Node prev;
    public /*: claimedby List */ boolean data;
}

public class List 
{
    private static Node first;
    /*:
     public static specvar content :: objset;
       vardefs "content == {x. x ~= null & (first,x) : {(v,w). v..next=w }^*  }";

     private static specvar reach :: "obj => obj => bool";
       vardefs "reach == (% a b. rtrancl_pt (% x y. x..Node.next=y) a b)";
       
     private static specvar reachParent :: "obj => obj => bool";
       vardefs "reachParent == (% a b. rtrancl_pt (% x y. x..Node.prev=y) a b)";

     invariant "first ~= null --> (ALL n. n..next ~= first)";
     
     // for MONA
     //invariant "tree [next]";
     //invariant prevDef: "ALL x y. prev x = y -->
     //                 (x ~= null & (EX z. next z = x) --> next y = x) &
     //                 (((ALL z. next z ~= x) | x = null) --> y = null)";


     invariant "ptree prev [next]";	
    */

    // BEGIN CHECKED USING TREE LOGIC    

   public static void insert(Node pos, Node n)
   /*: requires "n ~= null & pos : content & n ~: content"
       modifies content
       ensures " n : content"
   */
   {
      Node e = first;
      Node p = null;

      while   /*: inv "ptree prev [next] &
		       (reach e pos) &
		       (p ~= null --> (first,p) : {(x,y). x..next = y}^* & p..next = e) 
		       ";
	      */  
	  (e != pos) {
	  p = e;
	  e = e.next;
      }
      if (p == null) {
	 n.next = first;
	 first.prev = n;
	 first = n;
	 
      } else { 
	 p.next = n;
	 n.prev = p;
	 n.next = e;
	 if (e != null)
	     e.prev = n;
	 }
   }

   public static void remove(Node r)
   /*: 
     requires "r ~= null"
     modifies content
     ensures "content = old content - {r}"
    */
   {
      Node e = first;
      while
	   /*: inv "ptree prev [next]
	            & (first ~= null --> (ALL n. n..next ~= first))
	            & reach first e
		    & (r : content --> reach e r)
		    ";
	    */
	  (e != null && e != r) 
	  {
	      e = e.next;
	  }
      if (e != null) {
	 Node n = e.next;
	 Node p = e.prev;
	 if (n != null) {
	    n.prev = p;
	 }

	 if (p != null) {
	    p.next = n;
	 } else {
	    first = n;
	 }
	 e.prev = null;
	 e.next = null;
      }
   }

    public static void filter()
   /*: modifies content
       ensures "content = {x. x : old content & ~x..data}"
   */	
    {
      Node e = first;
      boolean nondet;
      while /*: inv "ptree prev [next]
	             & (first ~= null --> (ALL n. n..next ~= first))
	             & reach first e
	             & content = {x. x : old content & (x..data --> reach e x)} 
		    "; 
	    */
	 (e != null) {
	 Node n = e.next;
	 Node p = e.prev;
	 if (e.data) {
	    if (n != null) {
	       n.prev = p;
	    }
	    else {
	       first = n;
	    }
	    e.next = null;
	    e.prev = null;
	 } 
	 e = n;
      }
   }

   public static boolean contains(Node n)
   /*: ensures " result = ( n : content )"
   */
    {
      Node e = first;
      Node p;
      while   /*:  inv " ptree prev [next]
		         & (reach first e)
		         & (reach first n --> reach e n)
		  ";	     
              */
	  (e != null && e != n) {
	  //	  p = e.prev;	  
	  e = e.next;	  
      }
      return (e != null);
   }

   public static boolean containsParent(Node n)
   /*: ensures " result = ( n : content )"
   */
    {
      Node e = first;
      Node p;
      while   /*:  inv " ptree prev [next]
		         & (reachParent e first)
		         & (reachParent n first --> reachParent n e)
		  ";	     
              */
	  (e != null && e != n) {
	  e = e.next;	  
	  if (e != null)
	      p = e.prev;	  
      }
      return (e != null);
   }


    // END OF CHECKED USING TREE LOGIC

   public static void partition(Node root)
   {
      // assume "is_root root";
      
      Node p_true = null;
      Node p_false = null;
      Node e = root;
      boolean nondet;
      while (e != null) {
	 // havoc "nondet";
	 if (e.data) {
	    Node tmp = p_true;
	    p_true = e;
	    e = e.next;
	    p_true.next = tmp;
	    tmp = null;
	 } else {
	    Node tmp = p_false; 
	    p_false = e;
	    e = e.next;
	    p_false.next = tmp;
	    tmp = null;
	 }
      }
      
      //: assert "ALL v. (p_true,v) : {(x,y). x..next = y}^* & null ~= v --> v..data"; 
      // assert "is_root p_true";
      // assert "is_root p_false";

   }

   public static void partition2(Node root)
   {
      // assume "is_root root";
      // assume "tree [next]";
      //: assume " (root,null) : {(x,y). x..next = y}^* ";

      //: ghost specvar prev :: obj;
     
      Node p_true = null;
      Node p_false = null;
      Node e = root;
      boolean nondet;
      //: prev := "null";

      while /*: inv "next null = null &
	    ( (prev,null) : {(x,y). x..next = y}^*   ) &
	    ( (e,null) : {(x,y). x..next = y}^*   ) &
	    ( e ~= root --> prev ~= null) &
	    ( prev ~= null --> prev ~= e ) &
	    ( p_true ~= null | p_false ~=null -->  (p_true = prev | p_false = prev) & p_true ~= p_false ) &
	    ( p_true ~= null  -->  p_true ~= e ) &
	    ( p_false ~= null -->  p_false ~= e ) &
	    ( (p_true,null) : {(x,y). x..next = y}^*   ) &
            ( (p_false,null) : {(x,y). x..next = y}^*   )
	            "; */
	  (e != null) {
	 // havoc "nondet";
	 // prev := "e";
	 if (e.data) {
	    Node tmp = p_true;
	    p_true = e;
	    e = e.next;
	    p_true.next = tmp;
	    //: prev := "p_true";
	    tmp = null;
	 } else {
	    Node tmp = p_false; 
	    p_false = e;
	    e = e.next;
	    p_false.next = tmp;
	    //: prev := "p_false";
	    tmp = null;
	 }
      }
      
      // assert "ALL v. (p_true,v) : {(x,y). x..next = y}^* & null ~= v --> v..data"; 
      // assert "is_root p_true";
      // assert "is_root p_false";

   }

   public static void findPrev(Node x, Node y)
   {
      //: assume "(x,y) : {(x,y). x..next = y}^*";
      // assume "tree [next]";
      Node e = x;
      Node prev = null;

      while (e != y) {
	 prev = e;
	 e = e.next;
      }
   }

   public static void findPrev2(Node x, Node y)
   {
      //: assume "(x,y) : {(x,y). x..next = y}^*";
      // assume "(x,null) : {(x,y). x..next = y}^*";      
      // assume "(y,null) : {(x,y). x..next = y}^*";      
      // assume "tree [next]";
      
      Node e = x;
      Node prev = null;

      while  /*: inv "next null = null &
	      (x,y) : {(x,y). x..next = y}^* &
	      (x,e) : {(x,y). x..next = y}^* &
	      (e,y) : {(x,y). x..next = y}^* &
              (e ~= x --> prev ~= null) &
	      (prev ~= null -->(prev,y) : {(x,y). x..next = y}^*  ) &
	      (prev ~= null --> (x,prev) : {(x,y). x..next = y}^* & prev..next = e)
     	      
	    ";	   */
	  (e != y) {
	 prev = e;
	 e = e.next;
      }
      // assert "prev = y --> prev..next = y"; 
      //: assert " (x ~= y ) --> prev..next = y";
      // assert "(x,null) : {(x,y). x..next = y}^*";
   }

   public static void split(Node root, Node pos)
   {
      //: assume "ALL v1 v2. v1..next ~= null & v1 ~= v2 --> v1..next ~= v2..next";
      //: assume "root ~= pos";
      Node e = root;
      Node prev = null;

      while (e != pos && e != null) {
	 prev = e;
	 e = e.next;
      }
      
      if (prev != null) 
	 prev.next = null;
   
      //: assert "e = pos --> is_root pos";
   }

   public static void getLast(Node root)
   {
       //: assume "tree [next]";
      Node e = root;
      Node p = null;

      while /*:
	    inv "next null = null &
	         (root,e) : {(x,y). x..next = y}^* &
		 (p ~= null --> p..next = e) &
	         (p ~= null --> (root,p) : {(x,y). x..next = y}^* & p..next = e)";
	   */ (e != null) 
      {
	 p = e;
	 e = e.next;
      }
      if (p != null) p.next = null;
      //: assert "(root,p) : {(x,y). x..next = y}^*";
      //: assert " p..next = null";
   }

  public static void getLast2(Node root)
   {
      // assume "tree [next]"; 
       //: assume "(root,null) : {(x,y). x..next = y}^*"

      Node e = root;
      Node p = null;

      while /*:
              inv " next null = null &
              (root,e) : {(x,y). x..next = y}^* &
	      ((root,p) : {(x,y). x..next = y}^*) &
	      (p ~= null --> p..next = e) "
	   */ (e != null) 
      {
	 p = e;
	 e = e.next;
      }
      if (p != null) p.next = null;
      //: assert "(root,p) : {(x,y). x..next = y}^*";
      //: assert " p..next = null";
   }


   public static void removeLast(Node root)
   {
      //: assume "tree [next]";
      //: assume "(root,null) : {(x,y). x..next = y}^*"

      Node e = root;
      Node l = null;
      Node prev = null;

      while
	  /*: inv "next null = null &
	    (root,e) : {(x,y). x..next = y}^* &
	    (root,l) : {(x,y). x..next = y}^* &
	    (root,prev) : {(x,y). x..next = y}^* &
	    (prev ~= null --> prev..next = l) &
	    (l ~= null --> l..next = e) &
	    (root ~= l & l ~= null --> prev ~= null) &
	    (l = null --> root = e | root = null) &
            {x. (root,x) : {(x,y). x..next = y}^*} = old {x. (root,x) : {(x,y). x..next = y}^*}
	    ";
	    
	   */ (e != null) 
      {
	 prev = l;
	 l = e;
	 e = e.next;
      }

      if (root != l) {
	 prev.next = null;
      } 

      //: assert "(root,null) : {(x,y). x..next = y}^*";
      //: assert "root != l --> {x. (root,x) : {(x,y). x..next = y}^*} = old {x. (root,x) : {(x,y). x..next = y}^*} - {l}"
   }


   public static void removeLast2(Node root)
   {
      // assume "tree [next]";
      //: assume "(root,null) : {(x,y). x..next = y}^*"

      Node e = root;
      Node l = null;
      Node prev = null;

      while
	  /*: inv "next null = null &
	      (root,null) : {(x,y). x..next = y}^* &
              (root,e) : {(x,y). x..next = y}^* &
	      (root,l) : {(x,y). x..next = y}^* &
	      (root,prev) : {(x,y). x..next = y}^* &
	      ( prev ~= null --> prev..next = l ) &
	      ( l ~= null --> l..next = e ) &
	      ( root ~= l & l ~= null --> prev ~= null ) &
	      ( l = null --> prev = null & e = root ) &
	      ( {x. (root,x) : {(x,y). x..next = y}^*} = old {x. (root,x) : {(x,y). x..next = y}^*} )
	    ";
	    
	   */ (e != null) 
      {
	 prev = l;
	 l = e;
	 e = e.next;
      }

      if (root != l) {
	 prev.next = null;
      } 

      //: assert "(root,null) : {(x,y). x..next = y}^*";
      //: assert "root != l --> {x. (root,x) : {(x,y). x..next = y}^*} = old {x. (root,x) : {(x,y). x..next = y}^*} - {l}"
   }


   public static void remove2(Node n)
   /*: 
     requires "n ~= null"
     modifies content
     ensures "content = old content - {n}"
    */
   {
      Node e = first;
      Node prev = null;

      while
	   /*: inv "
	            (reach first e)
		    & (reach first null)
		    & (reach first prev)
		    & (reach e n | n ~: content)
		    & (prev ~= n )
		    & (prev ~= null --> prev..next = e)
		    & (prev = null --> e = first)
	           ";
	    */
	  (e != null && e != n) 
	  {
	      prev = e;
	      e = e.next;
	  }
      if (e != null) {
	 if (prev != null) {
	    prev.next = e.next;
	 } else {
	    first = first.next;
	 }
	 e.next = null;
      }      
   }

    public static void reverse(Node root)
    {
	Node first = root;
	// assume "is_root first";
	
      Node t, e;
      e = first;
      first = null;
      while (e != null) {
	 t = first;
	 first = e;
	 e = e.next;
	 first.next = t;
      }
      // assert "is_root first";
   }
   
}
 
