/* vkuncak, 12.07.2007: even if we add "False" to postcondition the 'add' or 'isEmpty' methods still verify.
 *                      Therefore, the invariants are most likely contradictory!
 */

/* Software Analysis and Verification project
 *
 * Tree.java
 * Created on June 29, 2007,
 *
 * Authors: Feride Cetin and Kremena Diatchka
 * 
 * Description:
 * A binary search tree whose leaves form a doubly linked list.
 * Each node has an integer value, and a pointer to its parent.
 * Each value inserted in the tree is inserted as a leaf.
 * The method of insertion ensures that each node has zero or two children. 
 *
 * Note: In this version all the methods verify but the class does not verify in the initial state.
 *
 * 
 */

class Node {
   public /*: claimedby Tree */ Node right;
   public /*: claimedby Tree */ Node left;
   public /*: claimedby Tree */ Node parent;
   public /*: claimedby Tree */ Node next;
   public /*: claimedby Tree */ Node prev;
   public /*: claimedby Tree */ int v;
}


class Tree
{
   private static Node root;

   /*: public static specvar nodes :: objset;
       private vardefs "nodes == 
	{x. x ~= null & (root,x) : {(u,v) . Node.left u = v | Node.right u = v}^* }";
	
       public static specvar content :: "int set";
       vardefs "content == {x. EX n. x = n..Node.v & n : nodes}"; 
  
       public static specvar internalNodes :: objset;
       vardefs  "internalNodes == {x. x : nodes &  (x..Node.left ~= null | x..Node.right ~= null)}";

	// Specification variables helping with nextLeaf

       public static specvar descendants :: "obj => objset";
       vardefs "descendants == (%x. {y. y ~=null & (x,y) : {(u,v). u..Node.left = v | u..Node.right = v}^*} - {x})"; 
       
       public specvar ancestors :: "obj => objset";
       public vardefs "ancestors ==
        (%x. {y. y ~= null & ((x,y) : {(u,v) . u..Node.parent = v}^*)})";

	public specvar leftNodes :: "obj => objset";
	vardefs "leftNodes == (%x. {y. y ~= null & (x,y) : {(u,v). u..Node.left = v}^* })";

	public static specvar splitNodes :: "obj => objset";
	vardefs "splitNodes == (%n. {s. s : (ancestors n) & 
				     s..Node.right ~: (ancestors n) &
				     s..Node.right ~= n })";

	// returns true if param1 is the first split node of param2
	public static specvar splitNode :: "obj => obj => bool";
	vardefs "splitNode == (%x y. x : (splitNodes y) & (ALL c. c : (descendants x) --> c ~: (splitNodes y)))";

       public static specvar isLeftChild :: "obj => bool";
       vardefs "isLeftChild == (%n. n..Node.parent..Node.left = n)";
       //vardefs "isLeftChild == (%n. (Node.left (Node.parent n)) = n)";

	// returns true if param2 is the leftmost leaf reached from param1
	public static specvar isSmallest :: "obj => obj => bool";
	vardefs "isSmallest == (%x y. y : (leftNodes x) & y ~: internalNodes)";

	public static specvar isSmallestFromRoot :: "obj => bool";
	vardefs "isSmallestFromRoot == (%x. isSmallest root x)";

	// returns true if param2 is next in the list after param1
	public static specvar nextLeaf :: "obj => obj => bool";
	vardefs "nextLeaf == (%x y. (x..Node.parent = null --> y = null) &
				    (x..Node.parent ~= null --> 
					(isLeftChild x --> (isSmallest (x..Node.parent..Node.right) y)) &
					(~ isLeftChild x --> 
						( (EX s. (splitNode s y) --> (isSmallest s y)) &
						  (~(EX s. (splitNode s y)) --> (y =null)) 
						)
					)
				    ) 
			     )";

	
	// End specification variables helping with nextLeaf
	
	invariant LeftNotRight: "ALL x y. x..Node.left ~= x..Node.right";

       invariant "tree [Node.left, Node.right]";

       invariant rootNotPointed: "root = null | 
				(ALL n. n..Node.left ~= root & 
				        n..Node.right ~= root & 
					n..Node.next ~= root & 
					n..Node.prev ~= root)"; 

       invariant rootParentless: "root ~= null --> root..Node.parent = null";

       invariant pointToNodes: "ALL x y. x ~= null & y ~= null & x : nodes & 
	          (x..Node.right = y | 
		   x..Node.left = y | 
		   x..Node.next = y |
		   x..Node.prev = y | 
		   x..Node.parent = y) --> y : nodes";

       invariant ParentFieldConstraint: "ALL x y. Node.parent x = y -->
                     (x ~= null --> ((y..Node.left = x | y..Node.right = x) & (y : internalNodes)))";

   */


   public static boolean isEmpty()
   /*: ensures "comment ''emptyPost'' result = (nodes = {})"
    */
   {
	boolean b = (root == null);
	//: noteThat "comment ''nodeIsEmpty'' b = (ALL x. x ~: nodes)";   
	return b;
   }
  
    public static Node findSmallestLeaf()
    /*:	ensures "comment ''findSmallest_post'' result = null | 
		(result : nodes & result ~: internalNodes & (isSmallestFromRoot result))"
    */
   {
       Node n = root;
      
	if(n == null)
		return null;

        while 
       /*: inv "comment ''fsl_notNull'' n ~= null &
		comment ''fsl_notLeaf'' n : internalNodes &
		comment ''fsl_reachableLeft'' (root, n) : {(u,v). u..Node.left = v}^*"
        */
	(!isLeaf(n))
       {
               n = n.left;
       }
	//: assert "n ~= null";
       return n;
   }

   public static boolean isLeaf(Node n) 
   /*: requires "n ~= null" 
       ensures "result = (n : nodes & n ~: internalNodes)"
    */
   {
	return (n.left == null && n.right == null);
   }


   /*   Updates the pointers in the linked list after the node n has 
	been inserted in the list.
    */
   public static void leafUpdate (Node n)
   /*:  requires "comment ''leafUpdate_pre'' (n ~= null & n..Node.parent : nodes & n..Node.parent : internalNodes  & 
						nodes ~= {} & content ~= {} & n:nodes & n ~: internalNodes)"
  	 ensures "comment ''leafUpdate_post'' (nextLeaf n (n..Node.next))"
   */
   {
        Node p = n.parent;
	
	if(p.right == n)
	  {
		n.next = p.next;
		if(p.next != null)
			p.next.prev = n;
		n.prev = p.left;
		//: assert "comment ''NextNull'' (p..Node.parent = null --> p..Node.next = null)";
		//: assert "comment ''isRight'' ( ~ (isLeftChild n))";
		//: assert "comment ''nRight'' (nextLeaf n (n..Node.next))";
	  }
	else
	  {
	    	n.next = p.right;
	    	n.prev = p.prev;
	    	if(p.prev != null)
	    		p.prev.next = n;
		
		//: assert "comment ''isLeft'' (isLeftChild n)";
		//: assert "comment ''nLeft'' (nextLeaf n (n..Node.next))";
	  }
    }


   public static void add(int v) 
      /*: requires "v ~: content"
          modifies content, nodes, internalNodes
 	  ensures "comment ''add_post'' (content = old content Un {v})";
      */
   {
      Node temp = new Node();
      Node e = new Node();
      e.v = v;

      if(isEmpty()) {
         root = e;
         e.next = null;
         e.prev = null;
         return;     	  
      }

      Node n = root, p = null;
      boolean wentLeft = false;
      while  
      /*: inv "n : nodes"
       */
      (n != null){
    	  p = n;
    	  if (v < n.v) {
    		  wentLeft = true;
    		  n = n.left;
    	  } else {
    		  wentLeft = false;
    		  n = n.right;
    	  }
      }


      //: assert "comment ''add_pLeaf'' p : nodes & p ~: internalNodes";
      //: assert "False";     
      e.parent = p;
      temp.parent = p;

      if (wentLeft) {
    	  p.left = e;
    	  p.right = temp;
    	  temp.v = p.v ;
    	  p.v = e.v;
      }

      else {
        p.right = e;
		p.left = temp;
		temp.v = p.v ;
      }
      leafUpdate(e);
      leafUpdate(temp);
      p.next = null;
      p.prev = null;

   }

  public static Node getRoot() 
  /*: 	
	ensures "isSmallestFromRoot result"
   */
  {
	  return root;
  }
  
}

