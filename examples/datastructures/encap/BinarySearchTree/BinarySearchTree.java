public /*: claimedby BinarySearchTree */ final class Node {
    public Node left;
    public Node right;
    public Node parent;
    public int v;

    /*: 
      public ghost specvar subtree :: "int set" = "{}";
    */
}

public class BinarySearchTree
{
    private static Node root;
   
    /*:
      public static specvar content :: "int set";
      vardefs "content == root..subtree";

      static ghost specvar nodes :: objset = "{}";

      invariant RootNodesInv: "root ~= null --> root : nodes";

      invariant LeftNodesInv: 
      "ALL x. x : nodes & x..left ~= null --> x..left : nodes";

      invariant RightNodesInv: 
      "ALL x. x : nodes & x..right ~= null --> x..right : nodes";

      invariant ParentNodesInv: 
      "ALL x. x : nodes & x..parent ~= null --> x..parent : nodes";

      invariant RootInjInv: 
      "ALL x. x : nodes & root ~= null --> x..left ~= root & x..right ~= root";

      invariant LeftInjInv:
      "ALL x y z. x : nodes & y : nodes & z : nodes & x = y..left --> 
      (y ~= z --> z..left ~= x) & z..right ~= x";

      invariant RightInjInv:
      "ALL x y z. x : nodes & y : nodes & z : nodes & x = y..right -->
      (y ~= z --> z..right ~= x) & z..left ~= x";

      invariant NonNullNodesInv: "null ~: nodes";

      invariant SubtreeNullInv: "null..subtree = {}";

      invariant SubtreeDefInv: "ALL n. n : nodes --> 
      n..subtree = { n..v } Un n..left..subtree Un n..right..subtree & 
      n..v ~: n..left..subtree & n..v ~: n..right..subtree";

      invariant LeftOrderingInv: 
      "ALL x y. y : nodes & x : y..left..subtree --> x < y..v";

      invariant RightOrderingInv: 
      "ALL x y. y : nodes & x : y..right..subtree --> x > y..v";

      invariant LeftParentInv:
      "ALL x. x : nodes & x..left ~= null --> x..left..parent = x";

      invariant RightParentInv:
      "ALL x. x : nodes & x..right ~= null --> x..right..parent = x";

      invariant ParentNotNullInv:
      "ALL x. x : nodes & x..parent ~= null --> 
      x..parent..left = x | x..parent..right = x";

      invariant RootParentInv: "root..parent = null";

      invariant IsRootInv: "ALL x. x : nodes & x..parent = null --> x = root";

      invariant HasMinInv: "ALL x. x : nodes & x..subtree ~= {} -->
      (EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z))";
    */

    public static void add(int w)
    /*: modifies content
        ensures "content = old content Un { w }"
    */
    {
	Node n = root, p = null;
	boolean wentLeft = false;
	while /*: inv "(w : old content) = (w : fieldRead (old Node.subtree) n) &
		       (p ~= null & wentLeft --> p..left = n) &
		       (p ~= null & ~wentLeft --> p..right = n) &
		       (p ~= null --> p : nodes) &
		       (n ~= null --> n : nodes) &
		       (p = null --> n = root) &
		       (p ~= null & w < p..v --> wentLeft) &
		       (p ~= null & w > p..v --> ~wentLeft) &
		       (p ~= null --> p..v ~= w) &
		       (p ~= null --> content = old content Un { w }) &
		       theinv SubtreeNullInv &
		       theinv HasMinInv &
		       comment ''PSubtreeLoop''
		       (p ~= null --> 
		       p..subtree = (fieldRead (old Node.subtree) p) Un {w} &
		       p..v ~: p..left..subtree & p..v ~: p..right..subtree) &
		       comment ''AllSubtreeLoop''
		       (ALL x. x : nodes -->
		       (x..subtree = fieldRead (old Node.subtree) x) |
		       (x..subtree = (fieldRead (old Node.subtree) x) Un {w})) &
		       comment ''SubtreeDefLoop''
		       (ALL m. m : nodes & m ~= p --> m..subtree = 
		       { m..v } Un m..left..subtree Un m..right..subtree &
		       m..v ~: m..left..subtree & m..v ~: m..right..subtree) &
		       theinv LeftOrderingInv &
		       theinv RightOrderingInv"
	      */
	  (n != null) {
	    //: ghost specvar old_n_subtree :: "int set" = "n..subtree";
	    //: pickWitness min :: int suchThat "min : n..subtree & (ALL z. z : n..subtree --> min <= z)";

	    p = n;
	    //: "n..subtree" := "n..subtree Un { w }";
	    if (w < n.v) {
		wentLeft = true;
		n = n.left;
	    } else if (w > n.v) {
		wentLeft = false;
		n = n.right;
	    } else {
		{ 
		    //: pickAny x::obj;
		    {
			//: assuming NonEmptyHyp: "x : nodes & x..subtree ~= {}";
			{
			    //: assuming NotNCase: "x ~= p";
			    //: note NotNConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
			}
			{
			    //: assuming NCase: "x = p";
			    {
				//: assuming MinSmallHyp: "min <= w";
				//: note MinSmallConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
			    }
			    {
				//: assuming WSmallHyp: "w < min";
				//: note WSmallConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
			    }
			    //: note NConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)" from NConc, MinSmallConc, WSmallConc;
			}
			//: note NotEmptyConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)" from NotEmptyConc, NConc, NotNConc;
		    }
		    //: note HasMinLoop: "x : nodes & x..subtree ~= {} --> (EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z))" forSuch x;
		}
		return;
	    }
	    
	    { 
		//: pickAny x::obj;
		{
		    //: assuming NonEmptyHyp: "x : nodes & x..subtree ~= {}";
		    {
			//: assuming NotNCase: "x ~= p";
			//: note NotNConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
		    }
		    {
			//: assuming NCase: "x = p";
			{
			    //: assuming MinSmallHyp: "min <= w";
			    //: note MinSmallConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
			}
			{
			    //: assuming WSmallHyp: "w < min";
			    //: note WSmallConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
			}
			//: note NConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)" from NConc, MinSmallConc, WSmallConc;
		    }
		    //: note NotEmptyConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)" from NotEmptyConc, NConc, NotNConc;
		}
		//: note HasMinLoop: "x : nodes & x..subtree ~= {} --> (EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z))" forSuch x;
	    }
	}

	Node e = new Node();
	e.v = w;
	//: "e..subtree" := "{ w }";
	//: "nodes" := "nodes Un { e }";
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

	{ 
	    //: pickAny x::obj;
	    {
		//: assuming NonEmptyHyp: "x : nodes & x..subtree ~= {}";
		{
		    //: assuming NewNodeHyp: "x = e";
		    //: note NewNodeConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)" from NewNodeConc, NewNodeHyp;
		}
		{
		    //: assuming OldNodeHyp: "x ~= e";
		    //: note OldNodeConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
		}
		//: note NotEmptyConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)" from NotEmptyConc, NewNodeConc, OldNodeConc;
	    }
	    //: note HasMinConc: "x : nodes & x..subtree ~= {} --> (EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z))" forSuch x;
	}

    }

    public static boolean contains(int w)
    /*: ensures "result = (w : content)"
     */
    {
	Node curr = root;

	while /*: inv "(curr ~= null --> curr : nodes) &
		       comment ''InContentLoop''
		       (w : content) = (w : curr..subtree)"
	      */
	    (curr != null) {
	    if (curr.v == w) {
		return true;
	    } else {
		if (w < curr.v) {
		    curr = curr.left;
		} else {
		    curr = curr.right;
		}
	    }
	}

	return false;
    }

    public static boolean isEmpty()
    /*: ensures "result = (content = {})"
     */
    {
	return root == null;
    }

    public static void remove(int w)
    /*: modifies content
        ensures "content = old content - { w }"
     */
    {
	//: ghost specvar prev :: obj = "null";
	Node curr = root;

	while /*: inv "(w : old content) = (w : fieldRead (old Node.subtree) curr) &
		       (prev ~= null & w < prev..v --> curr = prev..left) &
		       (prev ~= null & w > prev..v --> curr = prev..right) &
		       (prev ~= null --> prev : nodes) &
		       (curr ~= null --> curr : nodes) &
		       (prev = null --> curr = root) &
		       (prev ~= null --> prev..v ~= w) &
		       (prev ~= null --> content = old content - { w }) &
		       theinv SubtreeNullInv &
		       theinv HasMinInv &
		       comment ''PSubtreeLoop''
		       (prev ~= null --> prev..subtree = 
		       (fieldRead (old Node.subtree) prev) - {w} &
		       prev..v ~: prev..left..subtree & 
		       prev..v ~: prev..right..subtree) &
		       comment ''AllSubtreeLoop''
		       (ALL x. x : nodes -->
		       (x..subtree = fieldRead (old Node.subtree) x) |
		       (x..subtree = (fieldRead (old Node.subtree) x) - {w})) &
		       comment ''SubtreeDefLoop''
		       (ALL m. m : nodes & m ~= prev --> m..subtree = 
		       { m..v } Un m..left..subtree Un m..right..subtree &
		       m..v ~: m..left..subtree & m..v ~: m..right..subtree) &
		       theinv LeftOrderingInv &
		       theinv RightOrderingInv"
	      */
	    (curr != null && curr.v != w) {
	    //: pickWitness min :: int suchThat "min : curr..subtree & (ALL z. z : curr..subtree --> min <= z)";

	    //: "curr..subtree" := "curr..subtree - { w }";

	    //: "prev" := "curr";
	    if (w < curr.v) {
		curr = curr.left;
	    } else {
		curr = curr.right;
	    }

	    {
		//: pickAny x::obj;
		{
		    //: assuming NonEmptyHyp: "x : nodes & x..subtree ~= {}";
		    {
			//: assuming NotPrevHyp: "x ~= prev";
			//: note NotPrevConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
		    }
		    {
			//: assuming PrevHyp: "x = prev";
			{
			    //: assuming MinNotWHyp: "min ~= w";
			    //: note MinNotWConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
			}
			{
			    //: assuming MinWHyp: "min = w";
			    //: note MinWConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
			}
			//: note PrevConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)";
		    }
		    //: note NotEmptyConc: "EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z)" from NotEmptyConc, PrevConc, NotPrevConc;
		}
		//: note HasMinLoop: "x : nodes & x..subtree ~= {} --> (EX y. y : x..subtree & (ALL z. z : x..subtree --> y <= z))" forSuch x;
	    }
	}

	if (curr != null) {
	    removeNode(curr);
	}
    }

    private static void removeNode(Node n)
    /*: requires "n ~= null & n : nodes & (n ~= n..parent) &
                  theinv RootNodesInv &
		  theinv LeftNodesInv &
		  theinv RightNodesInv &
		  theinv ParentNodesInv &
		  theinv RootInjInv &
		  theinv LeftInjInv &
		  theinv RightInjInv &
		  theinv NonNullNodesInv &
		  theinv SubtreeNullInv &
		  theinv LeftOrderingInv &
		  theinv RightOrderingInv &
		  theinv LeftParentInv &
		  theinv RightParentInv &
		  theinv ParentNotNullInv &
		  theinv RootParentInv &
		  theinv IsRootInv &
		  theinv HasMinInv &
		  comment ''ParentSubtreePre''
		  (n..parent ~= null --> n..parent..subtree =
		  ({n..parent..v} Un n..parent..left..subtree Un 
		  n..parent..right..subtree) - {n..v} &
		  n..parent..v ~: n..parent..left..subtree & 
		  n..parent..v ~: n..parent..right..subtree) &
		  comment ''SubtreeDefPre''
		  (ALL m. m : nodes & m ~= n..parent --> m..subtree = 
		  { m..v } Un m..left..subtree Un m..right..subtree &
		  m..v ~: m..left..subtree & m..v ~: m..right..subtree)"
        modifies content, "Node.left", "Node.right", "Node.parent", root, nodes,
	         "Node.subtree"
        ensures "(n = old root --> content = old content - { n..v }) &
	         (n ~= old root --> content = old content) & 
		 (nodes = old nodes - { n }) & theinvs"
    */
    {
	if (n.left == null) {
	    if (n.right == null) {
		// n has no children
		if (n.parent == null) {
		    // n is the root node
		    root = null;
		} else if (n.parent.left == n) {
		    // n is a left child
		    n.parent.left = null;
		} else {
		    // n is a right child
		    n.parent.right = null;
		}
	    } else {
		// n has a right child but no left child
		if (n.parent == null) {
		    // n is the root node
		    root = n.right;
		} else if (n.parent.left == n) {
		    // n is a left child
		    n.parent.left = n.right;
		} else {
		    // n is a right child
		    n.parent.right = n.right;
		}
		n.right.parent = n.parent;
		n.right = null;
	    }
	    n.parent = null;
	} else if (n.right == null) {
	    // n has a left child but no right child
	    if (n.parent == null) {
		// n is the root node
		root = n.left;
	    } else if (n.parent.left == n) {
		// n is a left child
		n.parent.left = n.left;
	    } else {
		// n is a right child
		n.parent.right = n.left;
	    }
	    n.left.parent = n.parent;
	    n.left = null;
	    n.parent = null;
	} else {
	    //: assume "False";
	    // n has both left and right children
	    Node r = removeMinOfRight(n);
	    swap(n, r);
	}
	//: "nodes" := "nodes - {n}";
    }

    private static Node removeMinOfRight(Node n)
    /*: requires "n ~= null & n : nodes & 
                  n..right ~= null & n ~= n..parent &
                  theinv RootNodesInv &
		  theinv LeftNodesInv &
		  theinv RightNodesInv &
		  theinv ParentNodesInv &
		  theinv RootInjInv &
		  theinv LeftInjInv &
		  theinv RightInjInv &
		  theinv NonNullNodesInv &
		  theinv SubtreeNullInv &
		  theinv LeftOrderingInv &
		  theinv RightOrderingInv &
		  theinv LeftParentInv &
		  theinv RightParentInv &
		  theinv ParentNotNullInv &
		  theinv RootParentInv &
		  theinv IsRootInv &
		  theinv HasMinInv &
		  comment ''ParentSubtreePre''
		  (n..parent ~= null --> n..parent..subtree =
		  ({n..parent..v} Un n..parent..left..subtree Un 
		  n..parent..right..subtree) - {n..v} &
		  n..parent..v ~: n..parent..left..subtree & 
		  n..parent..v ~: n..parent..right..subtree) &
		  comment ''SubtreeDefPre''
		  (ALL m. m : nodes & m ~= n..parent --> m..subtree = 
		  { m..v } Un m..left..subtree Un m..right..subtree &
		  m..v ~: m..left..subtree & m..v ~: m..right..subtree)"
       modifies "Node.left", "Node.right", "Node.parent", "Node.subtree"
       ensures "theinv RootNodesInv &
		theinv LeftNodesInv &
		theinv RightNodesInv &
		theinv ParentNodesInv &
		theinv RootInjInv &
		theinv LeftInjInv &
		theinv RightInjInv &
		theinv NonNullNodesInv &
		theinv SubtreeNullInv &
		theinv LeftOrderingInv &
		theinv RightOrderingInv &
		theinv LeftParentInv &
		theinv RightParentInv &
		theinv ParentNotNullInv &
		theinv RootParentInv &
		theinv IsRootInv &
		comment ''ParentSubtreePre''
		(n..parent ~= null --> n..parent..subtree =
		({n..parent..v} Un n..parent..left..subtree Un 
		n..parent..right..subtree) - {n..v} &
		n..parent..v ~: n..parent..left..subtree & 
		n..parent..v ~: n..parent..right..subtree) &
		comment ''SubtreeDefPre''
		(ALL m. m : nodes & m ~= n..parent --> m..subtree = 
		{ m..v } Un m..left..subtree Un m..right..subtree &
		m..v ~: m..left..subtree & m..v ~: m..right..subtree) &
		(ALL x. x : n..left..subtree --> x < result..v) &
		(ALL x. x : n..right..subtree --> result..v < x) &
		(ALL y. y : nodes & n..v : y..left..subtree --> 
		result..v < y..v) &
		(ALL y. y : nodes & n..v : y..right..subtree -->
		y..v < result..v)"
    */
    {
	//: private ghost specvar bigger :: "int set" = "{}";
	Node e = n.right;
	
	while /*: inv "e ~= null & e : nodes & e..parent ~= null &
		       n..right..subtree = bigger Un e..subtree &
		       e..v : n..right..subtree &
		       comment ''BiggerLoop''
		       (ALL x. x : bigger --> e..v < x)"
	      */
	    (e.left != null) {
	    //: bigger := "bigger Un {e..v} Un e..right..subtree";
	    e = e.left;
	}
	//: assume "False";

	if (e.parent.left == e) {
	    // e is a left child
	    e.parent.left = e.right;
	} else {
	    // e is a right child
	    e.parent.right = e.right;
	}
	
	if (e.right != null) {
	    e.right.parent = e.parent;
	}

	e.parent = null;
	e.right = null;
	
	//: "e..subtree" := "{e..v}";
	//: "nodes" := "nodes - { e }";
	return e;
    }

    private static void swap(Node n, Node r)
    {
    }
}
 
