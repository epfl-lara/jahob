class Node {
    public /*: claimedby List */ Node next;
}

// Cyclic list with a header node
class List
{
   public static Node first; 
  
   /*:
     private static ghost specvar next1 :: "obj => obj" = "(% x. null)"; // as if _INIT was not taking initial values of ghost vars into account
     public invariant next1field: "ALL n. n ~: alloc --> isolated n";

     public static specvar content :: objset;
     vardefs "content == {x. x ~= null & (first..next1,x) : {(v,w). v..next1=w}^*}";

     public static specvar isolated :: "obj => bool";
     vardefs "isolated == (%n. n..next1 = null & (ALL x. x ~= null --> x..next1 ~= n))";

     private static specvar last :: "obj => bool";
     private vardefs "last == (% x. (first,x) : {(v,w). v..next1=w}^* & x ~=null & x..next1 = null)";

     invariant firstIsolated: "first ~= null --> (ALL n. n..next1 ~= first)";
     
     invariant isTree: "tree [next1]";

     invariant fieldConstraint: "ALL x y. next x = y --> 
         ((last x --> y = first) & (~ last x --> y = x..next1))"
   */

    // initialization of a list with a header node pointing to itself
    public static void init() 
    /*: requires "first = null"
        modifies content, isolated, first
        ensures "content = {} & first ~= null"
     */
    {
    	first = new Node();
        first.next = first;
    }

    public static void add(Node n)
    /*: requires "comment ''add_pre'' (first ~= null & n ~: content & n ~= null & n ~= first & isolated n)"
        modifies content, isolated
        ensures "comment ''add_post'' (content = old content Un {n})"
    */
    {	
	n.next = first.next;
	//: "n..next1" := "first..next1";
	first.next = n;
	//: "first..next1" := "n";
    }

    public static boolean member(Node n)
    /*: requires "comment ''mem_pre'' (first ~= null & n ~= null)"
        ensures "comment ''mem_post'' (result = (n : content))"
     */
    {	
	Node tmp = first.next;
	if (tmp==first) { 
	    return false; 
	} else {
	    //: ghost specvar seen :: objset = "{}"
	    while /*:  inv "
		    comment ''A'' (tmp = first | tmp : content) &
		    comment ''B1'' (tmp : content --> seen = {x. x : content & (tmp,x) ~: {(u,v). u..next1 = v}^*}) &
		    comment ''B2'' (tmp = first --> seen = content) &
		    comment ''C'' (ALL x. x : seen --> x != n)" */
		(tmp != first) {
		if(tmp == n) {
		    return true;
		}
		//: seen := "seen Un {tmp}"
		tmp = tmp.next;
	    }
	    //: noteThat seenAll: "seen = content";
	    return false;
	}
    }
}
