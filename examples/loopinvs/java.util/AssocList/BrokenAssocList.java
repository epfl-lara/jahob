public /*: claimedby AssocList */ class Node {
    public Object key;
    public Object value;
    public Node next;
    /*: 
      public ghost specvar con :: "(obj * obj) set" = "({} :: (obj * obj) set)";
    */
}

class AssocList {
    private Node first;

    /*: 
     public specvar content :: "(obj * obj) set";
     vardefs "content == first..Node.con";

     public ensured invariant ContentAlloc:
       "ALL x y. (x, y) : content --> (x : Object.alloc & y : Object.alloc)";

     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..Node.next) | 
                              (x : AssocList & y = x..AssocList.first))";

     invariant InjInv:
       "ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2";

     public ensured invariant SetInv:
       "ALL k v0 v1. (k, v0) : content & (k, v1) : content --> v0 = v1";

     invariant AllocInv: "first : Object.alloc";

     public ensured invariant NonNullInv:
       "ALL k v. (k, v) : content --> k ~= null & v ~= null";

    */
    
    /*: invariant ConAlloc:
          "ALL z x y. z : Node & z : Object.alloc & (x, y) : z..Node.con -->
	    x : Object.alloc & y : Object.alloc";

	invariant ConNull:
	  "ALL x. x : Node & x : Object.alloc & x = null --> x..Node.con = {}";
	  
	invariant ConDef:
	  "ALL x. x : Node & x : Object.alloc & x ~= null -->
	          x..Node.con = 
		  {(x..Node.key, x..Node.value)} Un x..Node.next..Node.con &
		  (ALL v. (x..Node.key, v) ~: x..Node.next..Node.con)";

	invariant ConNonNull:
	  "ALL z x y. z : Node & z : Object.alloc & (x, y) : z..Node.con -->
	              x ~= null & y ~= null";
     */


    private Object brokenRecRemove0(Node prev, Object k0)
    /*: requires "k0 ~= null & (EX v. (k0, v) : prev..Node.con) & 
                  prev..Node.key ~= k0 & theinvs"
        modifies content, "Node.con", "Node.next"
        ensures "prev..Node.next..Node.con = 
		 (old prev..Node.next..Node.con) \<setminus> {(k0, result)} &
		 (k0, result) : (old prev..Node.con) &
		 theinv ContentAlloc & theinv InjInv & theinv SetInv & 
		 theinv AllocInv & theinv NonNullInv & theinv ConAlloc & 
		 theinv ConNull & theinv ConNonNull & 
		 comment ''ConDefPost'' 
		 (ALL x. 
		  ((x : Node & x : Object.alloc & x ~= null & x ~= prev) -->
		  x..Node.con = 
		  {(x..Node.key, x..Node.value)} Un x..Node.next..Node.con &
		  (ALL v. (x..Node.key, v) ~: x..Node.next..Node.con)))"
    */
    {
	//: private ghost specvar v0 :: obj;
	//: assume "(k0, v0) : prev..Node.con";
	Node curr = prev.next;
	if (curr.key == k0) {
	    prev.next = curr.next;
	    curr.next = null;
	    //: "curr..Node.con" := "{(curr..Node.key, curr..Node.value)}";
	    return curr.value;
	} else {
	    Object v = brokenRecRemove0(curr, k0);
	    //: "curr..Node.con" := "curr..Node.con \<setminus> {(k0, v0)}";
            return v;
	}
    }
}
