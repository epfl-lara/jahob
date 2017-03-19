public /*: claimedby Map */ class Node {
    public Object key;
    public Object value;
    public Node next;
    /*: 
      public ghost specvar con :: "(obj * obj) set" = "({} :: (obj * obj) set)";
    */
}

class Map {
    private Node first;

    /*: 
     public specvar mapping :: "(obj * obj) set";
     vardefs "mapping == first..Node.con";

     public ensured invariant MappingAlloc:
       "ALL x y. (x, y) : mapping --> (x : Object.alloc & y : Object.alloc)";

     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..Node.next) | 
                              (x : Map & y = x..Map.first))";

     invariant InjInv:
       "ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2";

     invariant AllocInv: "first : Object.alloc";

     public ensured invariant NonNullInv:
       "ALL k v. (k, v) : mapping --> k ~= null & v ~= null";

    */
    
    /*: invariant ConAlloc:
          "ALL z x y. z : Node & z : Object.alloc & (x, y) : z..Node.con -->
	    x : Object.alloc & y : Object.alloc";

	invariant ConNull:
	  "ALL x. x : Node & x : Object.alloc & x = null --> x..Node.con = {}";
	  
	invariant ConDef:
	  "ALL x. x : Node & x : Object.alloc & x ~= null -->
	          x..Node.con = 
		  {(x..Node.key, x..Node.value)} Un x..Node.next..Node.con";

	invariant ConNonNull:
	  "ALL z x y. z : Node & z : Object.alloc & (x, y) : z..Node.con -->
	              x ~= null & y ~= null";
    */


    public Map()
    /*: 
      modifies mapping 
      ensures "mapping = {}"
    */
    {
        first = null;
        // "first..Node.nodes" := "{}";
    }

    public boolean containsKey(Object k0)
    /*: ensures "result = (EX v. ((k0, v) : mapping))"
     */
    {
        return containsKey0(k0);
    }

    private boolean containsKey0(Object k0)
    /*: requires "theinvs"
        ensures "result = (EX v. ((k0, v) : mapping)) & theinvs"
    */
    {
        Node current = first;
        while /*: inv "current : Node & current : Object.alloc & 
                       (EX v. (k0, v) : mapping) = 
		       (EX v. (k0, v) : current..Node.con)" */
            (current != null) {
            if (current.key == k0) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public void add(Object k0, Object v0)
    /*: requires "k0 ~= null & v0 ~= null"
        modifies mapping
        ensures "mapping = (old mapping) Un {(k0, v0)} & 
	        (ALL x. x : Object.alloc & x : Map --> x : (old Object.alloc))"
     */
    {
	Node n = new Node();
	n.key = k0;
	n.value = v0;
	n.next = first;
	//: "n..Node.con" := "{(k0, v0)} Un first..Node.con";
	first = n;
    }

    public Object get(Object k0)
    /*: ensures "(result ~= null --> (k0, result) : mapping) &
	         (result = null --> ~(EX v. (k0, v) : mapping)) &
		 Object.alloc = old Object.alloc"
	         
     */
    {
	Node current = first;
        while /*: inv "current : Node & current : Object.alloc &
                       (ALL v. ((k0, v) : mapping) = 
		       ((k0, v) : current..Node.con))" */
            (current != null) {
            if (current.key == k0) {
                return current.value;
            }
            current = current.next;
        }
        return null;
    }

    public boolean isEmpty()
    /*: ensures "result = (mapping = {})";
    */
    {
        return (first==null);
    }
}
