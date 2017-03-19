public /*: claimedby Set */ class Node {
    public Object data;
    public Node next;
    public Lock mutex;
    /*: 
      public ghost specvar con :: "objset" = "({} :: obj set)";
    */
}

class Set {
    private Node first;

    private Lock mutex;
    /*: 
     public specvar content :: "obj set";
     vardefs "content == first..Node.con";

     public ensured invariant ContentAlloc:
       "ALL x. x : content --> x : Object.alloc";

     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..Node.next) | 
                              (x : Set & y = x..Set.first))";

     invariant InjInv:
       "ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2";

     invariant AllocInv: "first : Object.alloc";

    */
    
    /*: invariant ConAlloc:
          "ALL z x. z : Node & z : Object.alloc & x : z..Node.con -->
	    x : Object.alloc";

	invariant ConNull:
	  "ALL x. x : Node & x : Object.alloc & x = null --> x..Node.con = {}";
	  
	invariant ConDef:
	  "ALL x. x : Node & x : Object.alloc & x ~= null -->
	          x..Node.con = 
		  { x..Node.data } Un x..Node.next..Node.con &
		  (x..Node.data ~: x..Node.next..Node.con)";
     */


    public Set()
    /*: 
      modifies content 
      ensures "content = {}"
    */
    {
        first = null;
        // "first..Node.nodes" := "{}";
    }

    public void remove(Object d0)
    /*: requires "d0 ~= null & (d0 : content)"
        modifies content
        ensures "content = old content \<setminus> {d0} & (d0 : old content)"
    */
    {
	Node f = first;
	if (f.data == d0) {
	    Node second = f.next;
	    f.next = null;
	    //: "f..Node.con" := "{f..Node.data}";
	    first = second;
	} else {
	    Node prev = first;
	    /*: "prev..Node.con" := 
	        "prev..Node.con \<setminus> {d0}";
	    */
	    Node current = prev.next;
	    while /*: inv "
		    prev : Node & prev : Object.alloc & prev ~= null &
		    prev..Node.con = 
		     fieldRead (old Node.con) prev \<setminus> {d0} &
		    current : Node & current : Object.alloc & current ~= null &
		    prev..Node.next = current & prev ~= current &
		    content = old content \<setminus> {d0} &
		    (ALL n. n : Set & n : old Object.alloc & n ~= this -->
		    n..content = old (n..content)) &
		    d0 : current..Node.con &
		    comment ''ConDefInv''
		    (ALL n. n : Node & n : Object.alloc & n ~= null & n ~= prev -->
		    n..Node.con = {n..Node.data} Un n..Node.next..Node.con &
		    (n..Node.data ~: n..Node.next..Node.con)) &
		    (ALL n. n..Node.con = old (n..Node.con) |
		    n..Node.con = old (n..Node.con) \<setminus> {d0}) &
		    null..Node.con = {}"
		  */
		(current.data != d0)
                {
                    /*: "current..Node.con" := 
		      "current..Node.con \<setminus> {d0}"; */
                    prev = current;
                    current = current.next;
                }
	    Node nxt = current.next;
	    prev.next = nxt;
	    current.next = null;
	    //: "current..Node.con" := "{current..Node.data}";
	}
    }

    public boolean contains(Object d0)
    /*: ensures "result = (d0 : content)"
     */
    {
        return contains0(d0);
    }

    private boolean contains0(Object d0)
    /*: requires "theinvs"
        ensures "result = (d0 : content) & theinvs &
	         (ALL x. x..Set.content = (fieldRead (old Set.content) x)) &
		 Object.alloc = (old Object.alloc)"
    */
    {
        Node current = first;
        while /*: inv "current : Node & current : Object.alloc & 
                       ((d0 : content) = (d0 : current..Node.con))" */
            (current != null) {
            if (current.data == d0) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public void add(Object d0)
    /*: modifies content
        ensures "(content = old content Un {d0}) &
	        (ALL x. x : Object.alloc & x : Set --> x : (old Object.alloc))"
    */
    {
	if (!contains0(d0)) {
	    add0(d0);
	}
    }

    private void add0(Object d0)
    /*: requires "d0 ~: content & theinvs"
        modifies content, "Set.first"
        ensures "(content = old content Un {d0}) & theinvs &
	        (ALL x. x : Object.alloc & x : Set --> x : (old Object.alloc))"
    */
    {
	Node n = new Node();
	n.data = d0;
	n.next = first;
	//: "n..Node.con" := "{d0} Un first..Node.con";
	first = n;
    }

    public void addc(Object d0)
    /*: modifies content
        ensures "(content = old content Un {d0}) &
	        (ALL x. x : Object.alloc & x : Set --> x : (old Object.alloc))"
    */
    {
        Node current = first;
        while /*: inv "current : Node & current : Object.alloc & 
                       ((d0 : content) = (d0 : current..Node.con))" */
            (current != null) {
            if (current.data == d0) {
                return;
            }
            current = current.next;
        }
	Node n = new Node();
	n.data = d0;
	n.next = first;
	//: "n..Node.con" := "{d0} Un first..Node.con";
	first = n;
    }

    public void addr(Object d0)
    /*: modifies "Set.content", "Node.con", "Node.next"
        ensures "(content = old content Un {d0}) &
	         (ALL x. x : Object.alloc & x : Set --> x : (old Object.alloc))"
    */
    {
	mutex.acquire();
	if (first == null) {
	    Node n = new Node();
	    n.data = d0;
	    //: "n..Node.con" := "{d0}";
	    first = n;
	    mutex.release();
	} else {
	    //: "first..Node.con" := "(old first..Node.con) Un {d0}";
	    mutex.release();
	    spawn(naddr(first, d0));
	}
    }

    private static void naddr(Node n0, Object d0)
    /*: requires "n0 ~= null &
                  theinv ContentAlloc &
		  theinv InjInv &
		  theinv AllocInv &
		  theinv ConAlloc &
		  theinv ConNull &
		  (ALL x. x : Node & x : Object.alloc & x ~= null & x ~= n0 -->
		  x..Node.con =
		  { x..Node.data } Un x..Node.next..Node.con &
		  (x..Node.data ~: x..Node.next..Node.con)) &
		  (n0..Node.con =
		  ({ n0..Node.data } Un n0..Node.next..Node.con) Un {d0}) &
		  (n0..Node.data ~: n0..Node.next..Node.con)"
        modifies "Node.con", "Set.content", "Node.next"
        ensures "(n0..Node.con = (fieldRead (old Node.con) n0) Un {d0}) &
	         (ALL x. x : (old Object.alloc) -->
		 ((x..Node.con = (fieldRead (old Node.con) x)) |
		 (x..Node.con = (fieldRead (old Node.con) x) Un {d0}))) &
		 (ALL x. x : Object.alloc & x : Set --> x : (old Object.alloc)) &
	         theinvs"
    */
    {
	n0.mutex.acquire();
	if (n0.data == d0) {
	    n0.mutex.release();
	} else if (n0.next == null) {
	    Node n1 = new Node();
	    n1.data = d0;
	    //: "n1..Node.con" := "{d0}";
	    n0.next = n1;
	    //: "n0..Node.con" := "(old n0..Node.con) Un {d0}";
	    n0.mutex.release();
	} else {
	    //: "n0..Node.next..Node.con" := "(old n0..Node.next..Node.con) Un {d0}";
	    n0.mutex.release();
	    spawn(naddr(n0.next, d0));
	}
    }

    public boolean isEmpty()
    /*: ensures "result = (content = {})";
    */
    {
        return (first==null);
    }

}
