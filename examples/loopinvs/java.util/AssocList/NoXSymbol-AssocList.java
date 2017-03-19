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
     vardefs "content == first..con";

     public ensured invariant ContentAlloc:
       "ALL x y. (x, y) : content --> (x : alloc & y : alloc)";

     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..next) | 
                              (x : AssocList & y = x..first))";

     invariant InjInv:
       "ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2";

     public ensured invariant SetInv:
       "ALL k v0 v1. (k, v0) : content & (k, v1) : content --> v0 = v1";

     invariant AllocInv: "first : alloc";

     public ensured invariant NonNullInv:
       "ALL k v. (k, v) : content --> k ~= null & v ~= null";

    */
    
    /*: invariant ConAlloc:
          "ALL z x y. z : Node & z : alloc & (x, y) : z..con --> x : alloc & y : alloc";

	invariant ConNull:
	  "ALL x. x : Node & x : alloc & x = null --> x..con = {}";
	  
	invariant ConDef:
	  "ALL x. x : Node & x : alloc & x ~= null -->
	          x..con = 
		  {(x..key, x..value)} Un x..next..con &
		  (ALL v. (x..key, v) ~: x..next..con)";

	invariant ConNonNull:
	  "ALL z x y. z : Node & z : alloc & (x, y) : z..con --> x ~= null & y ~= null";
     */


    public AssocList()
    /*: 
      modifies content 
      ensures "content = {}"
    */
    {
        first = null;
        // "first..nodes" := "{}";
    }

    public boolean containsKey(Object k0)
    /*: ensures "result = (EX v. ((k0, v) : content))"
     */
    {
        return containsKey0(k0);
    }

    private boolean containsKey0(Object k0)
    /*: requires "theinvs"
        ensures "result = (EX v. ((k0, v) : content)) & theinvs"
    */
    {
        Node current = first;
        while /*: inv "current : Node & current : alloc & 
                       (EX v. (k0, v) : content) = (EX v. (k0, v) : current..con)" */
            (current != null) {
            if (current.key == k0) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public void add(Object k0, Object v0)
    /*: requires "k0 ~= null & v0 ~= null & ~(EX v. (k0, v) : content)"
        modifies content
        ensures "content = old content Un {(k0, v0)}"
     */
    {
	Node n = new Node();
	n.key = k0;
	n.value = v0;
	n.next = first;
	//: "n..con" := "{(k0, v0)} Un first..con";
	first = n;
    }

    public Object replace(Object k0, Object v0)
    /*: requires "k0 ~= null & v0 ~= null & (EX v. (k0, v) : content)"
        modifies content
	ensures "content = old content - {(k0, result)} Un {(k0, v0)} &
                 (k0, result) : old content"
    */
    {
	Object v1 = remove(k0);
	add(k0, v0);
	return v1;
    }

    public Object put(Object k0, Object v0)
    /*: requires "k0 ~= null & v0 ~= null"
        modifies content
	ensures "(result = null --> content = old content Un {(k0, v0)}) &
	         (result ~= null -->
		   content = old content - {(k0, result)} Un {(k0, v0)})"
     */
    {
	if (containsKey0(k0)) {
	    return replace(k0, v0);
	} else {
	    add(k0, v0);
	    return null;
	}
    }

    public Object get(Object k0)
    /*: requires "k0 ~= null"
        ensures "(result ~= null --> (k0, result) : content) &
	         (result = null --> ~(EX v. (k0, v) : content)) &
		 alloc = old alloc"
	         
     */
    {
	Node current = first;
        while /*: inv "current : Node & current : alloc &
                       (ALL v. ((k0, v) : content) = ((k0, v) : current..con))" */
            (current != null) {
            if (current.key == k0) {
                return current.value;
            }
            current = current.next;
        }
        return null;
    }

    public boolean isEmpty()
    /*: ensures "result = (content = {})";
    */
    {
        return (first==null);
    }

    public Object remove(Object k0)
    /*: requires "k0 ~= null & (EX v. (k0, v) : content)"
        modifies content
        ensures "content = old content \<setminus> {(k0, result)} &
	         (k0, result) : old content"
    */
    {
	//: pickWitness v0 :: obj suchThat "(k0, v0) : content";
	Node f = first;
	if (f.key == k0) {
	    Node second = f.next;
	    f.next = null;
	    //: "f..con" := "{(f..key, f..value)}";
	    first = second;
	    return f.value;
	} else {
	    Node prev = first;
	    /*: "prev..con" := 
	        "prev..con \<setminus> {(k0, v0)}";
	    */
	    Node current = prev.next;
	    while /*: inv "
		    prev : Node & prev : alloc & prev ~= null &
		    prev..con = 
		     fieldRead (old con) prev \<setminus> {(k0, v0)} &
		    current : Node & current : alloc & current ~= null &
		    prev..next = current & prev ~= current &
		    content = old content \<setminus> {(k0, v0)} &
		    (ALL n. n : AssocList & n : old alloc & n ~= this -->
		    n..content = old (n..content)) &
		    (k0, v0) : current..con &
		    comment ''ConDefInv''
		    (ALL n. n : Node & n : alloc & n ~= null & n ~= prev -->
		    n..con = {(n..key, n..value)} Un n..next..con &
		    (ALL v. (n..key, v) ~: n..next..con)) &
		    (ALL n. n..con = old (n..con) |
		    n..con = old (n..con) \<setminus> {(k0, v0)}) &
		    null..con = {}"
		  */
		(current.key != k0)
                {
                    /*: "current..con" := 
		      "current..con \<setminus> {(k0, v0)}"; */
                    prev = current;
                    current = current.next;
                }
	    Node nxt = current.next;
	    prev.next = nxt;
	    current.next = null;
	    //: "current..con" := "{(current..key, current..value)}";
	    return current.value;
	}
    }

    /*    
    public static void main(String[] args)
    {
        List l = new List();
        Object o1 = new Object();
        Object o2 = new Object();
        Object o3 = new Object();
        Object o4 = new Object();
        l.add(o1);
        l.add(o2);
        l.add(o3);
        l.add(o4);
        l.remove(o2);
        l.remove(o4);
        l.remove(o1);
        l.remove(o1);
        if (l.isEmpty()) {
            System.out.println("Oops, the list is empty but should have one element.");
        } else {
            System.out.println("ok1.");
        }
        l.remove(o3);
        if (!l.isEmpty()) {
            System.out.println("Oops, the list is not empty but should be.");
        } else {
            System.out.println("ok2.");
        }
    }
    */
}
