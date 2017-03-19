public /*: claimedby SLL */ class Node {
    public Object data;
    public Node next;
    /*: 
      public specvar con :: "objset" = "({} :: obj set)";
      vardefs "con == { data } Un next..Node.con";
    */
}

class SLL {
    private Node first;

    /*: 
     public specvar content :: "obj set";
     vardefs "content == first..Node.con";

     public ensured invariant ContentAlloc:
       "ALL x. x : content --> x : Object.alloc";

     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..Node.next) | 
                              (x : SLL & y = x..SLL.first))";

     invariant InjInv:
       "ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2";

     invariant AllocInv: "first : Object.alloc";

     public ensured invariant NonNullInv:
       "ALL x. x : content --> x ~= null";

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

	invariant ConNonNull:
	  "ALL z x. 
	    z : Node & z : Object.alloc & x : z..Node.con --> x ~= null";
     */


    public SLL()
    /*: 
      modifies content 
      ensures "content = {}"
    */
    {
        first = null;
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
	    first = second;
	} else {
	    Node prev = first;
	    Node current = prev.next;
	    while /*: inv "
		    prev : Node & prev : Object.alloc & prev ~= null &
		    current : Node & current : Object.alloc & current ~= null &
		    prev..Node.next = current & prev ~= current &
		    content = old content \<setminus> {d0} &
		    (ALL n. n : SLL & n : old Object.alloc & n ~= this -->
		    n..content = old (n..content)) &
		    d0 : current..Node.con &
		    comment ''ConDefInv''
		    (ALL n. n : Node & n : Object.alloc & n ~= null & n ~= prev -->
		    n..Node.con = {n..Node.data} Un n..Node.next..Node.con &
		    (n..Node.data ~: n..Node.next..Node.con)) &
		    null..Node.con = {} &
		    Node.con =
		    (% this. { this..Node.data } Un this..Node.next..Node.con)"
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
        ensures "result = (d0 : content) & theinvs"
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
    /*: requires "d0 ~= null & (d0 ~: content)"
        modifies content
        ensures "content = old content Un {d0}"
     */
    {
	Node n = new Node();
	n.data = d0;
	n.next = first;
	first = n;
    }

    public boolean isEmpty()
    /*: ensures "result = (content = {})";
    */
    {
        return (first==null);
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
