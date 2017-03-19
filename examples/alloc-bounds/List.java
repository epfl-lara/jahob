public /*: claimedby List */ class Node {
    public Object data;
    public Node next;
    /*: 
      public ghost specvar con :: objset = "{} :: objset";

    */
}

class List {
   private Node first;

   /*: 

   invariant ConAlloc: "ALL n. n : Object.alloc & n : Node  --> 
      n..Node.con \<subseteq> Object.alloc";

   invariant ConNull: "null..Node.con = {}";
   invariant ConDef: "ALL n. n : Object.alloc & n : Node & n ~= null --> 
       n..Node.con = {n..Node.data} Un n..Node.next..Node.con & 
       n..Node.data ~: n..Node.next..Node.con";
       

     public specvar content :: objset;
     vardefs "content == first..Node.con";

     public ensured invariant ("ContentAlloc") "content \<subseteq> Object.alloc";



     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..Node.next) | 
                              (x : List & y = x..List.first))";

     invariant ("Inj") "ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2";

   */

    //    public List()
    /*
      modifies content 
      ensures "content = {}"
    */
    //    {
    //    first = null;
    //    // "first..Node.nodes" := "{}";
    //}

    public boolean member(Object o1)
    //: ensures "result = (o1 : content)";
    {
        return member1(o1);
    }

    private boolean member1(Object o1)
    /*: requires "theinvs"
        ensures "result = (o1 : content) & theinvs"
    */
    {
        Node current = first;
        while /*: inv "current : Node & current : Object.alloc & 
                       (o1 : content) = (o1 : current..Node.con)" */
            (current != null) {
            if (current.data==o1) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public void add(Object o1)
    /*: modifies content
        ensures "content = old content Un {o1} &
	         cardinality (Object.alloc \<setminus> old Object.alloc) <= 1"
    */
    {
        if (!member1(o1)) {
            Node n = new Node();
            n.data = o1;
            n.next = first;
            //: "n..Node.con" := "{o1} Un first..Node.con";
            first = n;
        }
    }

    public List copy0() 
    /*: 
      ensures "result..content = this..content"
    */
    {
	List r = new List();
	r.first = null;
	if (first==null) {
	    return r;
	} else {
	    /*: 
	      noteThat obs0: "r ~: Node";
	      noteThat obs1: "theinv ConDef" from ConDef, obs0;
	      noteThat isLast1: "first..Node.con = {first..Node.data}";
	    */
	    // 	      assume "first..Node.next = null";

	    Node n;

	    /* copy first node */
	    n = new Node();
	    n.data = first.data;
	    //: "n..Node.con" := "first..Node.con";
	    n.next = null;
	    /* link first node */
	    r.first = n;

	    Node prev = n;
	    Node current = first.next;
	    //: noteThat isLast2: "n..Node.con = {n..Node.data}";
	    while (current != null) {
		/* copy current node */
		n = new Node();
		n.data = current.data;
		//: "n..Node.con" := "current..Node.con";
		n.next = null;

		/* link the copy */
		prev.next = n;

		/* advance */
		prev = n;
		current = current.next;
	    }
	    // assert copied: "r..content = this..content"
	    /* ghost specvar o1 :: obj;
	      havoc o1;
	      assume "o1 : Object.alloc & o1 : Node & o1 ~= null";
	      assume "o1 = n";
	      assert cndef: 
	      "o1..Node.con = {o1..Node.data} Un o1..Node.next..Node.con & 
  	      o1..Node.data ~: o1..Node.next..Node.con";
	      assume "False";
	    */
	    return r;
	}
    }

    public void mergeWith0(List l1)
    /*: 
      requires "l1 ~= null & l1 ~= this"
      modifies "List.content"
      ensures "True"
     */
    {
	if (!l1.isEmpty()) {
	    Object o1 = l1.getOne();
	    add(o1);
	    l1.remove(o1);
	    mergeWith(l1);
	}
    }

    public void mergeWith(List l1)
    /*: 
      requires "l1 ~= null & l1 ~= this"
      modifies "List.content"
      ensures "cardinality (Object.alloc \<setminus> old Object.alloc) 
            <= cardinality (old (l1..content))"
     */
    {
	if (!l1.isEmpty()) {
	    Object o1 = l1.getOne();
 	    l1.remove(o1);
	    /*:
	      ghost specvar S1 :: objset;
	      havoc S1;
	      assume S1_def: "S1 = old (l1..content)";
	      noteThat noAlloc1: "Object.alloc = old Object.alloc";
	      ghost specvar S2 :: objset;
	      havoc S2;
	      assume S2_def: "S2 = l1..content";
	      noteThat o1_was_there: "o1 : S1";
	      noteThat o1_removed: "S2 = S1 \<setminus> {o1}" 
	         from remove, S1_def, S2_def;
	     */
	    add(o1);
	    /*:
	      ghost specvar alloc1 :: objset;
	      alloc1 := "Object.alloc";
	      noteThat oneAlloc: 
                "cardinality (alloc1 \<setminus> old Object.alloc) <= 1";
	      noteThat S2same: "S2 = l1..content";
	     */
	    mergeWith(l1);
	    /*:
	      noteThat recursiveCase: 
	            "cardinality (Object.alloc \<setminus> alloc1)
	          <= cardinality S2" from mergeWith, S2_def;
              noteThat addingUp: 
      "cardinality (Object.alloc \<setminus> old Object.alloc) <= cardinality S1" 
           from recursiveCase, oneAlloc, o1_was_there, o1_removed;
	     */
	} else {
	    /*:
	      noteThat noL1: "(old (l1..content)) = {}";
	      ghost specvar S :: objset;
	      havoc S;
	      assume Sdef: "S = (old (l1..content))";
	      noteThat noS: "S = {}";
	      noteThat l1Size0: "cardinality S = 0" from noS;
	      noteThat "cardinality (old (l1..content)) = 0" from l1Size0, Sdef;
	      noteThat noNew: "Object.alloc = old Object.alloc";
	      noteThat diffSize0: 
	      "cardinality (Object.alloc \<setminus> old Object.alloc) = 0" 
	      from noNew;
	      noteThat last: 
	      "cardinality (Object.alloc \<setminus> old Object.alloc) 
	          <= cardinality (old (l1..content))" from l1Size0, diffSize0;
	     */
	}
    }

    public boolean isEmpty()
    /*: ensures "result = (content = {}) & 
                 Object.alloc = old Object.alloc & 
                 List.content = old List.content";
    */
    {
        return (first==null);
    }

    public Object getOne()
    /*: requires "content ~= {}"
        ensures "result : content & 
	         Object.alloc = old Object.alloc &
		 List.content = old List.content";
    */
    {
        return first.data;
    }

    public void remove(Object o1)
    /*: modifies content
        ensures "content = old content \<setminus> {o1} &
	         Object.alloc = old Object.alloc";
    */
    {
        if (member1(o1)) {
            Node f = first;
            if (f.data==o1) {
                Node second = f.next;
                f.next = null;
                //: "f..Node.con" := "{f..Node.data}";
                first = second;
            } else {
                Node prev = first;
                /*: "prev..Node.con" := "prev..Node.con \<setminus> {o1}"; */
                Node current = prev.next;
                while /*: inv "
                        prev : Node & prev : Object.alloc & prev ~= null &
                        prev..Node.con = fieldRead (old Node.con) prev 
                                               \<setminus> {o1} &
                        current : Node & current : Object.alloc & current ~= null &
                        prev..Node.next = current & prev ~= current &
                        content = old content \<setminus> {o1} &
                  (ALL n. n : List & n : old Object.alloc & n ~= this -->
                           n..content = old (n..content)) &
                        o1 : current..Node.con &
                     comment ''ConDefInv''
                      (ALL n. n : Node & n : Object.alloc & n ~= null & n ~= prev -->
                        n..Node.con = {n..Node.data} Un n..Node.next..Node.con &
                        n..Node.data ~: n..Node.next..Node.con) &
                        (ALL n. n..Node.con = old (n..Node.con) |
                                n..Node.con = old (n..Node.con) \<setminus> {o1}) &
                        null..Node.con = {}" */
                    (current.data != o1)
                {
                    /*: "current..Node.con" := 
                        "current..Node.con \<setminus> {o1}"; */
                    prev = current;
                    current = current.next;
                }
                Node nxt = current.next;
                prev.next = nxt;
                current.next = null;
                //: "current..Node.con" := "{current..Node.data}";
            }
        }
    }

    public static void test()
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
	List l1 = l.copy();
        l1.remove(o2);
        l1.remove(o4);
        l1.remove(o1);
        l1.remove(o1);
	/*
        if (l1.isEmpty()) {
            System.out.println("Oops, the list is empty but should have one element.");
        } else {
            System.out.println("ok1.");
        }
	*/
        l1.remove(o3);
	/*
        if (!l1.isEmpty()) {
            System.out.println("Oops, the list is not empty but should be.");
        } else {
            System.out.println("ok2.");
        }
	*/
    }

    public static void main(String[] args)
    {
	test();
    }
}
