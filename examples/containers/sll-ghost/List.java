public
 /*: claimedby List */ class Node {
    public Object data;
    public Node next;
    /*: 
      public ghost specvar con :: objset = "{} :: objset";

      public ensured invariant ConAlloc: "con \<subseteq> Object.alloc";

      public invariant ConNull: "this = null --> con = {}";
      public invariant ConDef: "this ~= null --> 
         con = {this..data} Un next..con & 
         data ~: next..con";
    */
}

class List {
   private Node first;

   /*: 
     public specvar content :: objset;
     vardefs "content == first..Node.con";

     public ensured invariant ("ContentAlloc") "content \<subseteq> Object.alloc";

     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..Node.next) | 
                              (x : List & y = x..List.first))";

     invariant ("Inj") "ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2";
   */

    public List()
    /*: 
      modifies content 
      ensures "content = {} & Object.alloc = old Object.alloc"
    */
    {
        first = null;
        // "first..Node.nodes" := "{}";
    }

    public boolean member(Object o1)
    //: ensures "result = (o1 : content) & Object.alloc = old Object.alloc";
    {
        return member1(o1);
    }

    private boolean member1(Object o1)
    /*: requires "theinvs"
        ensures "result = (o1 : content) & theinvs & Object.alloc = old Object.alloc"
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
	         (Object.alloc \<setminus> (old Object.alloc) \<subseteq> Node)"
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

    public boolean isEmpty()
    /*: ensures "result = (content = {})";
    */
    {
        return (first==null);
    }

    public Object getOne()
    /*: requires "content ~= {}"
        ensures "result : content";
    */
    {
        return first.data;
    }

    public void remove(Object o1)
    /*: modifies content
        ensures "content = old content \<setminus> {o1} & Object.alloc = old Object.alloc";
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
        l.remove(o2);
        l.remove(o4);
        l.remove(o1);
        l.remove(o1);
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
