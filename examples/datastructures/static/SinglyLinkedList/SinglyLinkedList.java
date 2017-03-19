public /*: claimedby SinglyLinkedList */ class Node {
    public Object data;
    public Node next;

    /*:
      public ghost specvar con :: "objset" = "{}"

      invariant ConAlloc:
      "\<forall> x. x \<in> con \<longrightarrow> x \<in> alloc";

      invariant ConNull:
      "null..con = {}";
      
      invariant ConDef:
      "this ~= null \<longrightarrow> 
       con = {data} \<union> next..con \<and> data \<notin> next..con";

      invariant ConNonNull:
      "\<forall> x. x \<in> con \<longrightarrow> x \<noteq> null";
    */
}

class SinglyLinkedList {
    private static Node first;

    /*: 
     public static specvar content :: "obj set";
     vardefs "content == first..con";

     public ensured invariant ContentAlloc:
     "\<forall> x. x \<in> content \<longrightarrow> x \<in> alloc";

     public ensured invariant NonNullInv: 
     "\<forall> x. x \<in> content \<longrightarrow> x \<noteq> null";

     invariant InjInv:
     "\<forall> x y. x \<in> Node \<and> y \<in> Node \<and> x..next = y \<and>
      y \<noteq> null \<longrightarrow> first \<noteq> y \<and> 
      (ALL z. z \<in> Node \<and> z..next = y \<longrightarrow> x = z)";
    */

    public static void init()
    /*: 
      modifies content 
      ensures "content = {}"
    */
    {
        first = null;
    }

    public static void remove(Object d0)
    /*: requires "d0 \<noteq> null \<and> d0 \<in> content"
        modifies content
        ensures "content = old content - {d0} \<and> d0 \<in> old content"
    */
    {
	Node f = first;
	if (f.data == d0) {
	    Node second = f.next;
	    f.next = null;
	    //: "f..con" := "{f..data}";
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

    public static boolean contains(Object d0)
    /*: ensures "result = (d0 : content)"
     */
    {
        return contains0(d0);
    }

    private static boolean contains0(Object d0)
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

    public static void add(Object d0)
    /*: requires "d0 ~= null & (d0 ~: content)"
        modifies content
        ensures "content = old content Un {d0}"
     */
    {
	Node n = new Node();
	n.data = d0;
	n.next = first;
	//: "n..Node.con" := "{d0} Un first..Node.con";
	first = n;
    }

    public static boolean isEmpty()
    /*: ensures "result = (content = {})";
    */
    {
        return (first==null);
    }

}
