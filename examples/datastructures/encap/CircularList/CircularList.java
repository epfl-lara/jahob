public /*: claimedby CircularList */ class Node {
    public Node next;
    public Node prev;
    public Object data;

    /*:
      public ghost specvar next1 :: obj = "null";
    */
}

class CircularList
{
    private static Node first;
    private static Node last;
  
    /*:
      public static specvar content :: objset;
      vardefs "content == {d. EX n. n : nodes & n..data = d}";
      
      static specvar nodes :: objset;
      vardefs "nodes == {x. x \<noteq> null \<and> (first,x) \<in> {(v,w). v..next1=w}^*}";

     private static specvar isLast :: "obj \<Rightarrow> bool";
     vardefs "isLast == (\<lambda> x. (first,x) \<in> {(v,w). v..next1=w}^* \<and>
                              x \<noteq> null \<and> x..next1 = null)";

     invariant lastIsLast: "first \<noteq> null \<longrightarrow> isLast last";

     invariant isTree: "tree [next1]";

     invariant firstIsolated: "first ~= null --> (ALL n. n : nodes --> n..next1 ~= first)";
     
     invariant nextDef: "\<forall> x y. x..next = y \<longrightarrow>
         ((x \<notin> nodes \<longrightarrow> y = null) \<and>
	  (x = last \<longrightarrow> y = first) \<and>
	  (x \<in> nodes \<and> x \<noteq> last \<longrightarrow> y = x..next1))"

     invariant prevDef: "\<forall> x y. x..prev = y \<longrightarrow>
         ((x \<notin> nodes \<longrightarrow> y = null) \<and>
	  (x = first \<and> first \<noteq> null \<longrightarrow> y = last) \<and>
	  (x \<in> nodes \<and> x \<noteq> first \<longrightarrow> y..next1 = x))"

     invariant nextNeverNull: "\<forall> x. x \<in> nodes \<longrightarrow> x..next \<noteq> null";

     invariant prevNeverNull: "\<forall> x. x \<in> nodes \<longrightarrow> x..prev \<noteq> null";

     invariant next1isolated: 
     "\<forall> n. n \<noteq> null \<and> n \<notin> nodes \<longrightarrow> 
     n..next1 = null \<and> (\<forall> x. x..next1 \<noteq> n)";

     invariant noDups: "ALL m n. m : nodes & n : nodes & m..data = n..data --> m = n";

    */

    public static void add(Object data)
    /*: requires "data ~: content"
        modifies content
        ensures "content = old content \<union> {data}"
    */
    {
	Node n = new Node();
	n.data = data;
	addNode(n);
    }

    private static void addNode(Node n)
    /*: requires "n..data ~: content & n \<notin> nodes \<and> n \<noteq> null \<and> n..next = null \<and> (\<forall> x. x..next \<noteq> n) & theinvs"
        modifies content, nodes, first, last, next, prev, next1
        ensures "nodes = old nodes Un {n} &
	         content = old content Un {n..data} & theinvs"
    */
    {
	if (first==null) {
	    first = n;
	    n.next = n;
	    n.prev = n;
	    last = n;
	    //: "n..next1" := "null";
	} else {
	    if (first.next==first) {
		last = n;
	    }
	    n.next = first.next;
	    first.next.prev = n;
	    //: "n..next1" := "first..next1";
	    first.next = n;
	    n.prev = first;
	    //: "first..next1" := "n";	    
	}
	//: noteThat inserted: "nodes = old nodes Un {n}";
    }

    public static void remove(Object data)
    /*: modifies content
        ensures "content = old content - {data}"
    */
    {
	Node n = getNode(data);

	if (n != null) {
	    removeNode(n);
	}
    }

    private static Node getNode(Object data)
    /*: requires "theinvs"
        ensures "comment ''nodeFound'' 
                 (result ~= null --> result : nodes & result..Node.data = data) &
		 comment ''nodeNotFound'' (result = null --> data ~: content)"
     */
    {
	if (first == null) {
	    return null;
	}

	Node curr = first;
	//: ghost specvar rnodes :: objset;

	//: "rnodes" := "{x. x ~= null & (curr,x) : {(v,w). v..next1=w}^*}";

	while /*: inv "comment ''inRest''
		       (ALL n. n : nodes & n..Node.data = data --> n : rnodes) &
		       comment ''inNodes'' (curr : nodes) &
		       comment ''rNodesDef''
		       (rnodes = {x. x ~= null & (curr,x) : {(v,w). v..next1=w}^*})" */
	    (true) {
	    if (curr.data == data) {
		return curr;
	    }
	    if (curr == last) {
		//: note notInRest: "ALL n. n : rnodes --> n..Node.data ~= data";
		return null;
	    }
	    curr = curr.next;
	    //: "rnodes" := "{x. x ~= null & (curr,x) : {(v,w). v..next1=w}^*}";
	}
    }

    private static void removeNode(Node n)
    /*: requires "n : nodes & theinvs"
        modifies content, nodes, first, last, next, prev, next1
        ensures "comment ''nodeRemoved'' (nodes = old nodes - {n}) & 
	         comment ''dataRemoved'' (content = old content - {n..data}) &
		 theinvs"
    */
    {
	// noteThat "first ~= null";
	// noteThat "n ~= null";
	if (first.next==first) {
	    // noteThat lone: "n = first";
	    first = null;
	    n.next = null;
	    n.prev = null;
	    last = null;
	} else {
	    Node nxt = n.next;
	    Node prv = n.prev;
	    prv.next = nxt;
	    nxt.prev = prv;
	    n.next = null;
	    n.prev = null;
	    //: "n..next1" := "null";
	    if (n==first) {
		first = nxt;
	    } else {
		if (n==last) {
		    //: "prv..next1" := "null";
		    last = prv;
		} else {
		    //: "prv..next1" := "nxt";
		}
	    }
	}
	//: note removed: "nodes = old nodes - {n}";
    }
}
