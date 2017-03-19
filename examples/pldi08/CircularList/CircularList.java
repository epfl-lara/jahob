class Node {
    public /*: claimedby CircularList */ Node next;
    public /*: claimedby CircularList */ Node prev;
}

class CircularList
{
    private static Node first;
    private static Node last;
  
   /*:
     private static ghost specvar next1 :: "obj \<Rightarrow> obj" = "(\<lambda> x. null)";

     public static specvar content :: objset;
     vardefs "content == {x. x \<noteq> null \<and> (first,x) \<in> {(v,w). v..next1=w}^*}";

     private static specvar isLast :: "obj \<Rightarrow> bool";
     vardefs "isLast == (\<lambda> x. (first,x) \<in> {(v,w). v..next1=w}^* \<and>
                              x \<noteq> null \<and> x..next1 = null)";
     invariant lastIsLast: "first \<noteq> null \<longrightarrow> isLast last";

     invariant firstIsolated: "first \<noteq> null \<longrightarrow> (\<forall> n. n..next1 \<noteq> first)";
     
     invariant isTree: "tree [next1]";

     invariant nextDef: "\<forall> x y. next x = y \<longrightarrow>
         ((x = last \<longrightarrow> y = first) \<and>
	  (x \<in> content \<and> x \<noteq> last \<longrightarrow> y = x..next1) \<and>
	  (x \<notin> content \<longrightarrow> y=null))"

     invariant prevDef: "\<forall> x y. prev x = y \<longrightarrow>
         ((x \<notin> content \<longrightarrow> y = null) \<and>
	  (x = first \<and> first \<noteq> null \<longrightarrow> y = last) \<and>
	  (x \<in> content \<and> x \<noteq> first \<longrightarrow> y..next1 = x))"

     invariant nextNeverNull: "\<forall> x. x \<in> content \<longrightarrow> x..next \<noteq> null";
     invariant prevNeverNull: "\<forall> x. x \<in> content \<longrightarrow> x..prev \<noteq> null";

     invariant next1isolated: "\<forall> n. n \<noteq> null \<and> n \<notin> content \<longrightarrow> isolated n";
     private static specvar isolated :: "obj \<Rightarrow> bool";
     vardefs "isolated == (\<lambda> n. n..next1 = null \<and> (\<forall> x. x \<noteq> null \<longrightarrow> x..next1 \<noteq> n))";
   */

    public static void add(Node n)
    /*: requires "n \<notin> content \<and> n \<noteq> null \<and> n..next = null \<and> (\<forall> x. x..next \<noteq> n)"
        modifies content
        ensures "content = old content \<union> {n}"
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
	//: noteThat inserted: "content = old content Un {n}";
    }

    public static void remove(Node n)
    /*: requires "n : content"
        modifies content
        ensures "comment ''removePost'' (content = old content - {n})"
    */
    {
	//: noteThat "first ~= null";
	//: noteThat "n ~= null";
	if (first.next==first) {
	    //: noteThat lone: "n = first";
	    first = null;
	    n.next = null;
	    n.prev = null;	    
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
		    //: "last" := "prv";
		} else {
		    //: "prv..next1" := "nxt";
		}
	    }
	}
    }
}
