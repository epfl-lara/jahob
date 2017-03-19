/* Imperative instantiable association list. */

public /*: claimedby AssociationList */ class Node {
    public Object key;
    public Object value;
    public Node next;
    //: public ghost specvar cnt :: "(obj * obj) set" = "{}"
}

class AssociationList {
    private static Node first;  
    /*:
    public static specvar content :: "(obj * obj) set";
    vardefs "content == first..cnt";
  
    invariant InjInv:
    "\<forall> x y. x \<in> Node \<and> y \<in> Node \<and> x..next = y & y ~= null \<longrightarrow> first ~= y \<and> (ALL z. z \<in> Node \<and> z..next = y \<longrightarrow> x = z)";

    invariant CntNull:
    "\<forall> x. x \<in> Node \<and> x \<in> alloc \<and> x = null \<longrightarrow> x..cnt = {}";
	  
    invariant CntDef:
    "\<forall> x. x \<in> Node \<and> x \<in> alloc \<and> x \<noteq> null \<longrightarrow>
	  x..cnt = {(x..key, x..value)} \<union> x..next..cnt \<and>
          (\<forall> v. (x..key, v) \<notin> x..next..cnt)";

    public ensured invariant SetInv:
    "\<forall> k v0 v1. (k, v0) \<in> content \<and> (k, v1) \<in> content \<longrightarrow> v0 = v1";
    public ensured invariant NonNullInv:
    "\<forall> k v. (k, v) \<in> content \<longrightarrow> k \<noteq> null \<and> v \<noteq> null";
    invariant CntAlloc:
    "\<forall> z x y. z \<in> Node \<and> z \<in> alloc \<and> (x, y) \<in> z..cnt \<longrightarrow> x \<in> alloc \<and> y \<in> alloc";
    invariant CntNonNull:
    "\<forall> z x y. z \<in> Node \<and> z \<in> alloc \<and> (x, y) \<in> z..cnt \<longrightarrow> x \<noteq> null \<and> y \<noteq> null";
    */

    public static void init()
    /*: modifies "content"
        ensures "content = {}" */
    {
	first = null;
    }

    public static boolean containsKey(Object k0)
    //: ensures "result = (\<exists> v. ((k0, v) \<in> content))"
    {
        return containsKey0(k0);
    }

    private static boolean containsKey0(Object k0)
    /*: requires "theinvs"
        ensures "result = (\<exists> v. ((k0, v) \<in> content)) \<and> theinvs" */
    {
        Node current = first;
        while //: inv "(\<exists> v. (k0, v) \<in> content) = (\<exists> v. (k0, v) \<in> current..cnt)"
            (current != null) {
            if (current.key == k0) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public static void add(Object k0, Object v0)
    /*: requires "k0 \<noteq> null \<and> v0 \<noteq> null \<and> \<not>(\<exists> v. (k0, v) \<in> content)"
        modifies content
        ensures "content = old content \<union> {(k0, v0)}" */
    {
	add0(k0, v0);
    }

    private static void add0(Object k0, Object v0)
    /*: requires "theinvs \<and> k0 \<noteq> null \<and> v0 \<noteq> null \<and> \<not>(\<exists> v. (k0, v) \<in> content)"
        modifies content, "new..key", "new..value", "new..next", "new..cnt", first
        ensures "theinvs \<and> content = old content \<union> {(k0, v0)}" */
    {
	Node n = new Node();
	n.key = k0;
	n.value = v0;
	n.next = first;
	//: "n..cnt" := "{(k0, v0)} \<union> first..cnt";
	first = n;
    }

    public static Object replace(Object k0, Object v0)
    /*: requires "k0 \<noteq> null \<and> v0 \<noteq> null \<and> (\<exists> v. (k0, v) \<in> content)"
        modifies content
	ensures "content = old content - {(k0, result)} \<union> {(k0, v0)} \<and>
                 (k0, result) \<in> old content" */
    {
        Object v1 = remove0(k0);
        add0(k0, v0);
        return v1;
    }

    public static Object put(Object k0, Object v0)
    /*: requires "k0 \<noteq> null \<and> v0 \<noteq> null"
        modifies content
	ensures "content = old content - {(k0, result)} \<union> {(k0, v0)} \<and>
                 ((result \<noteq> null) = ((k0, result) \<in> old content)) \<and>
                 ((result = null) = (\<not>(\<exists> v. (k0, v) \<in> old content)))" */
    {
	if (containsKey0(k0)) {
	    Object v1 = remove0(k0);
	    add0(k0, v0);
	    return v1;
	} else {
	    add0(k0, v0);
	    return null;
	}
    }

    public static Object get(Object k0)
    /*: requires "k0 \<noteq> null"
        ensures "((result \<noteq> null) = ((k0, result) \<in> content)) \<and>
	         ((result = null) = (\<not>(\<exists> v. (k0, v) \<in> content)))" */
    {
	Node current = first;
        while //: inv "\<forall> v. ((k0, v) \<in> content) = ((k0, v) \<in> current..cnt)"
            (current != null) {
            if (current.key == k0) {
                return current.value;
            }
            current = current.next;
        }
        return null;
    }

    public static boolean isEmpty()
    /*: ensures "result = (content = {})"; */
    {
        return (first==null);
    }

    public static Object remove(Object k0)
    /*: requires "k0 \<noteq> null \<and> (\<exists> v. (k0, v) \<in> content)"
        modifies content
        ensures "content = old content - {(k0, result)} \<and>
	         (k0, result) \<in> old content" */
    {
	return remove0(k0);
    }

    private static Object remove0(Object k0)
    /*: requires "theinvs \<and> k0 \<noteq> null \<and> (\<exists> v. (k0, v) \<in> content)"
        modifies content, first, "Node.next", "Node.cnt"
        ensures "theinvs \<and>
	         content = old content - {(k0, result)} \<and>
	         (k0, result) \<in> old content" */
    {
	//: pickWitness v0 :: obj suchThat "(k0, v0) \<in> content";
	Node f = first;
	if (f.key == k0) {
	    Node second = f.next;
	    f.next = null;
	    //: "f..cnt" := "{(f..key, f..value)}";
	    first = second;
	    return f.value;
	} else {
	    Node prev = first;
	    //: "prev..cnt" := "prev..cnt - {(k0, v0)}";
	    Node current = prev.next;
	    while /*: inv "prev \<noteq> null \<and>
		    prev..cnt = prev..(old cnt) - {(k0, v0)} \<and> current \<noteq> null \<and>
		    prev..next = current \<and> prev \<noteq> current \<and>
		    content = old content - {(k0, v0)} \<and>
		    (k0, v0) \<in> current..cnt \<and>
		    comment ''CntDefInv''
		    (\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> n \<noteq> prev \<longrightarrow>
		    n..cnt = {(n..key, n..value)} \<union> n..next..cnt \<and>
		    (\<forall> v. (n..key, v) \<notin> n..next..cnt)) \<and>
		    (\<forall> n. n..cnt = old (n..cnt) \<or> 
                          n..cnt = old (n..cnt) - {(k0, v0)}) \<and>
		    null..cnt = {}"
		  */
		(current.key != k0)
                {
                    //: "current..cnt" := "current..cnt - {(k0, v0)}"; 
                    prev = current;
                    current = current.next;
                }
	    Node nxt = current.next;
	    prev.next = nxt;
	    current.next = null;
	    //: "current..cnt" := "{(current..key, current..value)}";
	    return current.value;
	}
    }
}
