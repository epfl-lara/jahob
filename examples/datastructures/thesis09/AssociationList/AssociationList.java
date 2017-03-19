/* Imperative instantiable association list. */

public /*: claimedby AssociationList */ class Node {
    public Object key;
    public Object value;
    public Node next;
    //: public ghost specvar cnt :: "(obj * obj) set" = "\<emptyset>"
}

class AssociationList {
    private Node first;
    /*:
      public specvar contents :: "(obj * obj) set";
      vardefs "contents == first..cnt";
  
      static specvar edge :: "obj \<Rightarrow> obj \<Rightarrow> bool";
      vardefs "edge == (\<lambda>x y. (x \<in> Node \<and> y = x..next) \<or>  
                         (x \<in> AssociationList \<and> y = x..first))";

      invariant CntDef: "\<forall>x. x \<in> Node \<and> x \<in> alloc \<and> x \<noteq> null \<longrightarrow> 
        x..cnt = {(x..key, x..value)} \<union> x..next..cnt \<and> 
        (\<forall>v. (x..key, v) \<notin> x..next..cnt)";
      invariant CntNull: "null..cnt = \<emptyset>";
      invariant CntNonNull:
      "\<forall>z x y. z \<in> Node \<and> z \<in> alloc \<and> (x, y) \<in> z..cnt \<longrightarrow> 
         x \<noteq> null \<and> y \<noteq> null";
      invariant CntAlloc: 
      "\<forall>z x y. z \<in> Node \<and> z \<in> alloc \<and> (x, y) \<in> z..cnt \<longrightarrow> 
         x \<in> alloc \<and> y \<in> alloc";
      invariant InjInv: 
      "\<forall>x1 x2 y. y \<noteq> null \<and> edge x1 y \<and> edge x2 y \<longrightarrow> x1 = x2";
      invariant MapInv: 
      "\<forall>k v0 v1. (k, v0) \<in> contents \<and> (k, v1) \<in> contents \<longrightarrow> v0 = v1";
      invariant NonNullInv: 
      "\<forall>k v. (k, v) \<in> contents \<longrightarrow> k \<noteq> null \<and> v \<noteq> null"; */

    public AssociationList()
    /*: modifies contents
        ensures "contents = \<emptyset>" */
    {
	first = null;
    }

    public boolean containsKey(Object k0)
    //: ensures "result = (\<exists> v. ((k0, v) \<in> contents))"
    {
        return _containsKey(k0);
    }

    private boolean _containsKey(Object k0)
    /*: requires "theinvs"
        ensures "result = (\<exists> v. ((k0, v) \<in> contents)) \<and> theinvs" */
    {
        Node current = first;
        while //: inv "(\<exists> v. (k0, v) \<in> contents) = (\<exists> v. (k0, v) \<in> current..cnt)"
            (current != null) {
            if (current.key == k0) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public void add(Object k0, Object v0)
    /*: requires "k0 \<noteq> null \<and> v0 \<noteq> null \<and> \<not>(\<exists> v. (k0, v) \<in> contents)"
        modifies contents
        ensures "contents = old contents \<union> {(k0, v0)}" */
    {
	_add(k0, v0);
    }

    private void _add(Object k0, Object v0)
    /*: requires "k0 \<noteq> null \<and> v0 \<noteq> null \<and> \<not>(\<exists> v. (k0, v) \<in> contents) \<and> theinvs"
        modifies contents, "new..key", "new..value", "new..next", "new..cnt", first
	ensures "contents = old contents \<union> {(k0, v0)} \<and> theinvs" */
    {
	Node n = new Node();
	n.key = k0;
	n.value = v0;
	n.next = first;
	//: "n..cnt" := "{(k0, v0)} \<union> first..cnt";
	first = n;
    }

    public Object replace(Object k0, Object v0)
    /*: requires "k0 \<noteq> null \<and> v0 \<noteq> null \<and> (\<exists> v. (k0, v) \<in> contents)"
        modifies contents
	ensures "contents = old contents - {(k0, result)} \<union> {(k0, v0)} \<and>
                 (k0, result) \<in> old contents" */
    {
        Object v1 = _remove(k0);
        _add(k0, v0);
        return v1;
    }

    public Object put(Object k0, Object v0)
    /*: requires "k0 \<noteq> null \<and> v0 \<noteq> null"
        modifies contents
	ensures "contents = old contents - {(k0, result)} \<union> {(k0, v0)} \<and>
	         (result = null \<longrightarrow> \<not>(\<exists>v. (k0, v) \<in> old contents)) \<and>
	         (result \<noteq> null \<longrightarrow> (k0, result) \<in> old contents)" */
    {
	if (_containsKey(k0)) {
	    Object v1 = _remove(k0);
	    _add(k0, v0);
	    return v1;
	} else {
	    _add(k0, v0);
	    return null;
	}
    }

    public Object get(Object k0)
    /*: requires "k0 \<noteq> null"
        ensures "((result \<noteq> null) \<longrightarrow> ((k0, result) \<in> contents)) \<and>
	         ((result = null) \<longrightarrow> (\<not>(\<exists> v. (k0, v) \<in> contents)))" */
    {
	Node current = first;
        while //: inv "\<forall> v. ((k0, v) \<in> contents) = ((k0, v) \<in> current..cnt)"
            (current != null) {
            if (current.key == k0) {
                return current.value;
            }
            current = current.next;
        }
        return null;
    }

    public boolean isEmpty()
    //: ensures "result = (contents = \<emptyset>)"
    {
        return (first==null);
    }

    public Object remove(Object k0)
    /*: requires "k0 \<noteq> null \<and> (\<exists>v. (k0, v) \<in> contents)"
        modifies contents
	ensures "contents = old contents - {(k0, result)} \<and> 
	         (result = null \<longrightarrow> \<not>(\<exists>v. (k0, v) \<in> contents)) \<and>
		 (result \<noteq> null \<longrightarrow> (k0, result) \<in> old contents)" */
    {
	if (_containsKey(k0))
	    return _remove(k0);
	else
	    return null;
    }

    private Object _remove(Object k0)
    /*: requires "k0 \<noteq> null \<and> (\<exists> v. (k0, v) \<in> contents) \<and> theinvs"
        modifies contents, first, next, cnt
	ensures "contents = old contents - {(k0, result)} \<and> (k0, result) \<in> old contents \<and> theinvs" */
    {
	//: ghost specvar v0::obj;
	//: havoc v0 suchThat "(k0, v0) \<in> contents";
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
		    contents = old contents - {(k0, v0)} \<and>
		    (\<forall> n. n \<in> AssociationList \<and> n \<in> old alloc \<and> n \<noteq> this \<longrightarrow>
		    n..contents = old (n..contents)) \<and>
		    (k0, v0) \<in> current..cnt \<and>
		    comment ''CntDefInv''
		    (\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> n \<noteq> prev \<longrightarrow>
		    n..cnt = {(n..key, n..value)} \<union> n..next..cnt \<and>
		    (\<forall> v. (n..key, v) \<notin> n..next..cnt)) \<and>
		    (\<forall> n. n..cnt = old (n..cnt) \<or> 
                          n..cnt = old (n..cnt) - {(k0, v0)}) \<and>
		    null..cnt = \<emptyset>"
		  */
		(current.key != k0)
                {
                    //: "current..cnt" := "current..cnt - {(k0, v0)}"; 
                    prev = current;
                    current = current.next;
                }
	    Node tmp = current.next;
	    prev.next = tmp;
	    current.next = null;
	    //: "current..cnt" := "{(current..key, current..value)}";
	    return current.value;
	}
    }
}
