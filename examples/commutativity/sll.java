/* Note on the tests:
 *
 * Some non commuting methods can be considered commuting if assert checking
 * is disabled because we assume the preconditions with might introduce extra
 * hypotheses that were not obvious.
 *
 *  Example: remove0_precond since if the arguemnt of the second call
 *           is still in the list, it is different from thr first one.
 *
 * Furthermore, remember that equivalence condition now deals only with content
 * which can lead to awkward results like remove0_precond and contains0 commute.
 */


public /*: claimedby SLL */ class Node {
    public Object data;
    public Node next;
    //: public ghost specvar con :: "objset" = "{}"
}

class SLL {
    private Node first;

    /*: 
     public specvar content :: "obj set";
     vardefs "content == first..con";

     public ensured invariant ContentAlloc:
     "\<forall> x. x \<in> content \<longrightarrow> x \<in> alloc";

     private static specvar edge :: "obj \<Rightarrow> obj \<Rightarrow> bool";
     vardefs "edge == (\<lambda> x y. (x \<in> Node \<and> y = x..next) \<or>
                              (x \<in> SLL \<and> y = x..first))";

     invariant InjInv:
     "\<forall> x1 x2 y. y \<noteq> null \<and> edge x1 y \<and> edge x2 y \<longrightarrow> x1=x2";

     invariant AllocInv: "first \<in> alloc";

     public ensured invariant NonNullInv: "\<forall> x. x \<in> content \<longrightarrow> x \<noteq> null";
    
     invariant ConAlloc:
     "\<forall> z x. z \<in> Node \<and> z \<in> alloc \<and> x \<in> z..con \<longrightarrow> x \<in> alloc";

     invariant ConNull:
     "\<forall> x. x \<in> Node \<and> x \<in> alloc \<and> x = null \<longrightarrow> x..con = {}";
	  
     invariant ConDef:
     "\<forall> x. x \<in> Node \<and> x \<in> alloc \<and> x \<noteq> null \<longrightarrow>
           x..con = {x..data} \<union> x..next..con \<and> x..data \<notin> x..next..con";

     invariant ConNonNull:
     "\<forall> z x. z \<in> Node \<and> z \<in> alloc \<and> x \<in> z..con \<longrightarrow> x \<noteq> null"; */

    public SLL()
    /*: 
      modifies content 
      ensures "content = {}"
     */
    {
        first = null;
    }

    private void _remove_precond(Object d0)
    /*: requires "d0 \<noteq> null \<and> d0 \<in> content \<and> theinvs"
        modifies content, first, "Node.con", "Node.next"
        ensures "content = old content \<setminus> {d0}
                 \<and> d0 \<in> old content \<and> theinvs
                 \<and> Object.alloc = old Object.alloc"
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
	    //: "prev..Node.con" := "prev..Node.con \<setminus> {d0}";
	    Node current = prev.next;
	    while /*: inv "
		    prev ~= null & current ~= null &
		    prev..con =  prev..(old con) \<setminus> {d0} &
		    prev..next = current & prev ~= current &
		    content = old content \<setminus> {d0} &
		    (ALL n. n : SLL & n : old Object.alloc & 
		    n ~= this -->
		    n..content = old (n..content)) &
		    d0 : current..con &
		    comment ''ConDefInv''
		    (ALL n. n : Node & n : Object.alloc & n ~= null & n ~= prev
                    --> n..con = {n..data} Un n..next..con &
		        (n..data ~: n..next..con)) &
		    (ALL n. n..con = old (n..con) |
                            n..con = old (n..con) \<setminus> {d0})"
		  */
		(current.data != d0)
                {
                    //: "current..con" := "current..con \<setminus> {d0}";
                    prev = current;
                    current = current.next;
                }
	    Node nxt = current.next;
	    prev.next = nxt;
	    current.next = null;
	    //: "current..con" := "{current..data}";
	}
    }

    private void _remove(Object d0)
    /*: requires "d0 \<noteq> null \<and> theinvs"
        modifies content, first, "Node.con", "Node.next"
        ensures "content = old content - {d0}
                 \<and> Object.alloc = old Object.alloc \<and> theinvs"
     */
    {
        if ( _contains(d0) ) _remove_precond(d0);
    }

    private boolean _contains(Object d0)
    /*: requires "theinvs"
        ensures "result = (d0 \<in> content) \<and> content = old content
                 \<and> Object.alloc = old Object.alloc \<and> theinvs"
     */
    {
        Node current = first;
        while //: inv "(d0 \<in> content) = (d0 \<in> current..Node.con)"
            (current != null) {
            if (current.data == d0) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    private void _add_precond(Object d0)
    /*: requires "d0 \<noteq> null \<and> d0 \<notin> content \<and> theinvs"
        modifies content, first, "new..con", "new..data", "new..next"
        ensures "content = old content \<union> {d0} \<and> theinvs
                 \<and> first..data = d0 \<and> first..next = old first
                 \<and> first \<notin> old Object.alloc
                 \<and> Object.alloc = old Object.alloc Un {first}
                 \<and> (\<forall> sll.
                              (sll \<in> SLL \<and> sll \<in> Object.alloc)
                               \<longrightarrow> sll \<in> old Object.alloc)"
     */
    {
	Node n = new Node();
	n.data = d0;
	n.next = first;
	//: "n..Node.con" := "{d0} Un first..Node.con";
	first = n;
    }

    private void _add(Object d0)
    /*: requires "d0 \<noteq> null \<and> theinvs"
        modifies content, first, "new..con", "new..data", "new..next"
        ensures "content = old content \<union> {d0} \<and> theinvs
                 \<and> (\<forall> sll.
                              (sll \<in> SLL \<and> sll \<in> Object.alloc)
                               \<longrightarrow> sll \<in> old Object.alloc)"
     */
    {
        if ( _contains(d0) ) return;
        _add_precond(d0);
    }

    public void remove(Object d0)
    /*: requires "d0 \<noteq> null"
        modifies content
        ensures "content = old content \<setminus> {d0}
                 \<and> Object.alloc = old Object.alloc"
     */
    {
        _remove(d0);
    }

    public boolean contains(Object d0)
    /*: ensures "result = (d0 \<in> content) \<and> content = old content
                 \<and> Object.alloc = old Object.alloc"
     */
    {
        return _contains(d0);
    }

    public void add(Object d0)
    /*: requires "d0 \<noteq> null"
        modifies content
        ensures "content = old content \<union> {d0}"
     */
    {
        _add(d0);
    }

    public boolean isEmpty()
    /*: ensures "result = (content = {})";
     */
    {
        return (first==null);
    }

    public void add2_precond(Object d0, Object d1)
    /*: requires "d0 \<noteq> null \<and> d0 \<notin> content
                  \<and> d1 \<noteq> null \<and> d1 \<notin> content
                  \<and> d0 \<noteq> d1"
        modifies content
        ensures "content = old content \<union> {d0, d1}
                 \<and> (\<forall> sll.
                              (sll \<in> SLL \<and> sll \<in> Object.alloc)
                               \<longrightarrow> sll \<in> old Object.alloc)"
     */
    {
        _add_precond(d0);
        _add_precond(d1);
    }

    public void add2(Object d0, Object d1)
    /*: requires "d0 \<noteq> null & d1 \<noteq> null"
        modifies content
        ensures "content = old content \<union> {d0, d1}
                 \<and> (\<forall> sll.
                              (sll \<in> SLL \<and> sll \<in> Object.alloc)
                               \<longrightarrow> sll \<in> old Object.alloc)"
     */
    {
        _add(d0);
        _add(d1);
    }

    public void remove2_precond(Object d0, Object d1)
    /*: requires "d0 \<noteq> null \<and> d0 \<in> content
                  \<and> d1 \<noteq> null \<and> d1 \<in> content
                  \<and> d0 \<noteq> d1"
        modifies content
        ensures "content = old content \<setminus> {d0, d1}
                 & Object.alloc = old Object.alloc"
     */
    {
        _remove_precond(d0);
        _remove_precond(d1);
    }

    public void remove2(Object d0, Object d1)
    /*: requires "d0 \<noteq> null \<and> d0 \<in> content
                  \<and> d1 \<noteq> null \<and> d1 \<in> content"
        modifies content
        ensures "content = old content \<setminus> {d0, d1}
                 & Object.alloc = old Object.alloc"
     */
    {
        _remove(d0);
        _remove(d1);
    }

    // meaningless parallelisation since the eauivalence condition does not 
    // rely on a varaible or field, but on the result of the calls
    public boolean contains2(Object d0, Object d1)
    /*: requires "d0 \<noteq> null \<and> d1 \<noteq> null"
        ensures "result = ((d0 \<in> content) \<and> (d1 \<in> content))"
     */
    {
        boolean res = _contains(d0) && _contains(d1);
        return res;
    }

    public void removeAndAdd_precond(Object d0, Object d1)
    /*: requires "d0 \<noteq> null \<and> (d0 \<in> content)
                  \<and> d1 \<noteq> null \<and> (d1 \<notin> content)"
        modifies content
        ensures "content = (old content Un {d1}) \<setminus> {d0}"
     */
    {
        _add_precond(d1);
        _remove_precond(d0);
    }

    public void removeAndAdd(Object d0, Object d1)
    /*: requires "d0 \<noteq> null \<and> d1 \<noteq> null"
        modifies content
        ensures "content = (old content Un {d1}) \<setminus> {d0}"
     */
    {
        _add(d1);
        _remove(d0);
    }
}
