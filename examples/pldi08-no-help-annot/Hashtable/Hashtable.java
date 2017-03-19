public /*: claimedby Hashtable */ class Node {
    public /*: claimedby Hashtable */ Object key;
    public /*: claimedby Hashtable */ Object value;
    public /*: claimedby Hashtable */ Node next;
}

class Hashtable {
    private static Node[] table = null;

    /*:
     public static ghost specvar content :: "(obj * obj) set" = "{}";
     public static ghost specvar init :: "bool" = "False";

     static specvar h :: "(obj \<Rightarrow> int \<Rightarrow> int)";
     vardefs "h == (\<lambda> o1. (\<lambda> i1. ((abs (hashFunc o1)) mod i1)))";

     static specvar abs :: "(int \<Rightarrow> int)" 
     vardefs "abs == (\<lambda> i1. (if (i1 < 0) then (-i1) else i1))";

     private static ghost specvar con :: "obj => (obj * obj) set" = "\<lambda> this. {}";

     invariant ContentDefInv:
     "init \<longrightarrow> content = {(k,v). (k,v) \<in> table.[(h k (table..length))]..con}";

     invariant TableNotNull: "init \<longrightarrow> table \<noteq> null";
     invariant TableHidden: "init \<longrightarrow> table \<in> hidden";
     invariant AllocInv: "table \<in> alloc";

     invariant NodeHidden1: 
     "init \<longrightarrow> (\<forall> i. 0 \<le> i \<and> i < table..length \<and> table.[i] \<noteq> null \<longrightarrow> table.[i] \<in> hidden)";

     invariant NodeHidden2:
     "\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> n..next \<noteq> null \<longrightarrow> n..next \<in> hidden";

     invariant HashInv:
     "init \<longrightarrow> (\<forall> k. 0 \<le> (h k (table..length)) \<and> (h k (table..length)) < table..length)";

     invariant ElementAllocInv:
       "\<forall> i. 0 \<le> i \<and> i < table..length \<longrightarrow> table.[i] \<in> alloc";

     invariant FirstInjInv:
       "init \<longrightarrow> (\<forall> i x y. 
          y = x..next \<and> y \<noteq> null \<and> 0 \<le> i \<and> i < table..length \<longrightarrow> y \<noteq> table.[i])";

     invariant NextInjInv:
       "\<forall> x1 x2 y. y \<noteq> null \<and> y = x1..next \<and> y = x2..next \<longrightarrow> x1 = x2";

     invariant ElementInjInv:
       "init \<longrightarrow> (\<forall> i j.
	  ((0 \<le> i \<and> i < table..length \<and>
	    0 \<le> j \<and> j < table..length \<and>
	    table.[i] \<noteq> null \<and> table.[i] = table.[j]) \<longrightarrow> i = j))";

     invariant ElementTypeInv:
       "\<forall> i. 0 \<le> i \<and> i < table..length \<longrightarrow> table.[i] \<in> Node";

     public ensured invariant SetInv:
       "\<forall> k v0 v1. (k,v0) \<in> content \<and> (k,v1) \<in> content \<longrightarrow> v0 = v1";

     public ensured invariant NonNullInv:
       "\<forall> k v. (k,v) \<in> content \<longrightarrow> k \<noteq> null \<and> v \<noteq> null";

     invariant Coherence: "init \<longrightarrow>
       (\<forall> i k v. 0 \<le> i \<and> i < table..length \<longrightarrow>
           (k,v) \<in> table.[i]..con \<longrightarrow> h k (table..length) = i)";

     invariant ConAlloc:
       "\<forall> z x y. z \<in> Node \<and> z \<in> alloc \<and> (x,y) \<in> z..con \<longrightarrow> x \<in> alloc \<and> y \<in> alloc";

     invariant ConNull:
       "\<forall> x. x \<in> Node \<and> x \<in> alloc \<and> x = null \<longrightarrow> x..con = {}";

     invariant ConDef:
       "ALL x. x : Node & x : Object.alloc & x ~= null -->
          x..con = 
	  {(x..Node.key, x..Node.value)} Un x..Node.next..con &
	  (ALL v. (x..Node.key, v) ~: x..Node.next..con)";

     invariant ConNonNull:
       "ALL z x y. z : Node & z : Object.alloc & z ~= null & 
       (x, y) : z..con --> x ~= null & y ~= null";

    */

    public static void init(int n)
    /*: requires "0 < n"
        modifies content, init
        ensures "init & content = {}" */
    {
	int i = 0;
	table = new /*: hidden */ Node[n];
	
	//: "content" := "{}";
	//: "init" := "True";

    }

    private static int compute_hash(Object o1)
    /*: requires "o1 ~= null & init & theinvs"
        ensures "result = h o1 (table..Array.length) & 0 <= result & 
	         result < table..Array.length &
		 Object.alloc = (old Object.alloc) & theinvs"
    */
    {
        int hc = o1.hashCode();

        if (hc < 0) { hc = -hc; }

        return (hc % table.length);
    }

    public static boolean containsKey(Object k0)
    /*: requires "k0 \<noteq> null \<and> init"
        ensures "result = (EX v. ((k0, v) : content))"
     */
    {
        return containsKey0(k0);
    }

    private static boolean containsKey0(Object k0)
    /*: requires "k0 \<noteq> null \<and> init \<and> theinvs"
        ensures "result = (EX v. ((k0, v) : content)) & theinvs"
    */
    {
	int hc = compute_hash(k0);
	boolean res = bucketContainsKey(hc, k0);
	return res;
    }
    
    private static boolean bucketContainsKey(int bucket_id, Object k0)
    /*: requires "init & theinvs & 0 <= bucket_id & 
                  bucket_id < table..Array.length"
	ensures "result = (EX v. ((k0, v) : table.[bucket_id]..con)) & 
	         theinvs"
     */
    {
        Node current = table[bucket_id];
        while /*: inv "current : Node & current : Object.alloc & theinvs &
		       (EX v. (k0, v) : table.[bucket_id]..con) = 
		       (EX v. (k0, v) : current..con)"
	       */
            (current != null) {
            if (current.key == k0) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public static Object remove1(Object k0)
    /*: requires "init & k0 ~= null & (EX v. (k0, v) : content)"
        modifies content
        ensures "content = old content \<setminus> {(k0, result)} &
	         (k0, result) : old content"
    */
    {
	return remove(k0);
    }

    private static Object remove(Object k0)
    /*: requires "theinvs & (comment ''Init'' init) & k0 ~= null & (EX v. (k0, v) : content)"
        modifies content, con, next, arrayState
        ensures "theinvs &
	         comment ''IndeedRemoved'' (content = old content \<setminus> {(k0, result)}) &
	         comment ''IndeedWasThere'' ((k0, result) : old content) &
		 comment ''frameArray'' (ALL a i. a ~= table --> a.[i] = old (a.[i]))"
    */
    {
	//: private ghost specvar v0 :: obj
	//: havoc v0 suchThat "(k0, v0) : content"

	int hc = compute_hash(k0);
	Node f = table[hc];

	if (f.key == k0) {
	    // assume "False";
	    Node second = f.next;
	    f.next = null;
	    //: "f..con" := "{(f..Node.key, f..Node.value)}";
	    table[hc] = second;
	    //: "content" := "old content \<setminus> {(k0, v0)}";	    
	    return f.value;
	} else {
	    Node prev = f;
	    //: "prev..con" := "prev..con \<setminus> {(k0, v0)}";
	    //: "content" := "old content \<setminus> {(k0, v0)}";
	    Node current = prev.next;
	    while /*: inv "prev \<in> Node \<and> prev \<in> alloc \<and> prev \<noteq> null \<and> prev \<in> hidden \<and>
	              comment ''PrevCon'' (prev..con = 
		     fieldRead (old con) prev \<setminus> {(k0, v0)}) &
	             current : Node & current : Object.alloc & current ~= null &
		    comment ''PrevCurr'' (prev..Node.next = current & prev ~= current) &
		    content = old content \<setminus> {(k0, v0)} &
		    (k0, v0) : current..con &
		    comment ''ConDefInv''
		    (\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> n \<noteq> prev \<longrightarrow>
		    n..con = {(n..key, n..value)} \<union> n..next..con \<and> (\<forall> v. (n..key, v) \<notin> n..next..con)) \<and>
		    comment ''ConIs'' (ALL n. n..con = old (n..con) |
		    n..con = old (n..con) \<setminus> {(k0, v0)}) &
		    null..con = {} &
		    comment ''FConInv'' (f..con = 
		    (fieldRead (old con) f) \<setminus> {(k0, v0)})"
		  */
		(current.key != k0)
                {
                    //: "current..con" := "current..con \<setminus> {(k0, v0)}";

                    prev = current;
                    current = current.next;
                }
	    Node nxt = current.next;
	    prev.next = nxt;
	    current.next = null;

	    //: "current..con" := "{(current..Node.key, current..Node.value)}";
	    return current.value;
	}
    }

    private static void add(Object k0, Object v0)
    /*: requires "(comment ''Init'' init) \<and> k0 \<noteq> null \<and> v0 \<noteq> null \<and> 
                  \<not> (\<exists> v. (k0, v) \<in> content) \<and> theinvs"
        modifies content, arrayState, "new..con", "new..next", "new..value", "new..key"
        ensures "content = old content Un {(k0, v0)} \<and>
	        (\<forall> a i. a \<noteq> table \<longrightarrow> a.[i] = old (a.[i])) \<and> theinvs" */
    {
	int hc = compute_hash(k0);
	Node n = new /*: hidden */ Node();
	n.key = k0;
	n.value = v0;
	Node first = table[hc];
	n.next = first;
	//: "n..con" := "{(k0, v0)} Un first..con";
	table[hc] = n;
	//: "content" := "(old content) Un {(k0, v0)}";
    }

    public static void add1(Object k0, Object v0)
    /*: requires "init & k0 ~= null & v0 ~= null & 
                  ~(EX v. (k0, v) : content)"
        modifies content
        ensures "content = old content Un {(k0, v0)}"
    */
    {
        add(k0, v0);
    }

    public static Object replace(Object k0, Object v0)
    /*: requires "init & k0 ~= null & v0 ~= null & (EX v. (k0, v) : content)"
        modifies content
	ensures "content = old content - {(k0, result)} Un {(k0, v0)} &
                 (k0, result) : old content"
    */
    {
	Object v1 = remove(k0);
	add(k0, v0);
	return v1;
    }

    public static Object put(Object k0, Object v0)
    /*: requires "init & k0 ~= null & v0 ~= null"
        modifies content
	ensures "(result = null --> content = old content Un {(k0, v0)}) &
	         (result ~= null -->
		   content = old content - {(k0, result)} Un {(k0, v0)})"
     */
    {
	if (containsKey0(k0)) {
            Object v1 = remove(k0);
            add(k0, v0);
	    return v1;
	} else {
	    add(k0, v0);
	    return null;
	}
    }

    public static Object get(Object k0)
    /*: requires "(comment ''Init'' init) \<and> k0 \<noteq> null"
        ensures "(result \<noteq> null \<longrightarrow> (k0, result) \<in> content) \<and>
	         (result = null \<longrightarrow> \<not>(\<exists> v. (k0, v) \<in> content))"
	         
    */
    {
	int hc = compute_hash(k0);
	Node current = table[hc];

        while /*: inv "current \<in> Node \<and> current \<in> alloc \<and> alloc = old alloc \<and>
                       comment ''SoFar'' (\<forall> v. ((k0, v) \<in> content) = ((k0, v) \<in> current..con))" */
            (current != null) {
            if (current.key == k0) {
                return current.value;
            }

            current = current.next;
        }

        return null;
    }

    public static boolean isEmpty()
    /*: requires "comment ''Init'' init"
        ensures "result = (content = {})";
    */
    {
	int i = 0;
	while /*: inv "comment ''IBounds'' (0 \<le> i) \<and>
                       (\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> table.[j]..con = \<emptyset>)" */
	    (i < table.length) {
	    if (table[i] != null) {
		return false;
	    }
	    i = i + 1;
	}
	return true;
    }

}
