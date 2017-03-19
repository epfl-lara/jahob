public /*: claimedby Hashtable */ class Node {
    public /*: claimedby Hashtable */ Object key;
    public /*: claimedby Hashtable */ Object value;
    public /*: claimedby Hashtable */ Node next;
    /*: 
      public ghost specvar con :: "(obj * obj) set" = "({} :: (obj * obj) set)";
    */
}

class Hashtable {
    private Node[] table = null;

    /*: 
     public ghost specvar content :: "(obj * obj) set";
     public ghost specvar init :: "bool" = "False :: bool";

     private static ghost specvar h :: "(obj => int => int)";

     invariant ContentDefInv:
     "init --> 
      content = 
      {(k, v). (k, v) : table.[(h k (table..Array.length))]..Node.con}";

     public ensured invariant ContentAlloc:
     "ALL x y. 
      (x, y) : content --> (x : Object.alloc & y : Object.alloc)";

     invariant TableNotNull: "init --> table ~= null";
     invariant TableHidden: "init --> table : hidden";
     invariant AllocInv: "table : Object.alloc";

     invariant HashInv:
       "ALL k. 0 <= (h k (table..Array.length)) & 
               (h k (table..Array.length)) < table..Array.length";

     invariant ElementAllocInv:
       "ALL i. 
         0 <= i & i < table..Array.length --> table.[i] : Object.alloc";

     invariant FirstInjInv:
       "init --> 
        (ALL i x y. y = x..Node.next & y ~= null & 0 <= i &
	i < table..Array.length --> y ~= table.[i])";

     invariant NextInjInv:
       "ALL x1 x2 y. 
         y ~= null & y = x1..Node.next & y = x2..Node.next --> x1 = x2";

     invariant ElementInjInv:
       "(ALL i j h1 h2. 
	  ((h1 : Object.alloc & h1 : Hashtable & h1..init & 
	    0 <= i & i < h1..table..Array.length & 
	    h2 : Object.alloc & h2 : Hashtable & h2..init 
	    & 0 <= j & j < h2..table..Array.length & 
	    h1..table.[i] ~= null & 
	    h1..table.[i] = h2..table.[j]) --> (i = j & h1 = h2)))";

     invariant TableInjInv:
       "(ALL h1 h2.
          ((h1 : Object.alloc & h1 : Hashtable & h1..init &
	    h2 : Object.alloc & h2 : Hashtable & h2..init &
	    h1..table = h2..table --> h1 = h2)))";

     invariant ElementTypeInv:
       "ALL i. 0 <= i & i < table..Array.length --> table.[i] : Node";

     public ensured invariant SetInv:
       "ALL k v0 v1. (k, v0) : content & (k, v1) : content --> v0 = v1";

     public ensured invariant NonNullInv:
       "ALL k v. (k, v) : content --> k ~= null & v ~= null";

     invariant Coherence: "init --> 
       (ALL i k v. 0 <= i & i < table..Array.length --> 
       (k,v) : table.[i]..Node.con --> h k (table..Array.length) = i)";

     invariant ConAlloc:
       "ALL z x y. z : Node & z : Object.alloc & (x, y) : z..Node.con -->
        x : Object.alloc & y : Object.alloc";

     invariant ConNull:
       "ALL x. x : Node & x : Object.alloc & x = null --> x..Node.con = {}";

     invariant ConDef:
       "ALL x. x : Node & x : Object.alloc & x ~= null -->
          x..Node.con = 
	  {(x..Node.key, x..Node.value)} Un x..Node.next..Node.con &
	  (ALL v. (x..Node.key, v) ~: x..Node.next..Node.con)";

     invariant ConNonNull:
       "ALL z x y. z : Node & z : Object.alloc & z ~= null & 
       (x, y) : z..Node.con --> x ~= null & y ~= null";
     */
    /*
     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..Node.next) | 
                              (x : Hashtable & 
      (EX i. 0 <= i & i < table..Array.length & y = x..Hashtable.table.[i])))";
    */
    /*
     invariant CorrectnessInv:
       "init --> 
        (ALL k. (EX v. (k, v) : content) = 
	        (EX v. (k, v) : table.[(h k (table..Array.length))]..Node.con))";
    */
    /*
     invariant InjInv:
       "ALL x1 x2 y. y ~= null & edge x1 y & edge x2 y --> x1=x2";
    */

    public Hashtable(int n)
    /*: 
      modifies content, init
      ensures "init & content = {}"
    */
    {
	int i = 0;
	//: "init" := "False";
	table = new /*: hidden */ Node[n];
	
	while /*: inv "(ALL j. 0 <= j & j < i --> table.[j] = null) &
		       (ALL a i. (a : Object.alloc & a : Array & a ~: hidden) -->
		        (a.[i] = (arrayRead (old Array.arrayState) a i)))";
	       */
	    (i < n) {
	    table[i] = null;
	}
	//: "content" := "{}";
	//: "init" := "True";
    }

    private int compute_hash(Object o1)
    /*: requires "True"
        ensures "result = h o1 (table..Array.length) & 0 <= result & 
	         result < table..Array.length &
		 Object.alloc = (old Object.alloc)"
    */
    {
	//:assume "False"
	return o1.hashCode() % table.length;
    }

    public boolean containsKey(Object k0)
    /*: requires "init"
        ensures "result = (EX v. ((k0, v) : content))"
     */
    {
        return containsKey0(k0);
    }

    private boolean containsKey0(Object k0)
    /*: requires "init & theinvs"
        ensures "result = (EX v. ((k0, v) : content)) & theinvs"
    */
    {
	int hc = compute_hash(k0);
	//: noteThat allocSame: "Object.alloc = old Object.alloc";
	/*: noteThat newContent: 
	  "theinv ContentDefInv" from ContentDefInv, allocSame, newContent;
	 */
	/*: noteThat newElemInj: 
	  "theinv ElementInjInv" from ElementInjInv, allocSame, newElemInj;
	 */
	boolean res = bucketContainsKey(hc, k0);
	//: noteThat lemma0: "theinv ContentDefInv & theinv Coherence";
	//: noteThat lemma1: "this : Object.alloc & this : Hashtable & init";
	//: noteThat lemma2: "hc = h k0 (table..Array.length)";
	/*: noteThat lemma3: "(EX v. (k0, v) : content) = 
	      (EX v. (k0, v) : table.[hc]..Node.con)" 
	      from lemma0, lemma1, lemma2;
	*/
	return res;
    }
    
    private boolean bucketContainsKey(int bucket_id, Object k0)
    /*: requires "init & theinvs & 0 <= bucket_id & 
                  bucket_id < table..Array.length"
	ensures "result = (EX v. ((k0, v) : table.[bucket_id]..Node.con)) & 
	         theinvs"
     */
    {
        Node current = table[bucket_id];
        while /*: inv "current : Node & current : Object.alloc & theinvs &
		       (EX v. (k0, v) : table.[bucket_id]..Node.con) = 
		       (EX v. (k0, v) : current..Node.con)"
	       */
            (current != null) {
            if (current.key == k0) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public void add(Object k0, Object v0)
    /*: requires "init & k0 ~= null & v0 ~= null & 
                  ~(EX v. (k0, v) : content)"
        modifies content
        ensures "content = old content Un {(k0, v0)}"
    */
    {
	Node n = new /*: hidden */ Node();
	int hc = compute_hash(k0);
	n.key = k0;
	n.value = v0;
	Node first = table[hc];
	n.next = first;
	//: "n..Node.con" := "{(k0, v0)} Un first..Node.con";
	table[hc] = n;
	//: "content" := "(old content) Un {(k0, v0)}";

	/*: noteThat ThisProps: 
	  "this : old Object.alloc & this : Hashtable & init";
	*/
	//: noteThat AllocChange: "Object.alloc = old Object.alloc Un {n}";
	//: noteThat NewNotHT: "n ~: Hashtable";
	//: noteThat HProp: "hc = h k0 (table..Array.length)";
	//: noteThat NewNotAlloc: "n ~: old Object.alloc";
	/*: noteThat NewNotRefArray:
	  "ALL ht i. ht : old Object.alloc & ht : Hashtable & 
	  0 <= i & i < ht..table..Array.length -->
	  (arrayRead (old Array.arrayState) (ht..table) i) ~= n"
	  from ElementAllocInv, NewNotAlloc, NewNotRefArray;
	 */
	//: noteThat NewTableInj: "theinv TableInjInv";
	/*: noteThat NewContentDef: "theinv ContentDefInv"
	  from ThisProps, ContentDefInv, AllocChange, NewNotHT, HProp, 
	  NewNotRefArray, NewTableInj, HashInv, NewContentDef;
	*/

	/*: noteThat NewElemInj: "theinv ElementInjInv"
	  from ThisProps, ElementInjInv, AllocChange, NewNotHT, 
	  NewNotRefArray, TableInjInv, NewElemInj;
	 */

	/*: noteThat FirstAlloc: "first : old Object.alloc"
	  from ThisProps, HProp, HashInv, ElementAllocInv, FirstAlloc;
	*/

	/*: noteThat FirstNode: "first : Node"
	  from ThisProps, HProp, HashInv, ElementTypeInv, FirstNode;
	*/

	/*: noteThat NewCoherence: "theinv Coherence"
	  from Coherence, AllocChange, NewNotHT, HProp, NewNotRefArray, 
	  NewCoherence;
	 */
	
	//: noteThat NotInContent: "ALL v. (k0, v) ~: old content";
	//: noteThat NewOldNEq: "n ~= first";
	/*: noteThat NewNotRef: "ALL x. x..Node.next ~= n"
	  from NewOldNEq, NewNotAlloc, unalloc_lonely, NewNotRef;
	*/
	/*: noteThat NewConDef: "theinv ConDef" 
	  from ThisProps, NotInContent, ContentDefInv, ConDef, 
	  AllocChange, NewNotRef, HProp, NewConDef;
	 */

	//: noteThat KVNonNull: "k0 ~= null & v0 ~= null";
	/*: noteThat NewConNonNull: "theinv ConNonNull"
	  from ConNonNull, AllocChange, FirstNode, FirstAlloc, 
	  KVNonNull, ConNull, NewConNonNull;
	*/

	//: noteThat NewNode: "n : Node";
	/*: noteThat NewElemType: "theinv ElementTypeInv"
	  from ElementTypeInv, AllocChange, NewNode, NewNotHT, NewElemType;
	 */

	//: noteThat NewAlloc: "n : Object.alloc";
	/*: noteThat NewElemAlloc: "theinv ElementAllocInv"
	  from ElementAllocInv, NewAlloc, AllocChange, NewNotHT, 
	  NewElemAlloc;
	 */

	//: noteThat HCBounds: "0 <= hc & hc < table..Array.length";
	/*: noteThat OldNotRefByNext: 
	  "ALL x. first ~= null --> old (x..Node.next) ~= first"
	  from FirstInjInv, ThisProps, HCBounds, OldNotRefByNext;
	 */
	/*: noteThat NewNextInj: "theinv NextInjInv"
	  from NextInjInv, OldNotRefByNext, NewNextInj;
	 */

	/*: noteThat OldNotRefInTable: 
	  "ALL ht i. ht : Object.alloc & ht : Hashtable & ht..init & 
	  0 <= i & i < ht..table..Array.length & first ~= null --> 
	  ht..table.[i] ~= first"
	  from ThisProps, HCBounds, ElementInjInv, AllocChange, 
	  NewNotHT, NewOldNEq, OldNotRefInTable;
	 */
	/*: noteThat NewFirstInj: "theinv FirstInjInv"
	  from FirstInjInv, AllocChange, NewNotHT, NewNotRef, 
	  OldNotRefByNext, OldNotRefInTable, HCBounds, NewFirstInj;
	 */
    }

    public Object replace(Object k0, Object v0)
    /*: requires "k0 ~= null & v0 ~= null & (EX v. (k0, v) : content)"
        modifies content
	ensures "content = old content - {(k0, result)} Un {(k0, v0)} &
                 (k0, result) : old content"
    */
    {
	Object v1 = remove(k0);
	add(k0, v0);
	return v1;
    }

    public Object put(Object k0, Object v0)
    /*: requires "k0 ~= null & v0 ~= null"
        modifies content
	ensures "(result = null --> content = old content Un {(k0, v0)}) &
	         (result ~= null -->
		   content = old content - {(k0, result)} Un {(k0, v0)})"
     */
    {
	if (containsKey0(k0)) {
	    return replace(k0, v0);
	} else {
	    add(k0, v0);
	    return null;
	}
    }

    public Object get(Object k0)
    /*: requires "k0 ~= null"
        ensures "(result ~= null --> (k0, result) : content) &
	         (result = null --> ~(EX v. (k0, v) : content)) &
		 Object.alloc = old Object.alloc"
	         
     */
    {
	int hc = compute_hash(k0);
	Node current = table[hc];
        while /*: inv "current : Node & current : Object.alloc &
                       (ALL v. ((k0, v) : content) = ((k0, v) : current..Node.con))" */
            (current != null) {
            if (current.key == k0) {
                return current.value;
            }
            current = current.next;
        }
        return null;
    }

    public boolean isEmpty()
    /*: ensures "result = (content = {})";
    */
    {
	int i = 0;
	while (i < table.length) {
	    if (table[i] != null) {
		return false;
	    }
	}
	return true;
    }

    public Object remove(Object k0)
    /*: requires "k0 ~= null & (EX v. (k0, v) : content)"
        modifies content
        ensures "content = old content \<setminus> {(k0, result)} &
	         (k0, result) : old content"
    */
    {
	/*: private ghost specvar v0 :: obj;
	 */
	//: assume "(k0, v0) : content";
	int hc = compute_hash(k0);
	Node f = table[hc];
	if (f.key == k0) {
	    Node second = f.next;
	    f.next = null;
	    //: "f..Node.con" := "{(f..Node.key, f..Node.value)}";
	    table[hc] = second;
	    return f.value;
	} else {
	    Node prev = f;
	    /*: "prev..Node.con" := 
	        "prev..Node.con \<setminus> {(k0, v0)}";
	    */
	    Node current = prev.next;
	    while /*: inv "
		    prev : Node & prev : Object.alloc & prev ~= null &
		    prev..Node.con = 
		     fieldRead (old Node.con) prev \<setminus> {(k0, v0)} &
		    current : Node & current : Object.alloc & current ~= null &
		    prev..Node.next = current & prev ~= current &
		    content = old content \<setminus> {(k0, v0)} &
		    (ALL n. n : Hashtable & n : old Object.alloc & n ~= this -->
		    n..content = old (n..content)) &
		    (k0, v0) : current..Node.con &
		    comment ''ConDefInv''
		    (ALL n. n : Node & n : Object.alloc & n ~= null & n ~= prev -->
		    n..Node.con = {(n..Node.key, n..Node.value)} Un n..Node.next..Node.con &
		    (ALL v. (n..Node.key, v) ~: n..Node.next..Node.con)) &
		    (ALL n. n..Node.con = old (n..Node.con) |
		    n..Node.con = old (n..Node.con) \<setminus> {(k0, v0)}) &
		    null..Node.con = {}"
		  */
		(current.key != k0)
                {
                    /*: "current..Node.con" := 
		      "current..Node.con \<setminus> {(k0, v0)}"; */
                    prev = current;
                    current = current.next;
                }
	    Node nxt = current.next;
	    prev.next = nxt;
	    current.next = null;
	    //: "current..Node.con" := "{(current..Node.key, current..Node.value)}";
	    return current.value;
	}
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
