public /*: claimedby Hashtable */ class Node {
    public Object key;
    public Object value;
    public Node next;

    /*:
      public ghost specvar con :: "(obj * obj) set" = "{}";

      invariant ConAlloc:
      "\<forall> x y. (x,y) \<in> con \<longrightarrow> 
       x \<in> alloc \<and> y \<in> alloc";

      invariant ConNull: 
      "null..con = \<emptyset>";

      invariant ConDef:
      "this \<noteq> null \<longrightarrow>
       con = {(key, value)} Un next..con \<and>
       (\<forall> v. (key, v) \<notin> next..con)";

      invariant ConNonNull:
      "\<forall> x y. (x, y) \<in> con \<longrightarrow> 
       x \<noteq> null \<and> y \<noteq> null";
    */
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

     public invariant SetInv:
     "\<forall> k v0 v1. (k,v0) \<in> content \<and> 
      (k,v1) \<in> content \<longrightarrow> v0 = v1";

     invariant ContentDefInv:
     "init \<longrightarrow> 
      content = {(k,v). (k,v) \<in> table.[(h k (table..length))]..con}";

     invariant TableNotNull: 
     "init \<longrightarrow> table \<noteq> null";

     invariant TableHidden: 
     "init \<longrightarrow> table \<in> hidden";

     invariant NodeHidden1: 
     "init \<longrightarrow> 
      (\<forall> i. 0 \<le> i \<and> i < table..length \<and> 
       table.[i] \<noteq> null \<longrightarrow> table.[i] \<in> hidden)";

     invariant NodeHidden2:
     "\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> 
      n \<noteq> null \<and> n..next \<noteq> null \<longrightarrow> 
      n..next \<in> hidden";

     invariant HashInv:
     "init \<longrightarrow> 
      (\<forall> k. 0 \<le> (h k (table..length)) \<and> 
       (h k (table..length)) < table..length)";

     invariant FirstInjInv:
     "init \<longrightarrow> 
      (\<forall> i x y. y = x..next \<and> y \<noteq> null \<and> 
       0 \<le> i \<and> i < table..length \<longrightarrow> 
       y \<noteq> table.[i])";

     invariant NextInjInv:
     "\<forall> x1 x2 y. y \<noteq> null \<and> y = x1..next \<and> 
      y = x2..next \<longrightarrow> x1 = x2";

     invariant ElementInjInv:
     "init \<longrightarrow> 
      (\<forall> i j. 0 \<le> i \<and> i < table..length \<and> 
       0 \<le> j \<and> j < table..length \<and> 
       table.[i] = table.[j] \<and> 
       table.[j] \<noteq> null \<longrightarrow> i = j)";

     invariant Coherence:
     "init \<longrightarrow>
      (\<forall> i k v. 0 \<le> i \<and> i < table..length \<longrightarrow>
       (k,v) \<in> table.[i]..con \<longrightarrow> h k (table..length) = i)";

    */

    public static void init(int n)
    /*: requires "0 < n"
        modifies content, init
        ensures "init \<and> content = {}" */
    {
	int i = 0;
	table = new /*: hidden */ Node[n];
	
	//: "content" := "{}";
	//: "init" := "True";

	{ //: localize;
	//: note ArrayLength: "0 < table..length";
	//: note HashFuncRel: "h = (\<lambda> o1. (\<lambda> i1. ((abs (hashFunc o1)) mod i1)))"; 
        //: note ShowHashInv: "theinv HashInv" from ArrayLength, HashFuncRel;
	}
    }

    private static int compute_hash(Object o1)
    /*: requires "o1 \<noteq> null \<and> init \<and> theinvs"
        ensures "result = h o1 (table..Array.length) \<and> 
	         0 \<le> result \<and> result < table..length \<and>
		 alloc = old alloc \<and> theinvs"
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
	//: note Init: "init";
        //: note HC: "hc = h k0 (table..length)";
        //: note InCon: "res = (\<exists> v. ((k0, v) \<in> table.[hc]..con))";
        /*: note ShowResult: "res = (\<exists> v. ((k0, v) \<in> content))" 
	    from InCon, HC, ContentDefInv, Init; */
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

    private static Object removeFirst(Object k0, int hc)
    /*: requires "comment ''Init'' init \<and> k0 \<noteq> null \<and> 
	          (\<exists> v. (k0, v) \<in> content) \<and>
	          comment ''KFound'' (k0 = table.[hc]..key) \<and> 
		  comment ''HCProps''
	          (0 \<le> hc \<and> hc < table..length \<and> 
		  hc = h k0 (table..length)) \<and> 
	          theinvs"
        modifies content, con, next, arrayState
        ensures "comment ''IndeedRemoved'' 
	         (content = old content \<setminus> {(k0, result)}) \<and>
                 comment ''IndeedWasThere'' ((k0, result) : old content) \<and>
	         comment ''frameArray'' 
	         (\<forall> a i. a \<noteq> table \<longrightarrow> 
		 a.[i] = old (a.[i])) \<and> 
	         theinvs" */
    {
	//: pickWitness v0::obj suchThat InContent: "(k0, v0) \<in> content";

	Node f = table[hc];
        Node second = f.next;
        f.next = null;
        //: "f..con" := "{(f..Node.key, f..Node.value)}";

        table[hc] = second;
        //: "content" := "old content \<setminus> {(k0, v0)}";

	//: note FNonNull: "f \<noteq> null";

	/*: note OldContent: 
            "old content = 
	    {(k,v). (k,v) \<in> old (table.[(h k (table..length))]..con)}"
	    from ContentDefInv, Init; */

	//: note FProps: "f \<in> Node \<and> f \<in> alloc";

        /*: noteThat VFound: "v0 = f..value" 
            from InContent, ContentDefInv, ConDef, KFound, Init,
	    FProps, FNonNull, HCProps;*/

        /*: noteThat Acyclic:
	    "fieldRead (old next) (arrayRead (old arrayState) table hc) \<noteq>
	     (arrayRead (old arrayState) table hc)"; */
	
	/*: note ContentPost: "theinv ContentDefInv" 
	    from OldContent, ElementInjInv, Init, KFound, VFound, Acyclic,
	    ConDef, FProps, FNonNull, HashInv, HCProps; */

	{//: localize;
	 //: note ContentPost: "content = old content \<setminus> {(k0, v0)}";
	 //: note SetPost: "theinv SetInv" from SetInv, ContentPost;
	}

	{//: note NextNull: "(old next) null = null";
	 /*: note CoherencePost: "theinv Coherence"
	     from Coherence, Acyclic, ConDef, ConNull, NextNull, FProps, 
	     HCProps; */
	}

        return f.value;
    }

    private static Object removefromBucket(Object k0, int hc)
    /*: requires "comment ''Init'' init \<and> k0 \<noteq> null \<and> 
	          (\<exists> v. (k0, v) \<in> content) \<and>
	          comment ''KNotFound'' (k0 \<noteq> table.[hc]..key) \<and> 
	          comment ''HCProps'' 
	          (0 \<le> hc \<and> hc < table..length \<and> 
		  hc = h k0 (table..length)) \<and> 
	          theinvs"
        modifies content, con, next, arrayState
        ensures "comment ''IndeedRemoved'' 
	         (content = old content \<setminus> {(k0, result)}) \<and>
                 comment ''IndeedWasThere'' ((k0, result) : old content) \<and>
	         comment ''frameArray'' 
	         (\<forall> a i. a \<noteq> table \<longrightarrow> 
		 a.[i] = old (a.[i])) \<and> 
	         theinvs" */
    {
	//: pickWitness v0::obj suchThat InContent: "(k0, v0) \<in> content";

        Node f = table[hc];
        Node prev = f;

        //: "prev..con" := "prev..con \<setminus> {(k0, v0)}";
        //: "content"   := "old content \<setminus> {(k0, v0)}";

        /*: note InBucket: "(k0, v0) \<in> (fieldRead (old con) f)"
            from InContent, ContentDef, Init, HCProps; */
        /*: note FNonNull: "f \<noteq> null" 
	    from InBucket, HCProps, ConDef, ConNull, Init; */

        Node current = prev.next;
      
	while /*: inv "prev \<in> Node \<and> prev \<in> alloc \<and> prev \<noteq> null \<and> 
	          prev \<in> hidden \<and>
	          comment ''PrevCon'' 
	          (prev..con = 
	          fieldRead (old con) prev \<setminus> {(k0, v0)}) \<and>
	          comment ''PrevNot'' 
	          (\<forall> v. (prev..key, v) \<notin> prev..next..con) \<and>
	          comment ''CurrProps'' (current \<in> Node \<and> current \<in> alloc) \<and> 
	          comment ''CurrNotNull'' (current \<noteq> null) \<and>
	          comment ''PrevCurr'' 
	          (prev..next = current \<and> prev \<noteq> current) \<and>
	          content = old content \<setminus> {(k0, v0)} \<and>
	          (k0, v0) \<in> current..con \<and>
	          comment ''ConDefInv''
		  (\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> n \<noteq> prev \<longrightarrow>
	          n..con = {(n..key, n..value)} \<union> n..next..con \<and> 
	          (\<forall> v. (n..key, v) \<notin> n..next..con)) \<and>
	          comment ''ConLoop'' (ALL n. n..con = old (n..con) \<or> 
	          n..con = old (n..con) \<setminus> {(k0, v0)}) \<and> 
	          comment ''ConNull'' (null..con = \<emptyset>) \<and>
	          comment ''FConInv'' 
	          (f..con = (fieldRead (old con) f) \<setminus> {(k0, v0)})" */
	    (current.key != k0)
        {
            //: "current..con" := "current..con \<setminus> {(k0, v0)}";

	    /*: note CurrCon: "current..con = 
	        fieldRead (old con) current \<setminus> {(k0, v0)}"; */
	    //: note PrevIsNot: "prev..key \<noteq> k0";
	    /*: note OldConDef: "fieldRead (old con) prev = 
	        {(prev..key, prev..value)} \<union> 
	        fieldRead (old con) (prev..next)"; */
	    /*: note PrevConDef: 
	        "prev..con = 
		 {(prev..key, prev..value)} \<union> prev..next..con" 
	        from PrevCurr, PrevCon, CurrCon, OldConDef, PrevIsNot; */

            prev = current;
            current = current.next;

            /*: note ConExceptPrev: 
	        "\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> 
		 n \<noteq> null \<and> n \<noteq> prev \<longrightarrow> 
		 n..con = {(n..key, n..value)} \<union> n..next..con \<and> 
		 (\<forall> v. (n..key, v) \<notin> n..next..con)"
		from PrevConDef, PrevNot, ConDefInv, PrevCurr, NextInjInv, 
		CurrNotNull; */
        }
	
	Node nxt = current.next;
	prev.next = nxt;
	current.next = null;

	//: "current..con" := "{(current..Node.key, current..Node.value)}";

	{
	    //: pickAny x::obj;
	    {
		//: assuming h1: "x : Node & x : Object.alloc & x ~= null";
		//: note n1: "x ~= prev --> fieldRead (old Node.next) x ~= current" from h1, NextInjInv, CurrNotNull, PrevCurr;
		//: note n2: "current..con = {(current..Node.key, current..Node.value)}";
		{
		    //: assuming h2: "x = current";
		    //: note c5: "x..con = {(x..Node.key, x..Node.value)} Un x..Node.next..con" from h1, h2, ConNull;
		}
		{
		    //: assuming h3: "x = prev";
		    //: note n3: "fieldRead (old Node.next) current ~= current" from NextInjInv, CurrNotNull, PrevCurr, CurrProps;			    
		    //: note n4: "prev..next..con = fieldRead (old Node.con) (prev..next)";
		    //: note n5: "fieldRead (old Node.con) prev = {(prev..key, prev..value)} Un fieldRead (old Node.con) current";
		    //: note n6: "fieldRead (old Node.con) current = {(current..key, current..value)} Un fieldRead (old Node.con) (fieldRead (old Node.next) current)";
		    //: note n7: "prev..key ~= k0";

		    {
			//: pickAny k::obj, v::obj;
			{
			    //: assuming h4: "(k, v) : x..con";
			    //: note n8: "k ~= k0";
			    //: note n10: "current..key = k0";
			    //: note c8: "(k, v) : {(x..Node.key, x..Node.value)} Un x..Node.next..con" from h1, h3, h4, PrevCurr, n3, PrevCon, n4, n5, n6, n7, n8, n10;
			}
			//: note c6: "(k, v) : x..con --> (k, v) : {(x..Node.key, x..Node.value)} Un x..Node.next..con" forSuch k, v;
		    }
		    {
			//: pickAny k::obj, v::obj;
			{
			    //: assuming h5: "(k, v) : {(x..Node.key, x..Node.value)} Un x..Node.next..con";
			    //: note n9: "k ~= k0";
			    //: note c9: "(k, v) : x..con" from h1, h3, h5, PrevCurr, n3, n4, PrevCon, n5, n6, n7, n9;
			}
			//: note c7: "(k, v) : {(x..Node.key, x..Node.value)} Un x..Node.next..con --> (k, v) : x..con" forSuch k, v; 
		    }
		    //: note c4: "x..con = {(x..Node.key, x..Node.value)} Un x..Node.next..con" from c6, c7;
		}
		{
		    //: assuming h4: "x ~= current & x ~= prev";
		    //: note c3: "x..con = {(x..Node.key, x..Node.value)} Un x..Node.next..con" from h1, h4, n1, ConDef;
		}
		//: cases "x = current", "x = prev", "x ~= current & x ~= prev" for n4: "x..con = {(x..Node.key, x..Node.value)} Un x..Node.next..con";
		{
		    //: pickAny v::obj;
		    //: note c2: "(x..Node.key, v) ~: x..Node.next..con" forSuch v;
		}
		//: note c1: "x..con = {(x..Node.key, x..Node.value)} Un x..Node.next..con & (ALL v. (x..Node.key, v) ~: x..Node.next..con)";
	    }
	    //: note ConDefPost: "x : Node & x : Object.alloc & x ~= null --> x..con = {(x..Node.key, x..Node.value)} Un x..Node.next..con & (ALL v. (x..Node.key, v) ~: x..Node.next..con)" forSuch x;
	}
	{
	    //: assuming InitHyp: "init";
	    {
		//: pickAny i::int, k::obj, v::obj;
		{
		    //: assuming LhsHyp: "0 <= i & i < table..length & (k, v) : table.[i]..con";
		    //: note NotCurr: "table.[i] ~= current";
		    //: note RhsConc: "h k (table..length) = i" from InitHyp, LhsHyp, Coherence, NotCurr, ConLoop;
		}
		//: note Conc: "0 <= i & i < table..length --> (k, v) : table.[i]..con --> h k (table..length) = i" forSuch i, k, v;
	    }
	    //: note CoherencePost: "ALL i k v. 0 <= i & i < table..length --> (k, v) : table.[i]..con --> h k (table..length) = i";
	}
	{
	    //: assuming InitHyp: "init";
	    //: note OldContent: "old content = {(k,v). (k,v) \<in> old (table.[(h k (table..length))]..con)}" from InitHyp, ContentDef;
	    {
		//: pickAny k::obj, v::obj;
		{
		    //: assuming ForwHyp: "(k, v) : content";
		    //: note NotCurr: "table.[(h k (table..length))] ~= current" from FirstInjInv, InitHyp, ForwHyp, PrevCurr, CurrNotNull, HashInv;
		    //: note ForwConc: "(k, v) : table.[(h k (table..length))]..con" from ForwHyp, OldContent, NotCurr, ConLoop;
		}
		//: note ForwAll: "(k, v) : content --> (k, v) : table.[(h k (table..length))]..con" forSuch k, v;
	    }
	    {
		//: pickAny k::obj, v::obj;
		{
		    //: assuming BackHyp: "(k, v) : table.[(h k (table..length))]..con";
		    //: note NotCurr: "table.[(h k (table..length))] ~= current" from FirstInjInv, InitHyp, BackHyp, PrevCurr, CurrNotNull, HashInv;
		    //: note BackConc: "(k, v) : content" from BackHyp, OldContent, NotCurr, ConLoop, FConInv, HCProps;
		}
		//: note BackAll: "(k, v) : table.[(h k (table..length))]..con --> (k, v) : content" forSuch k, v;
	    }
	    //: note ContentDefPost: "content = {(k, v). (k, v) : table.[(h k (table..length))]..con}" from ForwAll, BackAll;
	}
	
        return current.value;

    }

    private static Object remove(Object k0)
    /*: requires "theinvs \<and> (comment ''Init'' init) \<and> 
                  k0 \<noteq> null \<and> (\<exists> v. (k0, v) \<in> content)"
        modifies content, con, next, arrayState
        ensures "theinvs \<and> 
	         comment ''IndeedRemoved'' 
	         (content = old content \<setminus> {(k0, result)}) \<and> 
	         comment ''IndeedWasThere'' ((k0, result) : old content) \<and> 
		 comment ''frameArray'' 
	         (ALL a i. a ~= table --> a.[i] = old (a.[i]))" */
    {
	//: pickWitness v0::obj suchThat KeyInContent: "(k0, v0) \<in> content";

	int hc = compute_hash(k0);
	Node f = table[hc];

        /*: note HCProps: 
            "0 \<le> hc \<and> hc < table..Array.length \<and> 
	     hc = h k0 (table..length)"; */
	/*: noteThat KeyInBucket: "(k0, v0) \<in> table.[hc]..con" 
	    from HCProps, KeyInContent, ContentDef, Init; */

	if (f.key == k0) {
	    
	    return removeFirst(k0, hc);

	} else {
	  
	    return removefromBucket(k0, hc);
	}
    }

    private static void add(Object k0, Object v0)
    /*: requires "comment ''Init'' init \<and> 
                  k0 \<noteq> null \<and> v0 \<noteq> null \<and> 
                  \<not> (\<exists> v. (k0, v) \<in> content) \<and> theinvs"
        modifies content, arrayState, "new..con", "new..next", "new..value", 
	         "new..key"
        ensures  "content = old content Un {(k0, v0)} \<and>
	          (\<forall> a i. a \<noteq> table \<longrightarrow> 
		  a.[i] = old (a.[i])) \<and> theinvs" */
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

        //: note HCBounds: "0 \<le> hc \<and> hc < table..length";
	//: noteThat NewOldNEq: "n \<noteq> first";

	//: noteThat HProp: "hc = h k0 (table..Array.length)";

	/*: note NewNotRefThisArr: 
	    "\<forall> i. 0 \<le> i \<and> i < table..length \<longrightarrow> 
	      (arrayRead (old arrayState) table i) \<noteq> n";*/

	//: noteThat NewNotAlloc: "n \<notin> old alloc";
	/*: noteThat NewNotRefByNext: "\<forall> x. x..next \<noteq> n"
	    from NewOldNEq, NewNotAlloc, unalloc_lonely; */

	{//: localize;
	//: note NotInOldContent: "\<forall> v. (k0, v) \<notin> old content";
	/*: note NotInOldConFirst: 
	    "\<forall> v. (k0, v) \<notin> (fieldRead (old con) first)"
	    from NotInOldContent, ContentDefInv, Init, HProp; */
	//: note FirstNotN: "first \<noteq> n";
	/*: noteThat ConDefPost: "theinv ConDef" 
	    from ConDef, NewNotRefByNext, FirstNotN, NotInOldConFirst; */
	}

	{
	    //: assuming InitHyp: "init";
	    {
		//: pickAny i::int, k::obj, v::obj;
		//: note g1: "arrayRead (old Array.arrayState) (table) i ~= n";
		{
		    //: assuming h2: "0 <= i & i < table..length & (k,v) : table.[i]..con";
		    //: note c3: "h k (table..length) = i" from InitHyp, h2, Coherence, g1, HProp;
		}
		//: note c2: "0 <= i & i < table..length --> (k,v) : table.[i]..con --> h k (table..length) = i" forSuch i, k, v;
	    }
	    //: note CoherencePost: "ALL i k v. 0 <= i & i < table..length --> (k,v) : table.[i]..con --> h k (table..length) = i";
	}

	//: note ContentPost: "theinv ContentDefInv" from HProp, NewNotRefThisArr, HashInv, ContentDefInv, Init;

	{//: localize;
	/*: noteThat OldNotRefByNext: 
	    "\<forall> x. first \<noteq> null \<longrightarrow> 
	     old (x..next) \<noteq> first"
	    from FirstInjInv, Init, HCBounds; */
	/*: note NextInjPost: "theinv NextInjInv"
	    from NextInjInv, OldNotRefByNext; */
	}
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
	ensures "content = old content - {(k0, result)} Un {(k0, v0)} \<and>
	         (result = null \<longrightarrow> \<not> (\<exists> v. (k0, v) \<in> old content)) \<and>
		 (result \<noteq> null \<longrightarrow> (k0, result) \<in> old content)" */
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
        ensures  "(result \<noteq> null \<longrightarrow> 
	           (k0, result) \<in> content) \<and>
	          (result = null \<longrightarrow> 
		   \<not>(\<exists> v. (k0, v) \<in> content))" */
    {
	// instantiate ContentInst: "theinv ContentDefInv" with "this";
	// mp ContentIs: "this : alloc & this : Hashtable & init --> content = {(k, v). (k, v) \<in> table.[(h k (table..length))]..con}";
	// note ContentIs: "content = {(k, v). (k, v) \<in> table.[(h k (table..length))]..con}" from ContentDefInv, Init;
	int hc = compute_hash(k0);
	Node current = table[hc];

        //: note HCIs: "hc = h k0 (table..length)";
        /*: note InCurrent: 
	    "\<forall> v. (((k0, v) \<in> content) = 
	     ((k0, v) \<in> current..con))" 
	    from ContentDefInv, Init, HCIs; */

        while /*: inv "\<forall> v. ((k0, v) \<in> content) = 
		       ((k0, v) \<in> current..con)" */
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
        ensures "result = (content = {})"; */
    {
	int i = 0;
	while /*: inv "comment ''IBounds'' (0 \<le> i) \<and>
                       (\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> 
		       table.[j]..con = \<emptyset>)" */
	    (i < table.length) {
	    if (table[i] != null) {
		//: note ILT: "i < table..length";
		//: note INonEmpty: "table.[i]..con \<noteq> \<emptyset>";
		/*: note ContentNonEmpty: "content \<noteq> \<emptyset>" 
		    from INonEmpty, ContentDefInv, Coherence, IBounds, ILT, 
		    Init; */
		return false;
	    }
	    i = i + 1;
	}
	/*: note AllEmpty: 
	    "\<forall> j. 0 \<le> j \<and> j < table..length \<longrightarrow> 
	    table.[j]..con = \<emptyset>"; */
	/*: note ContentEmpty: "content = \<emptyset>" 
	    from AllEmpty, ContentDefInv, HashInv, Init; */
	return true;
    }

}
