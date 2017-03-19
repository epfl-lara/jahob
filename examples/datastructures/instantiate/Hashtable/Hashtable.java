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
    private Node[] table = null;

    /*:
     public ghost specvar content :: "(obj * obj) set" = "{}";
     public ghost specvar init :: "bool" = "False";

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
      (\<forall> ht i j. ht \<in> Hashtable \<and> ht \<in> alloc \<and> 
       ht..init \<and> 0 \<le> i \<and> i < ht..table..length \<and> 
       0 \<le> j \<and> j < table..length \<and> 
       ht..table.[i] = table.[j] \<and> 
       table.[j] \<noteq> null \<longrightarrow> ht = this \<and> i = j)";

     invariant Coherence:
     "init \<longrightarrow>
      (\<forall> i k v. 0 \<le> i \<and> i < table..length \<longrightarrow>
       (k,v) \<in> table.[i]..con \<longrightarrow> h k (table..length) = i)";

     invariant TableInjInv: 
     "\<forall> ht. ht..table = table \<and> 
      table \<noteq> null \<longrightarrow> ht = this";

    */

    public Hashtable(int n)
    /*: requires "0 < n"
        modifies content, init
        ensures "init \<and> content = {}" */
    {
	int i = 0;
	table = new /*: hidden */ Node[n];
	
	//: "content" := "{}";
	//: "init" := "True";

	//: note NewNotHT: "table \<notin> Hashtable";

	{ //: localize;
	/*: note ElemInj1: 
            "\<forall> ht1 i j. ht1 \<in> Hashtable \<and> ht1 \<in> alloc \<and> ht1..init \<and> 
             0 \<le> i \<and> i < ht1..table..length \<and> 0 \<le> j \<and> j < table..length \<and> 
             ht1..table.[i] = table.[j] \<and> ht1..table.[i] \<noteq> null \<longrightarrow> ht1 = this \<and> i = j"; */
        /*: note ElemInj2: 
            "\<forall> ht2 i j. ht2 \<in> Hashtable \<and> ht2 \<in> alloc \<and> ht2..init \<and> 0 \<le> i \<and> 
             i < table..length \<and> 0 \<le> j \<and> j < ht2..table..length \<and> 
             table.[i] = ht2..table.[j] \<and> table.[i] \<noteq> null \<longrightarrow> this = ht2 \<and> i = j"; */
        /*: note ElemInjOther:
            "\<forall> ht1 ht2 i j. ht1 \<noteq> this \<and> ht2 \<noteq> this \<and> ht1 \<in> Hashtable \<and> ht1 \<in> alloc \<and> 
             ht1..init \<and> ht2 \<in> Hashtable \<and> ht2 \<in> alloc \<and> ht2..init \<and> 0 \<le> i \<and> 
             i < ht1..table..length \<and> 0 \<le> j \<and> j < ht2..table..length \<and> 
             ht1..table.[i] = ht2..table.[j] \<and> ht1..table.[i] \<noteq> null \<longrightarrow> ht1 = ht2 \<and> i = j"
            from ElementInjInv, NewNotHT; */
	/*: note ElemInjAll: "theinv ElementInjInv" 
	    from ElemInj1, ElemInj2, ElemInjOther; */
	}

	{ //: localize;
        /*: note CohThis: "\<forall> i k v. 0 \<le> i \<and> i < table..length \<and> (k,v) \<in> table.[i]..con \<longrightarrow> 
            h k (table..length) = i"; */
        /*: note CohOther: "\<forall> ht. ht \<noteq> this \<and> ht : alloc \<and> ht \<in> Hashtable \<and> ht..init \<longrightarrow>
            (\<forall> i k v. 0 \<le> i \<and> i < ht..table..length \<and> (k,v) \<in> ht..table.[i]..con \<longrightarrow> 
            h k (ht..table..length) = i)" from Coherence, NewNotHT; */
        /*: note CohAll: "theinv Coherence" from CohThis, CohOther; */
	}

	{ //: localize;
        /*: note FirstInjThis: "\<forall> i x y. y = x..next \<and> y \<noteq> null \<and> 0 \<le> i \<and> 
            i < table..length \<longrightarrow> y \<noteq> table.[i]"; */
        /*: note FirstInjOther: "\<forall> ht. ht : alloc \<and> ht : Hashtable \<and> ht \<noteq> this \<and> 
          ht..init \<longrightarrow> (\<forall> i x y. y = x..next \<and> y \<noteq> null \<and> 0 \<le> i \<and> i < ht..table..length \<longrightarrow> 
          y \<noteq> ht..table.[i])" from FirstInjInv, TableInjInv, NewNotHT; */
        /*: note FirstInjAll: "theinv FirstInjInv" 
            from FirstInjThis, FirstInjOther; */
	}

	{ //: localize;
        //: note TableEmpty: "\<forall> i. table.[i]..con = \<emptyset>";
        /*: note ContentThis: 
            "content = {(k,v). (k,v) \<in> table.[(h k (table..length))]..con}"
            from TableEmpty; */
	/*: note ContentOther: "\<forall> ht. ht : alloc \<and> ht : Hashtable \<and> ht \<noteq> this \<longrightarrow> 
	      ht..content = old (ht..content)"; */
        /*: note ContentPost: "theinv ContentDefInv" 
	    from ContentThis, ContentOther, ContentDef, NewNotHT; */
	}

	{ //: localize;
	/*: note NodeHiddenThis: 
	      "\<forall> i. 0 \<le> i \<and> i < table..length \<and> table.[i] \<noteq> null \<longrightarrow> table.[i] \<in> hidden"; */
	/*: note NodeHiddenOther:
	      "\<forall> ht. ht : alloc \<and> ht : Hashtable \<and> ht..init \<and> ht \<noteq> this \<longrightarrow> 
	      (\<forall> i. 0 \<le> i \<and> i < ht..table..length \<and> ht..table.[i] \<noteq> null \<longrightarrow> 
	      ht..table.[i] \<in> hidden)"
	    from NodeHidden1, TableInjInv, NewNotHT; */
	/*: note NodeHiddenAll: "theinv NodeHidden1" 
	    from NodeHiddenThis, NodeHiddenOther; */
	}

	{ //: localize;
	//: note ArrayLength: "0 < table..length";
	//: note HashFuncRel: "h = (\<lambda> o1. (\<lambda> i1. ((abs (hashFunc o1)) mod i1)))"; 
	/*: note HashThis: 
	    "\<forall> k. 0 \<le> (h k (table..length)) \<and> (h k (table..length)) < table..length"
	    from ArrayLength, HashFuncRel; */
	/*: note HashOther:
	    "\<forall> ht. ht \<noteq> this \<and> ht : alloc \<and> ht : Hashtable \<and> ht..init \<longrightarrow> 
	      (\<forall> k. 0 \<le> (h k (ht..table..length)) \<and> 
	      (h k (ht..table..length)) < ht..table..length)"
	    from HashInv, NewNotHT, TableInjInv; */
        //: note ShowHashInv: "theinv HashInv" from HashThis, HashOther;
	}
    }

    private int compute_hash(Object o1)
    /*: requires "o1 \<noteq> null \<and> init \<and> theinvs"
        ensures "result = h o1 (table..Array.length) \<and> 
	         0 \<le> result \<and> result < table..length \<and>
		 alloc = old alloc \<and> theinvs"
    */
    {
        int hc = o1.hashCode();

        if (hc < 0) { hc = -hc; }

        //: note LengthPos: "0 < table..length";
        //: note ResPos: "0 \<le> (hc mod table..length)" from Branch, LengthPos;
        /*: note ResLt: "(hc mod table..length) < table..length" 
            from Branch, LengthPos; */

        return (hc % table.length);
    }

    public boolean containsKey(Object k0)
    /*: requires "k0 \<noteq> null \<and> init"
        ensures "result = (EX v. ((k0, v) : content))"
     */
    {
        return containsKey0(k0);
    }

    private boolean containsKey0(Object k0)
    /*: requires "k0 \<noteq> null \<and> init \<and> theinvs"
        ensures "result = (EX v. ((k0, v) : content)) & theinvs"
    */
    {
	//: instantiate ContentThis: "theinv ContentDefInv" with "this";
	//: mp ContentRhs: "this \<in> alloc \<and> this \<in> Hashtable \<and> init \<longrightarrow> content = {(k,v). (k, v) \<in> table.[(h k (table..length))]..con}";
	int hc = compute_hash(k0);
	boolean res = bucketContainsKey(hc, k0);
        //: note HC: "hc = h k0 (table..length)";
        //: note InCon: "res = (\<exists> v. ((k0, v) \<in> table.[hc]..con))";
        /*: note ShowResult: "res = (\<exists> v. ((k0, v) \<in> content))" 
	    from InCon, HC, ContentRhs; */
	return res;
    }
    
    private boolean bucketContainsKey(int bucket_id, Object k0)
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

    public Object remove1(Object k0)
    /*: requires "init & k0 ~= null & (EX v. (k0, v) : content)"
        modifies content
        ensures "content = old content \<setminus> {(k0, result)} &
	         (k0, result) : old content"
    */
    {
	return remove(k0);
    }

    private Object removeFirst(Object k0, int hc)
    /*: requires "init \<and> k0 \<noteq> null \<and> 
	          (\<exists> v. (k0, v) \<in> content) \<and>
	          comment ''KFound'' (k0 = table.[hc]..key) \<and> 
		  comment ''HCProps''
	          (0 \<le> hc \<and> hc < table..length \<and> hc = h k0 (table..length)) \<and> 
	          theinvs"
        modifies content, con, next, arrayState
        ensures "comment ''IndeedRemoved'' 
	         (content = old content \<setminus> {(k0, result)}) \<and>
                 comment ''IndeedWasThere'' ((k0, result) : old content) \<and>
	         comment ''frameArray'' 
	         (\<forall> a i. a \<noteq> table \<longrightarrow> a.[i] = old (a.[i])) \<and> 
	         theinvs" */
    {
	//: ghost specvar v0 :: obj;
	//: havoc v0 suchThat InContent: "(k0, v0) \<in> content";

	{ //: localize;
	//: instantiate ThisNodeHidden1: "theinv NodeHidden1" with "this";
	//: mp ThisNodeHidden1Rhs: "this \<in> alloc \<and> this \<in> Hashtable \<and> init \<longrightarrow> (\<forall> i. 0 \<le> i \<and> i < table..length \<and> table.[i] \<noteq> null \<longrightarrow> table.[i] \<in> hidden)";
        //: note HiddenLemma: "null \<in> hidden \<longrightarrow> table.[hc] \<in> hidden" from ThisNodeHidden1Rhs, HCProps;
	}

	Node f = table[hc];
        Node second = f.next;
        f.next = null;
        //: "f..con" := "{(f..Node.key, f..Node.value)}";

        table[hc] = second;
        //: "content" := "old content \<setminus> {(k0, v0)}";

        //: note ThisProps: "this \<in> alloc \<and> this \<in> Hashtable \<and> init";
	//: note FNonNull: "f \<noteq> null";

	{//: localize;
	 //: instantiate ThisContent: "old (theinv ContentDefInv)" with "this";
	 //: note OldContent: "old content = {(k,v). (k,v) \<in> old (table.[(h k (table..length))]..con)}" from ThisContent, ThisProps;
	}

	/*: note FProps: "f \<in> Node \<and> f \<in> alloc" 
	    from unalloc_lonely, array_pointsto, ThisProps; */

	{//: localize;
	 //: instantiate FConDef: "old (theinv ConDef)" with "f";
	 //: noteThat VFound: "v0 = f..value" from InContent, OldContent, FConDef, KFound, FProps, FNonNull, HCProps;
	}

	{//: localize;
	 //: instantiate ThisFirstInj: "old (theinv FirstInjInv)" with "this";
	 /*: noteThat Acyclic:
	     "fieldRead (old next) (arrayRead (old arrayState) table hc) \<noteq> 
	     (arrayRead (old arrayState) table hc)" 
	     from FNonNull, HCProps, ThisFirstInj, ThisProps; */
	}

	{
	    //: pickAny ht::obj;
	    {
		//: assuming h1: "ht : alloc & ht : Hashtable & ht..init";
		{
		    //: assuming NotThisHyp: "ht ~= this";
		    //: note n1: "fieldRead (old Hashtable.content) ht = {(k, v). (k, v) : (fieldRead (old Node.con) (arrayRead (old Array.arrayState) (ht..table) (h k (ht..table..length))))}" from n1, h1, NotThisHyp, ContentDefInv;
		    //: note n2: "ht..table ~= table";
		    {
			//: pickAny k::obj, v::obj;
			{
			    //: assuming h2: "(k, v) : ht..content";
			    //: note n4: "arrayRead (old Array.arrayState) (ht..table) (h k (ht..table..length)) ~= arrayRead (old Array.arrayState) table hc" from ElementInjInv, h1, NotThisHyp, ThisProps, HCProps, HashInv, FNonNull;
			    //: note c4: "(k, v) : ht..table.[(h k (ht..table..length))]..con" from c4, h1, NotThisHyp, h2, n1, n2, n4;
			}
			//: note c3: "(k, v) : ht..content --> (k, v) : ht..table.[(h k (ht..table..length))]..con" forSuch k, v;
		    }
		    {
			//: pickAny k::obj, v::obj;
			{
			    //: assuming h3: "(k, v) : ht..table.[(h k (ht..table..length))]..con";
			    //: note n5: "arrayRead (old Array.arrayState) (ht..table) (h k (ht..table..length)) ~= arrayRead (old Array.arrayState) table hc" from n5, ElementInjInv, h1, NotThisHyp, ThisProps, HCProps, HashInv, FNonNull;
			    //: note c5: "(k, v) : ht..content" from c5, h1, NotThisHyp, h3, n1, n2, n5;
			}
			//: note c2: "(k, v) : ht..table.[(h k (ht..table..length))]..con --> (k, v) : ht..content" forSuch k, v;
		    }
		    //: note ContentOther: "ht..content = {(k, v). (k, v) : ht..table.[(h k (ht..table..length))]..con}" from c2, c3;
		}
		{
		    //: assuming ThisHyp: "ht = this";
		    {//: localize;
		     //: instantiate ThisElementInj: "old (theinv ElementInjInv)" with "this";
		     //: note ThisInj: "\<forall> i j. 0 \<le> i \<and> i < table..length \<and> 0 \<le> j \<and> j < table..length \<and> old (table.[i]) = old (table.[j]) \<and> old (table.[i]) \<noteq> null \<longrightarrow> i = j" from ThisElementInj, ThisProps;
		    }
		    //: note ContentThis: "ht..content = {(k,v). (k,v) \<in> ht..table.[(h k (ht..table..length))]..con}" from OldContent, ThisInj, ThisProps, KFound, VFound, Acyclic, ConDef, FProps, FNonNull, HashInv, HCProps, ThisHyp;
		}
		//: cases "ht = this", "ht ~= this" for "ht..content = {(k, v). (k, v) : ht..table.[(h k (ht..table..length))]..con}" from ContentThis, ContentOther;
		//: note ContentCases2: "ht..content = {(k, v). (k, v) : ht..table.[(h k (ht..table..length))]..con}";
	    }
	    //: note ContentAll: "ht : alloc & ht : Hashtable & ht..init --> ht..content = {(k, v). (k, v) : ht..table.[(h k (ht..table..length))]..con}" forSuch ht;
	}

	/*: note FProps: "f \<in> Node \<and> f \<in> alloc" 
	    from unalloc_lonely, array_pointsto, ThisProps; */

	//: noteThat NextNull: "(old next) null = null";
	/*: noteThat NewCoherence: "theinv Coherence"
	    from Coherence, Acyclic, ConDef, ConNull, NextNull, TableInjInv, 
	    FProps, HCProps; */
	
	/*: note AllHidden1: "theinv NodeHidden1"
	    from NodeHidden1, NodeHidden2, ThisProps,
	      FProps, FNonNull, TableInjInv, TableNotNull; */
		
        /*: note AllHidden2: "theinv NodeHidden2"
	    from NodeHidden2, NodeHidden1, ThisProps; */

	/*: noteThat FirstInjLemma: "theinv FirstInjInv" 
	    from FirstInjInv, NextInjInv; */

 	/*: noteThat ElemInj: "theinv ElementInjInv"
	    from ElementInjInv, FirstInjInv, TableInj, FProps, 
	      FNonNull, HCProps; */

	{//: localize;
	 //: instantiate ThisFirstInj: "old (theinv FirstInjInv)" with "this";
	 //: note FNotRefByNext: "\<forall> x. x..next \<noteq> f" from ThisFirstInj, ThisProps, FNonNull, HCProps, FProps;
	}

	//: note NullProps: "null \<in> alloc \<and> null \<in> Node";
	/*: noteThat NewConDef: "theinv ConDef"
	    from ConDef, ConNull, FNotRefByNext, HCProps, NullProps, FProps; */

        return f.value;
    }

    private Object removefromBucket(Object k0, int hc)
    /*: requires "comment ''Init'' init \<and> k0 \<noteq> null \<and> 
	          (\<exists> v. (k0, v) \<in> content) \<and>
	          comment ''KNotFound'' (k0 \<noteq> table.[hc]..key) \<and> 
	          comment ''HCProps'' 
	          (0 \<le> hc \<and> hc < table..length \<and> hc = h k0 (table..length)) \<and> 
	          theinvs"
        modifies content, con, next, arrayState
        ensures "comment ''IndeedRemoved'' 
	         (content = old content \<setminus> {(k0, result)}) \<and>
                 comment ''IndeedWasThere'' ((k0, result) : old content) \<and>
	         comment ''frameArray'' 
	         (\<forall> a i. a \<noteq> table \<longrightarrow> a.[i] = old (a.[i])) \<and> 
	         theinvs" */
    {
	//: ghost specvar v0 :: obj;
	//: havoc v0 suchThat InContent: "(k0, v0) \<in> content";

        //: note ThisProps: "this \<in> alloc \<and> this \<in> Hashtable \<and> this \<noteq> null";

        Node f = table[hc];
        Node prev = f;

        //: "prev..con" := "prev..con \<setminus> {(k0, v0)}";
        //: "content"   := "old content \<setminus> {(k0, v0)}";

        /*: note InBucket: "(k0, v0) \<in> (fieldRead (old con) f)"
            from InContent, ContentDef, ThisProps, Init, HCProps; */
        /*: note FNonNull: "f \<noteq> null" 
	    from PrevNotNull, InBucket, HCProps, ThisProps, ConDef, ConNull,
	    Init; */

        Node current = prev.next;
      
	/*: note InNext: "(k0, v0) \<in> (fieldRead (old con) current)" 
	    from InBucket, KNotFound, ConDef, unalloc_lonely, array_pointsto, 
	    ThisProps, FNonNull; */

	/*: note CurrNotNull: "current \<noteq> null"
	    from InNext, ConNull; */

	//: note PrevNode: "prev \<in> Node" from array_pointsto, ThisProps;

        /*: note PrevHidden: "prev \<in> hidden" 
            from NodeHidden1, HCProps, Init, ThisProps, FNonNull; */

        /*: note ConPreLoop: "\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> 
	      n \<noteq> prev \<longrightarrow> n..con = {(n..key, n..value)} \<union> n..next..con \<and> 
	      (\<forall> v. (n..key, v) \<notin> n..next..con)"
	    from ConDef, FirstInjInv, Init, ThisProps, HCProps, FNonNull; */

	/*: note ConUncBef: 
	      "\<forall> ht i. ht \<noteq> this \<and> ht \<in> Hashtable \<and> ht \<in> alloc \<and> ht..init \<and> 
	       0 \<le> i \<and> i < ht..table..length \<longrightarrow> 
	       ht..table.[i]..con = old (ht..table.[i]..con)"
	    from ElementInjInv, ThisProps, Init, HCProps, FNonNull; */

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
	          (f..con = (fieldRead (old con) f) \<setminus> {(k0, v0)}) \<and> 
	          comment ''ConUnchanged''
	          (\<forall> ht i. ht \<noteq> this \<and> ht \<in> Hashtable \<and> ht \<in> alloc \<and> 
	          ht..init \<and> 0 \<le> i \<and> i < ht..table..length \<longrightarrow> 
	          ht..table.[i]..con = old (ht..table.[i]..con))" */
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
	        "prev..con = {(prev..key, prev..value)} \<union> prev..next..con" 
	        from PrevCurr, PrevCon, CurrCon, OldConDef, PrevIsNot; */

            prev = current;
            current = current.next;

            /*: note FConLem: 
		  "f..con = (fieldRead (old con) f) \<setminus> {(k0, v0)}"
		from FConInv; */

            /*: note ConUncPre:
		  "\<forall> ht i. ht \<noteq> this \<and> ht \<in> Hashtable \<and> ht \<in> alloc \<and> 
	          ht..init \<and> 0 \<le> i \<and> i < ht..table..length \<longrightarrow> 
	          ht..table.[i]..con = old (ht..table.[i]..con)"
		from ConUnchanged, PrevCurr, FirstInjInv, CurrNotNull; */

            /*: note ConExceptPrev: "\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> 
		  n \<noteq> prev \<longrightarrow> n..con = {(n..key, n..value)} \<union> n..next..con \<and> 
	          (\<forall> v. (n..key, v) \<notin> n..next..con)"
		from PrevConDef, PrevNot, ConDefInv, PrevCurr, NextInjInv, CurrNotNull; */
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
	    //: note ConPost: "x : Node & x : Object.alloc & x ~= null --> x..con = {(x..Node.key, x..Node.value)} Un x..Node.next..con & (ALL v. (x..Node.key, v) ~: x..Node.next..con)" forSuch x;
	}

	{
	    //: pickAny ht::obj;
	    {
		//: assuming h1: "ht : alloc & ht : Hashtable & ht..init";
		{
		    //: pickAny i::int, k::obj, v::obj;
		    {
			//: assuming h2: "0 <= i & i < ht..table..length & (k, v) : ht..table.[i]..con";
			//: note n1: "ht..table.[i] ~= current";
			//: note c3: "h k (ht..table..length) = i" from h1, h2, Coherence, n1, ConLoop;
		    }
		    //: note c2: "0 <= i & i < ht..table..length --> (k, v) : ht..table.[i]..con --> h k (ht..table..length) = i" forSuch i, k, v;
		}
		//: note c1: "ALL i k v. 0 <= i & i < ht..table..length --> (k, v) : ht..table.[i]..con --> h k (ht..table..length) = i";
	    }
	    //: note CoherencePost: "ht : alloc & ht : Hashtable & ht..init --> (ALL i k v. 0 <= i & i < ht..table..length --> (k, v) : ht..table.[i]..con --> h k (ht..table..length) = i)" forSuch ht;
	}

	{
	    //: pickAny ht::obj;
	    {
		//: assuming h1: "ht : alloc & ht : Hashtable & ht..init";
		{
		    //: pickAny i::int, x::obj, y::obj;
		    {
			//: assuming h2: "y = x..next & y ~= null & 0 <= i & i < ht..table..length";
			//: note c4: "y ~= ht..table.[i]" from h1, h2, FirstInjInv, PrevCurr;
		    }
		    //: note c3: "y = x..next & y ~= null & 0 <= i & i < ht..table..length --> y ~= ht..table.[i]" forSuch i, x, y;
		}
		//: note c2: "ALL i x y. y = x..next & y ~= null & 0 <= i & i < ht..table..length --> y ~= ht..table.[i]";
	    }
	    //: note FirstInjPost: "ht : alloc & ht : Hashtable & ht..init --> (ALL i x y. y = x..next & y ~= null & 0 <= i & i < ht..table..length --> y ~= ht..table.[i])" forSuch ht;
	}

	{
	    //: pickAny x::obj;
	    {
		//: assuming h1: "x : alloc & x : Hashtable & x..init";
		//: note n1: "fieldRead (old Hashtable.content) x = {(k, v). (k, v) : fieldRead (old Node.con) (arrayRead (old Array.arrayState) (x..table) (h k (x..table..length)))}" from h1, ContentDefInv;
		//: note n2: "ALL k. 0 <= (h k (x..table..length)) & (h k (x..table..length)) < (x..table..length)" from h1, HashInv;
		{
		    //: assuming h2: "x ~= this";
		    //: note n3: "ALL i. 0 <= i & i < x..table..length --> x..table.[i] ~= current";
		    //: note n4: "ALL i. 0 <= i & i < x..table..length --> x..table.[i]..con = fieldRead (old Node.con) (arrayRead (old Array.arrayState) (x..table) i)" from h1, h2, n3, ConUnchanged;
		    //: note c3: "x..content = {(k, v). (k, v) : x..table.[(h k (x..table..length))]..con}" from h1, h2, n1, n2, n4;
		}
		{ 
		    //: assuming h3: "x = this";
		    //: note n5: "old content = {(k,v). (k,v) \<in> old (table.[(h k (table..length))]..con)}";
		    {
			//: pickAny k::obj, v::obj;
			{
			    //: assuming h4: "(k, v) : content";
			    //: note n6: "table.[(h k (table..length))] ~= current" from FirstInjInv, h1,h3, PrevCurr, CurrNotNull, HashInv;
			    //: note c5: "(k, v) : table.[(h k (table..length))]..con" from h4, n5, n6, ConLoop;
			}
			//: note c6: "(k, v) : content --> (k, v) : table.[(h k (table..length))]..con" forSuch k, v;
		    }
		    {
			//: pickAny k::obj, v::obj;
			{
			    //: assuming h5: "(k, v) : table.[(h k (table..length))]..con";
			    //: note n7: "table.[(h k (table..length))] ~= current" from FirstInjInv, h1, h3, PrevCurr, CurrNotNull, HashInv;
			    //: note c7: "(k, v) : content" from h5, n5, n7, ConLoop, FConInv, HCProps;
			}
			//: note c8: "(k, v) : table.[(h k (table..length))]..con --> (k, v) : content" forSuch k, v;
		    }
		    //: note c4: "content = {(k, v). (k, v) : table.[(h k (table..length))]..con}" from c6, c8;
		}
		//: note c2: "x..content = {(k, v). (k, v) : x..table.[(h k (x..table..length))]..con}" from c3, c4;
	    }
	    //: note ContentDefPost: "x : alloc & x : Hashtable & x..init --> x..content = {(k, v). (k, v) : x..table.[(h k (x..table..length))]..con}" forSuch x;
	}
        return current.value;

    }

    private Object remove(Object k0)
    /*: requires "theinvs \<and> (comment ''Init'' init) \<and> k0 \<noteq> null \<and> 
	         (\<exists> v. (k0, v) \<in> content)"
        modifies content, con, next, arrayState
        ensures "theinvs \<and> 
	         comment ''IndeedRemoved'' 
	         (content = old content \<setminus> {(k0, result)}) \<and> 
	         comment ''IndeedWasThere'' ((k0, result) : old content) \<and> 
		 comment ''frameArray'' 
	         (ALL a i. a ~= table --> a.[i] = old (a.[i]))"
    */
    {
	//: ghost specvar v0::obj;
	//: havoc v0 suchThat KeyInContent: "(k0, v0) \<in> content";

	int hc = compute_hash(k0);
	Node f = table[hc];

        /*: note ThisProps: 
            "this \<in> old alloc \<and> this \<in> alloc \<and> this \<in> Hashtable"; */
        /*: note HCProps: 
            "0 \<le> hc \<and> hc < table..Array.length \<and> hc = h k0 (table..length)"; */
	/*: noteThat KeyInBucket: "(k0, v0) : table.[hc]..con" 
            from HCProps, KeyInContent, ContentDef, Init, ThisProps; */

	if (f.key == k0) {
	    
	    return removeFirst(k0, hc);

	} else {
	  
	    return removefromBucket(k0, hc);
	}
    }

    private void add(Object k0, Object v0)
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

        //: note NewNotHT: "n \<notin> Hashtable";
        //: note ThisProps: "this \<in> alloc \<and> this \<in> old alloc \<and> this \<in> Hashtable";
        //: note HCBounds: "0 \<le> hc \<and> hc < table..length";
	//: noteThat NewOldNEq: "n \<noteq> first";

        //: note ThisTableNotNull: "table \<noteq> null";

	/*: noteThat OldNotRefInTable: 
	  "\<forall> ht i. ht : alloc \<and> ht : Hashtable \<and> ht..init \<and> 0 \<le> i \<and> 
           i < ht..table..length \<and> first \<noteq> null \<longrightarrow> ht..table.[i] \<noteq> first"
	  from OldNotRefInTable, Init, ThisProps, HCBounds, ElementInjInvHash,
	    NewOldNEq, TableInjInvHash, NewNotHT, ThisTableNotNull; */

        //: note HashPost: "theinv HashInv" from HashPost, HashInv, NewNotHT;

	//: note KeyAlloc: "k0 \<in> alloc";
	//: note ValAlloc: "v0 \<in> alloc";
	//: note AllocChanged: "alloc = old alloc Un {n}";
	/*: note FirstProps: 
	    "first \<in> alloc \<and> first \<in> Node \<and> first \<noteq> n" 
	    from unalloc_lonely, AllocChanged, ThisProps, array_pointsto, 
	    NewNotHT; */

	/*: note ConAllocLemma: "theinv ConAlloc"
	    from ConAllocLemma, ConAlloc, KeyAlloc, ValAlloc, FirstProps; */

        /*: note NewHidden2: "n..next \<noteq> null \<longrightarrow> n..next \<in> hidden" 
            from NewHidden2, NodeHidden1, ThisProps, Init, HCBounds; */
	/*: note OldHidden2: 
	    "\<forall> m. m \<noteq> n \<and> m \<in> Node \<and> m \<in> alloc \<and> m \<noteq> null \<and> m..next \<noteq> null \<longrightarrow> 
	     m..next \<in> hidden"; */
	//: note AllHidden2: "theinv NodeHidden2" from AllHidden2, NewHidden2, OldHidden2;

        //: note NewHidden: "n \<in> hidden";
        /*: note ThisHidden1: 
            "\<forall> i. 0 \<le> i \<and> i < table..length \<and> table.[i] \<noteq> null \<longrightarrow> table.[i] \<in> hidden"
            from ThisHidden1, NodeHidden1, NewHidden, ThisProps, Init; */
	/*: note OtherHidden1:
	    "\<forall> ht. ht \<noteq> this \<and> ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init \<longrightarrow> 
	     (\<forall> i. 0 \<le> i \<and> i < ht..table..length \<and> ht..table.[i] \<noteq> null \<longrightarrow> 
	      ht..table.[i] \<in> hidden)" from OtherHidden1, NodeHidden1, NewNotHT; */
	/*: note Hidden1All: "theinv NodeHidden1"
	    from Hidden1All, ThisHidden1, OtherHidden1; */

	//: noteThat AllocChange: "Object.alloc = old Object.alloc Un {n}";
	//: noteThat HProp: "hc = h k0 (table..Array.length)";

	/*: note NewNotRefThisArr: 
	    "\<forall> i. 0 \<le> i \<and> i < table..length \<longrightarrow> 
	      (arrayRead (old arrayState) table i) \<noteq> n";*/
	/*: noteThat NewNotRefArray:
	    "\<forall> a i. 0 \<le> i \<and> i < a..length \<longrightarrow> 
	      (arrayRead (old arrayState) a i) \<noteq> n"; */

	//: noteThat NewNotAlloc: "n \<notin> old alloc";
	/*: noteThat NewNotRefByNext: "\<forall> x. x..next \<noteq> n"
	  from NewOldNEq, NewNotAlloc, unalloc_lonely, NewNotRefByNext; */

	//: note NotInOldContent: "\<forall> v. (k0, v) \<notin> old content";
	/*: note NotInOldConFirst: 
	    "\<forall> v. (k0, v) \<notin> (fieldRead (old con) first)"
	    from NotInOldConFirst, NotInOldContent, ContentDef, ThisProps,
	      Init, HProp; */
	//: note FirstNotN: "first \<noteq> n";
	/*: noteThat NewConDef: "theinv ConDef" 
	  from NewConDef, ConDef, NewNotRefByNext, FirstNotN, 
	    NotInOldConFirst; */

	/*: note ElemInj: "theinv ElementInjInv" 
	    from ElementInjInv, ThisProps, NewNotHT, NewNotRefArray, 
	    TableInjInv, ThisTableNotNull; */

	{
	    //: pickAny ht::obj;
	    {
		//: assuming h1: "ht : alloc & ht : Hashtable & ht..init";
		{
		    //: pickAny i::int, k::obj, v::obj;
		    //: note g1: "arrayRead (old Array.arrayState) (ht..table) i ~= n";
		    //: note g2: "ht : old alloc";
		    {
			//: assuming h2: "0 <= i & i < ht..table..length & (k,v) : ht..table.[i]..con";
			{
			    //: assuming h3: "ht = this";
			    //: note c5: "h k (ht..table..length) = i" from c3, h1, h2, h3, Coherence, g1, g2, HProp;
			}
			{
			    //: assuming h4: "ht ~= this";
			    //: note g3: "ht..table ~= table";
			    //: note c4: "h k (ht..table..length) = i" from c4, h1, h2, h4, Coherence, g1, g2, g3;
			}
			//: note c3: "h k (ht..table..length) = i" from c4, c5;
		    }
		    //: note c2: "0 <= i & i < ht..table..length --> (k,v) : ht..table.[i]..con --> h k (ht..table..length) = i" forSuch i, k, v;
		}
		//: note c1: "ALL i k v. 0 <= i & i < ht..table..length --> (k,v) : ht..table.[i]..con --> h k (ht..table..length) = i";
	    }
	    //: note CohPost: "ht : alloc & ht : Hashtable & ht..init --> (ALL i k v. 0 <= i & i < ht..table..length --> (k,v) : ht..table.[i]..con --> h k (ht..table..length) = i)" forSuch ht;
	}

	{
	    //: pickAny ht::obj;
	    {
		//: assuming NewContentHyp: "ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init";
		//: note ThisContent: "content = {(k,v). (k,v) \<in> table.[(h k (table..length))]..con}" from ThisContent, HProp, NewNotRefThisArr, HashInv, ContentDefInv,  ThisProps, Init;
		{
		    //: assuming OtherHyp: "ht ~= this";
		    //: note OtherContent: "ht..content = {(k,v). (k,v) \<in> ht..table.[(h k (ht..table..length))]..con}" from OtherHyp, NewContentHyp, ContentDefInvHash, NewNotHT, TableInjInvHash, NewNotRefArray, TableNotNullHash, HashInv;
		}

		//: cases "ht = this", "ht ~= this" for NewContentCases: "ht..content = {(k,v). (k,v) \<in> ht..table.[(h k (ht..table..length))]..con}" from ThisContent, OtherContent;
		//: note NewContentConc: "ht..content = {(k,v). (k,v) \<in> ht..table.[(h k (ht..table..length))]..con}";
	    }
	    //: note NewContentDef: "ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init \<longrightarrow> ht..content = {(k,v). (k,v) \<in> ht..table.[(h k (ht..table..length))]..con}" forSuch ht;
	}

	/*: noteThat OldNotRefByNext: 
	  "\<forall> x. first \<noteq> null \<longrightarrow> old (x..next) \<noteq> first"
	  from FirstInjInv, Init, HCBounds, OldNotRefByNext, ThisProps; */

	/*: noteThat NewFirstInj: "theinv FirstInjInv"
	  from FirstInjInv, NewNotRefByNext, OldNotRefByNext, TableInjInv,
	    OldNotRefInTable, HCBounds, NewFirstInj, ThisProps, ElementInjInv,
	    NewNotHT; */

	/*: noteThat NewNextInj: "theinv NextInjInv"
	  from NextInjInv, OldNotRefByNext, NewNextInj; */
    }

    public void add1(Object k0, Object v0)
    /*: requires "init & k0 ~= null & v0 ~= null & 
                  ~(EX v. (k0, v) : content)"
        modifies content
        ensures "content = old content Un {(k0, v0)}"
    */
    {
        add(k0, v0);
    }

    public Object replace(Object k0, Object v0)
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

    public Object put(Object k0, Object v0)
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

    public Object get(Object k0)
    /*: requires "(comment ''Init'' init) \<and> k0 \<noteq> null"
        ensures "(result \<noteq> null \<longrightarrow> (k0, result) \<in> content) \<and>
	         (result = null \<longrightarrow> \<not>(\<exists> v. (k0, v) \<in> content))"
	         
    */
    {
	//: instantiate ContentInst: "theinv ContentDefInv" with "this";
	//: mp ContentIs: "this : alloc & this : Hashtable & init --> content = {(k, v). (k, v) \<in> table.[(h k (table..length))]..con}";
	int hc = compute_hash(k0);
	Node current = table[hc];

        //: note HCIs: "hc = h k0 (table..length)";
        /*: note InCurrent: "\<forall> v. (((k0, v) \<in> content) = ((k0, v) \<in> current..con))" 
	    from ContentIs, HCIs; */

        while /*: inv "\<forall> v. ((k0, v) \<in> content) = ((k0, v) \<in> current..con)" */
            (current != null) {
            if (current.key == k0) {
                return current.value;
            }

            current = current.next;
        }
        return null;
    }

    public boolean isEmpty()
    /*: requires "init"
        ensures "result = (content = {})";
    */
    {
	/*: note ThisProps:
	    "this \<in> alloc \<and> this \<in> Hashtable \<and> init"; */
	  
	int i = 0;
	while /*: inv "comment ''IBounds'' (0 \<le> i) \<and>
                       (\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> table.[j]..con = \<emptyset>)" */
	    (i < table.length) {
	    if (table[i] != null) {
		//: note ILT: "i < table..length";
		//: note INonEmpty: "table.[i]..con \<noteq> \<emptyset>";
		/*: note ContentNonEmpty: "content \<noteq> \<emptyset>" 
		    from INonEmpty, ContentDefInv, Coherence, IBounds, ILT, 
		    ThisProps; */
		return false;
	    }
	    i = i + 1;
	}
	//: note AllEmpty: "\<forall> j. 0 \<le> j \<and> j < table..length \<longrightarrow> table.[j]..con = \<emptyset>";
	/*: note ContentEmpty: "content = \<emptyset>" 
	    from AllEmpty, ContentDefInv, HashInv, ThisProps; */
	return true;
    }

}
