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
       con = {(key, value)} \<union> next..con \<and>
       (\<forall> v. (key, v) \<notin> next..con)";

      invariant ConNonNull:
      "\<forall> x y. (x, y) \<in> con \<longrightarrow> 
       x \<noteq> null \<and> y \<noteq> null";
    */
}

public class Hashtable {
    private Node[] table = null;

    /*:
     public ghost specvar contents :: "(obj * obj) set" = "{}";
     public ghost specvar init :: "bool" = "False";

     static specvar h :: "(obj \<Rightarrow> int \<Rightarrow> int)";
     vardefs "h == (\<lambda> o1. (\<lambda> i1. ((abs (hashFunc o1)) mod i1)))";

     static specvar abs :: "(int \<Rightarrow> int)" 
     vardefs "abs == (\<lambda> i1. (if (i1 < 0) then (-i1) else i1))";

     public invariant MapInv:
     "\<forall> k v0 v1. (k,v0) \<in> contents \<and> 
      (k,v1) \<in> contents \<longrightarrow> v0 = v1";

     invariant ContentsDefInv:
     "init \<longrightarrow> 
      contents = {(k,v). (k,v) \<in> table.[(h k (table..length))]..con}";

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

    public Hashtable()
    /*: modifies contents, init
        ensures "init \<and> contents = \<emptyset>" */
    {
	table = new /*: hidden */ Node[11];

	//: "contents" := "\<emptyset>";
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
        /*: note CohOther: "\<forall> ht. ht \<noteq> this \<and> ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init \<longrightarrow>
            (\<forall> i k v. 0 \<le> i \<and> i < ht..table..length \<and> (k,v) \<in> ht..table.[i]..con \<longrightarrow> 
            h k (ht..table..length) = i)" from Coherence, NewNotHT; */
        /*: note CohAll: "theinv Coherence" from CohThis, CohOther; */
	}

	{ //: localize;
        /*: note FirstInjThis: "\<forall> i x y. y = x..next \<and> y \<noteq> null \<and> 0 \<le> i \<and> 
            i < table..length \<longrightarrow> y \<noteq> table.[i]"; */
        /*: note FirstInjOther: "\<forall> ht. ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht \<noteq> this \<and> 
          ht..init \<longrightarrow> (\<forall> i x y. y = x..next \<and> y \<noteq> null \<and> 0 \<le> i \<and> i < ht..table..length \<longrightarrow> 
          y \<noteq> ht..table.[i])" from FirstInjInv, TableInjInv, NewNotHT; */
        /*: note FirstInjAll: "theinv FirstInjInv" 
            from FirstInjThis, FirstInjOther; */
	}

	{ //: localize;
        //: note TableEmpty: "\<forall> i. table.[i]..con = \<emptyset>";
        /*: note ContentsThis: 
            "contents = {(k,v). (k,v) \<in> table.[(h k (table..length))]..con}"
            from TableEmpty; */
	/*: note ContentsOther: "\<forall> ht. ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht \<noteq> this \<longrightarrow> 
	      ht..contents = old (ht..contents)"; */
        /*: note ContentsPost: "theinv ContentsDefInv" 
	    from ContentsThis, ContentsOther, ContentsDef, NewNotHT; */
	}

	{ //: localize;
	/*: note NodeHiddenThis: 
	      "\<forall> i. 0 \<le> i \<and> i < table..length \<and> table.[i] \<noteq> null \<longrightarrow> table.[i] \<in> hidden"; */
	/*: note NodeHiddenOther:
	      "\<forall> ht. ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init \<and> ht \<noteq> this \<longrightarrow> 
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
	    "\<forall> ht. ht \<noteq> this \<and> ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init \<longrightarrow> 
	      (\<forall> k. 0 \<le> (h k (ht..table..length)) \<and> 
	      (h k (ht..table..length)) < ht..table..length)"
	    from HashInv, NewNotHT, TableInjInv; */
        //: note ShowHashInv: "theinv HashInv" from HashThis, HashOther;
	}
    }

    private int compute_hash(Object o1)
    /*: requires "o1 \<noteq> null \<and> init \<and> theinvs"
        ensures "result = h o1 (table..length) \<and> 
	         0 \<le> result \<and> result < table..length \<and>
		 alloc = old alloc \<and> theinvs"
    */
    {
        int hc = o1.hashCode();

        if (hc < 0) { hc = -hc; }

        //: note LengthPos: "0 < table..length";
        //  note ResPos: "0 \<le> (hc mod table..length)" from TrueBranch, FalseBranch, LengthPos;
        /*: note ResLt: "(hc mod table..length) < table..length" 
            from TrueBranch, FalseBranch, LengthPos; */

        return (hc % table.length);
    }

    public boolean containsKey(Object k0)
    /*: requires "init \<and> k0 \<noteq> null"
        ensures "result = (\<exists> v. ((k0, v) \<in> contents))" */
    {
        return _containsKey(k0);
    }

    private boolean _containsKey(Object k0)
    /*: requires "k0 \<noteq> null \<and> init \<and> theinvs"
        ensures "result = (\<exists> v. ((k0, v) \<in> contents)) \<and> theinvs"
    */
    {
	//: instantiate ContentsThis: "theinv ContentsDefInv" with "this";
	//: mp ContentsRhs: "this \<in> alloc \<and> this \<in> Hashtable \<and> init \<longrightarrow> contents = {(k,v). (k, v) \<in> table.[(h k (table..length))]..con}";
        int hc = compute_hash(k0);
	boolean res = bucketContainsKey(hc, k0);
	//: note HC: "hc = h k0 (table..length)";
	//: note InCon: "res = (\<exists> v. ((k0, v) \<in> table.[hc]..con))";
	/*: note ShowResult: "res = (\<exists> v. ((k0, v) \<in> contents))" 
	    from InCon, HC, ContentsRhs; */
	return res;
    }
    
    private boolean bucketContainsKey(int bucket_id, Object k0)
    /*: requires "init \<and> 0 \<le> bucket_id \<and> bucket_id < table..length \<and> 
                  theinvs "
	ensures "result = (\<exists>v.((k0, v) \<in> table.[bucket_id]..con)) \<and> 
	         theinvs"
     */
    {
        Node curr = table[bucket_id];
        while /*: inv "(\<exists>v.(k0, v) \<in> table.[bucket_id]..con) = 
		       (\<exists>v.(k0, v) \<in> curr..con)"
	       */
            (curr != null) {
            if (curr.key == k0)
                return true;
            curr = curr.next;
        }
        return false;
    }

    public Object remove(Object k0)
    /*: requires "init \<and> k0 \<noteq> null"
        modifies contents
        ensures "contents = old contents \<setminus> {(k0, result)} \<and>
	         (result = null \<longrightarrow> \<not>(\<exists>v0. (k0,v0) \<in> old contents)) \<and>
		 (result \<noteq> null \<longrightarrow> (k0,result) \<in> old contents)" */
    {
	if (!_containsKey(k0))
	    return null;
	else
	    return _remove(k0);
    }

    private Object removeFirst(Object k0, int hc)
    /*: requires "init \<and> k0 \<noteq> null \<and> 
	          (\<exists> v. (k0, v) \<in> contents) \<and>
	          comment ''KFound'' (k0 = table.[hc]..key) \<and> 
		  comment ''HCProps''
	          (0 \<le> hc \<and> hc < table..length \<and> hc = h k0 (table..length)) \<and> 
	          theinvs"
        modifies contents, con, next, arrayState
        ensures "(contents = old contents \<setminus> {(k0, result)}) \<and>
                 comment ''C2'' ((k0, result) \<in> old contents) \<and>
		 comment ''C3'' (\<forall> a i. a \<noteq> table \<longrightarrow> a.[i] = old (a.[i])) \<and> 
	         theinvs" */
    {
	//: ghost specvar v0 :: obj;
	//: havoc v0 suchThat InContents: "(k0, v0) \<in> contents";

	Node f = table[hc];
        Node second = f.next;
        f.next = null;
        //: "f..con" := "{(f..key, f..value)}";

        table[hc] = second;
        //: "contents" := "old contents \<setminus> {(k0, v0)}";

        //: note ThisProps: "this \<in> alloc \<and> this \<in> Hashtable \<and> init";
	//: note OldContents: "old contents = {(k,v). (k,v) \<in> old (table.[(h k (table..length))]..con)}" from ContentsDefInv, ThisProps;
	//: note FNonNull: "f \<noteq> null";
	//: note FProps: "f \<in> Node \<and> f \<in> alloc" from unalloc_lonely, array_pointsto, ThisProps;
	//: note VFound: "v0 = f..value" from InContents, OldContents, ConDef, KFound, FProps, FNonNull, HCProps;

	//: note Acyclic: "fieldRead (old next) f \<noteq> f" from FNonNull, HCProps, FirstInjInv, ThisProps;

	{
	    //: pickAny ht::obj suchThat ContentsDefHyp: "ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init";
	    //: note ContentsThis: "ht = this \<longrightarrow> ht..contents = {(k,v). (k,v) \<in> ht..table.[(h k (ht..table..length))]..con}" from OldContents, ElementInjInv, Acyclic, ThisProps, KFound, VFound, ConDef, FProps, FNonNull, HashInv, HCProps;
	    {
		//: assuming NotThisHyp: "ht \<noteq> this";
		//: note OldHTContents: "fieldRead (old Hashtable.contents) ht = {(k, v). (k, v) \<in> (fieldRead (old con) (arrayRead (old arrayState) (ht..table) (h k (ht..table..length))))}" from ContentsDefHyp, NotThisHyp, ContentsDefInv;
		//: note TableNotEq: "ht..table \<noteq> table";
		/*: note ContentsOther: "ht..contents = {(k, v). 
		    (k, v) \<in> ht..table.[(h k (ht..table..length))]..con}"
		    from ContentsDefHyp, NotThisHyp, HashInv, 
		    ElementInjInv, HCProps, ThisProps, FNonNull, 
		    OldHTContents, TableNotEq; */
	    }
	    //: cases "ht = this", "ht \<noteq> this" for ContentsCases: "ht..contents = {(k, v). (k, v) \<in> ht..table.[(h k (ht..table..length))]..con}" from ContentsThis, ContentsOther;
	    //: note ContentsDefPostCond: "ht..contents = {(k, v). (k, v) \<in> ht..table.[(h k (ht..table..length))]..con}" from ContentCases forSuch ht;
	}

	/*: note CoherencePostCond: "theinv Coherence" from Coherence, Acyclic, ConDef, ConNull, FNonNull, TableInjInv, FProps, HCProps; */

        return f.value;
    }

    private Object removeFromBucket(Object k0, int hc)
    /*: requires "comment ''Init'' init \<and> k0 \<noteq> null \<and> 
	          (\<exists>v.(k0, v) \<in> contents) \<and>
	          comment ''KNotFound'' (k0 \<noteq> table.[hc]..key) \<and> 
	          comment ''HCProps'' 
	          (0 \<le> hc \<and> hc < table..length \<and> hc = h k0 (table..length)) \<and> 
	          theinvs"
        modifies contents, con, next, arrayState
        ensures "(contents = old contents \<setminus> {(k0, result)}) \<and>
                 ((k0, result) \<in> old contents) \<and>
	         (\<forall>a i. a \<noteq> table \<longrightarrow> a.[i] = old (a.[i])) \<and> 
	         theinvs" */
    {
	//: ghost specvar v0 :: obj;
	//: havoc v0 suchThat InContents: "(k0, v0) \<in> contents";

        Node f = table[hc];
        Node prev = f;

	/*: note InBucket: "(k0, v0) \<in> prev..con" from InContents, 
	    ContentsDefInv, thisNotNull, thisType, Init, HCProps; */
	/*: note PrevNotNull: "prev \<noteq> null" 
	    from InBucket, ConDef, ConNull; */

        //: "prev..con" := "prev..con \<setminus> {(k0, v0)}";
        //: "contents"   := "old contents \<setminus> {(k0, v0)}";

        Node curr = prev.next;
      
        /*: note PrevHidden: "prev \<in> hidden" 
            from NodeHidden1, thisNotNull, thisType, PrevNotNull, Init, HCProps; */
        /*: note ConPreLoop: "\<forall>n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> 
	    n \<noteq> prev \<longrightarrow> n..con = {(n..key, n..value)} \<union> n..next..con \<and> 
	    (\<forall>v.(n..key, v) \<notin> n..next..con)"
	    from ConDef, FirstInjInv, Init, HCProps, thisNotNull, thisType, PrevNotNull; */

	/*: note ConUnchangedPreLoop: 
	    "\<forall>ht i. ht \<noteq> this \<and> ht \<in> Hashtable \<and> ht \<in> alloc \<and> ht..init \<and> 
	     0 \<le> i \<and> i < ht..table..length \<longrightarrow> 
	     ht..table.[i]..con = old (ht..table.[i]..con)"
	     from ElementInjInv, thisType, PrevNotNull, Init, HCProps; */

	while /*: inv "prev \<in> Node \<and> prev \<in> alloc \<and> prev \<noteq> null \<and> 
	          prev \<in> hidden \<and>
	          comment ''PrevCon'' 
	          (prev..con = 
	          fieldRead (old con) prev \<setminus> {(k0, v0)}) \<and>
	          comment ''PrevNot'' 
	          (\<forall>v.(prev..key, v) \<notin> prev..next..con) \<and>
	          comment ''CurrProps'' (curr \<in> Node \<and> curr \<in> alloc) \<and> 
	          comment ''CurrNotNull'' (curr \<noteq> null) \<and>
	          comment ''PrevCurr'' 
	          (prev..next = curr \<and> prev \<noteq> curr) \<and>
	          contents = old contents \<setminus> {(k0, v0)} \<and>
	          (k0, v0) \<in> curr..con \<and>
	          comment ''ConDefInv''
		  (\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> n \<noteq> prev \<longrightarrow>
	          n..con = {(n..key, n..value)} \<union> n..next..con \<and> 
	          (\<forall>v.(n..key, v) \<notin> n..next..con)) \<and>
	          comment ''ConLoop'' (\<forall>n. n..con = old (n..con) \<or> 
	          n..con = old (n..con) \<setminus> {(k0, v0)}) \<and> 
	          (null..con = \<emptyset>) \<and>
	          comment ''FConInv'' 
	          (f..con = (fieldRead (old con) f) \<setminus> {(k0, v0)}) \<and> 
	          comment ''ConUnchanged''
	          (\<forall>ht i. ht \<noteq> this \<and> ht \<in> Hashtable \<and> ht \<in> alloc \<and> 
	          ht..init \<and> 0 \<le> i \<and> i < ht..table..length \<longrightarrow> 
	          ht..table.[i]..con = old (ht..table.[i]..con))" */
	    (curr.key != k0)
        {
            //: "curr..con" := "curr..con \<setminus> {(k0, v0)}";

	    /*: note CurrCon: "curr..con = 
	        fieldRead (old con) curr \<setminus> {(k0, v0)}"; */
	    //: note PrevIsNot: "prev..key \<noteq> k0";
	    /*: note OldConDef: "fieldRead (old con) prev = 
	        {(prev..key, prev..value)} \<union> 
	        fieldRead (old con) (prev..next)"; */
	    /*: note PrevConDef: 
	        "prev..con = {(prev..key, prev..value)} \<union> prev..next..con" 
	        from PrevCurr, PrevCon, CurrCon, OldConDef, PrevIsNot; */

            prev = curr;
            curr = curr.next;

            /*: note FConLem: 
	        "f..con = (fieldRead (old con) f) \<setminus> {(k0, v0)}"
		from FConInv; */

            /*: note ConExceptPrev: "\<forall>n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> 
	        n \<noteq> prev \<longrightarrow> n..con = {(n..key, n..value)} \<union> n..next..con \<and> 
		(\<forall>v.(n..key, v) \<notin> n..next..con)"
		from PrevConDef, PrevNot, ConDefInv, PrevCurr, NextInjInv, CurrNotNull; */
        }

	Node tmp = curr.next;
	prev.next = tmp;
	curr.next = null;

	//: "curr..con" := "{(curr..key, curr..value)}";
	
	{
	    //: pickAny x::obj suchThat xHyp: "x \<in> Node \<and> x \<in> alloc \<and> x \<noteq> null";
	    {
		//: assuming xIsPrev: "x = prev";
		//: note nextNotCurr: "fieldRead (old next) curr \<noteq> curr" from NextInjInv, CurrNotNull, PrevCurr, CurrProps;			    
		//: note prevNextCon: "prev..next..con = fieldRead (old con) (prev..next)";
		//: note prevOldCon: "fieldRead (old con) prev = {(prev..key, prev..value)} \<union> fieldRead (old con) curr";
		//: note currOldCon: "fieldRead (old con) curr = {(curr..key, curr..value)} \<union> fieldRead (old con) (fieldRead (old next) curr)";
		//: note prevKeyNotK0: "prev..key \<noteq> k0";
		{
		    //: pickAny k::obj, v::obj suchThat ForwHyp: "(k, v) \<in> x..con";
		    //: note kNotK0: "k \<noteq> k0";
		    //: note currKeyIsK0: "curr..key = k0";
		    //: note ForwCase: "(k, v) \<in> {(x..key, x..value)} \<union> x..next..con" from xHyp, xIsPrev, ForwHyp, PrevCurr, nextNotCurr, PrevCon, prevNextCon, prevOldCon, currOldCon, prevKeyNotK0, kNotK0, currKeyIsK0 forSuch k, v;
		}
		/*: note BackCase: 
		    "\<forall>k v.(k, v) \<in> {(x..key, x..value)} \<union> x..next..con \<longrightarrow>
		     (k, v) \<in> x..con"; */
		//: note xCon: "x..con = {(x..key, x..value)} \<union> x..next..con" from ForwCase, BackCase;
	    }
	    /*: cases "x = curr", "x = prev", "x \<noteq> curr \<and> x \<noteq> prev" for 
	        XCon: "x..con = {(x..key, x..value)} \<union> x..next..con"; */
	    //: note ConPost: "x..con = {(x..key, x..value)} \<union> x..next..con \<and> (\<forall>v.(x..key, v) \<notin> x..next..con)" forSuch x;
	}
	
	{
	    /*: pickAny ht::obj suchThat 
	        CohHyp: "ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init"; */
	    {
		/*: pickAny i::int, k::obj, v::obj suchThat
		    InnerHyp: "0 \<le> i \<and> i < ht..table..length \<and> (k, v) \<in> ht..table.[i]..con"; */
		//: note NotCurr: "ht..table.[i] \<noteq> curr";
		/*: note InnerConc: "h k (ht..table..length) = i" 
		    from CohHyp, InnerHyp, Coherence, NotCurr, ConLoop forSuch i, k, v; */
	    }
	    /*: note CoherencePost: 
	        "(\<forall>i k v.0 \<le> i \<and> i < ht..table..length \<longrightarrow>
		 (k, v) \<in> ht..table.[i]..con \<longrightarrow> h k (ht..table..length) = i)"
		from InnerConc forSuch ht; */
	}

	{
	    /*: pickAny x::obj suchThat ContentsDefHyp: "x \<in> alloc \<and> x \<in> Hashtable \<and> x..init"; */
	    //: note OldXContents: "fieldRead (old Hashtable.contents) x = {(k, v). (k, v) \<in> fieldRead (old con) (arrayRead (old arrayState) (x..table) (h k (x..table..length)))}" from ContentsDefHyp, ContentsDefInv;
	    {
		//: assuming XNotThisHyp: "x \<noteq> this";
		//: note NotCurr: "\<forall>i. 0 \<le> i \<and> i < x..table..length \<longrightarrow> x..table.[i] \<noteq> curr";
		//: note ConXUnchanged: "\<forall>i.0 \<le> i \<and> i < x..table..length \<longrightarrow> x..table.[i]..con = fieldRead (old con) (arrayRead (old arrayState) (x..table) i)" from ContentsDefHyp, XNotThisHyp, NotCurr, ConUnchanged;
		//: note LengthLemma: "\<forall>k.0 \<le> (h k (x..table..length)) \<and> (h k (x..table..length)) < (x..table..length)" from ContentsDefHyp, HashInv;
		//: note XNotThisCase: "x..contents = {(k, v). (k, v) \<in> x..table.[(h k (x..table..length))]..con}" from XNotThisHyp, OldXContents, LengthLemma, ConXUnchanged;
	    }
	    { 
		//: assuming XIsThisHyp: "x = this";
		//: note OldContents: "old contents = {(k,v). (k,v) \<in> old (table.[(h k (table..length))]..con)}";
		{
		    //: pickAny k::obj, v::obj suchThat ForwHyp: "(k, v) \<in> contents";
		    //: note NotCurr: "table.[(h k (table..length))] \<noteq> curr" from FirstInjInv, ContentsDefHyp,XIsThisHyp, PrevCurr, CurrNotNull, HashInv;
		    //: note ForwCase: "(k, v) \<in> table.[(h k (table..length))]..con" from ForwHyp, OldContents, NotCurr, ConLoop forSuch k, v;
		}
		{
		    //: pickAny k::obj, v::obj suchThat BackHyp: "(k, v) \<in> table.[(h k (table..length))]..con";
		    //: note NotCurr: "table.[(h k (table..length))] \<noteq> curr" from FirstInjInv, ContentsDefHyp, XIsThisHyp, PrevCurr, CurrNotNull, HashInv;
		    //: note BackCase: "(k, v) \<in> contents" from BackHyp, OldContents, NotCurr, ConLoop, FConInv, HCProps forSuch k, v;
		}
		//: note XIsThisCase: "contents = {(k, v). (k, v) \<in> table.[(h k (table..length))]..con}" from ForwCase, BackCase;
	    }
	    //: note ContentsDefPost: "x..contents = {(k, v). (k, v) \<in> x..table.[(h k (x..table..length))]..con}" from XNotThisCase, XIsThisCase forSuch x;
	}
        return curr.value;

    }

    private Object _remove(Object k0)
    /*: requires "(comment ''Init'' init) \<and> k0 \<noteq> null \<and> 
	         (\<exists> v. (k0, v) \<in> contents) \<and> theinvs"
        modifies contents, con, next, arrayState
        ensures "(contents = old contents \<setminus> {(k0, result)}) \<and> 
	         ((k0, result) \<in> old contents) \<and> 
		 (\<forall> a i. a \<noteq> table \<longrightarrow> a.[i] = old (a.[i])) \<and> theinvs"
    */
    {
	//: ghost specvar v0::obj;
	//: havoc v0 suchThat KeyInContents: "(k0, v0) \<in> contents";

	int hc = compute_hash(k0);
	Node f = table[hc];

        //: note ThisProps: "this \<in> alloc \<and> this \<in> Hashtable";
        //: note HCDef: "hc = h k0 (table..length)";
	/*: note KeyInBucket: "(k0, v0) \<in> table.[hc]..con" 
            from HCDef, KeyInContents, ContentsDef, Init, ThisProps; */

	if (f.key == k0) {
	    
	    return removeFirst(k0, hc);

	} else {
	  
	    return removeFromBucket(k0, hc);
	}
    }

    private void _add(Object k0, Object v0)
    /*: requires "comment ''Init'' init \<and> 
                  k0 \<noteq> null \<and> v0 \<noteq> null \<and> 
                  \<not> (\<exists> v. (k0, v) \<in> contents) \<and> theinvs"
        modifies contents, arrayState, "new..con", "new..next", "new..value", 
	         "new..key"
        ensures  "contents = old contents \<union> {(k0, v0)} \<and>
	          (\<forall> a i. a \<noteq> table \<longrightarrow> 
		  a.[i] = old (a.[i])) \<and> theinvs" */
    {
	int hc = compute_hash(k0);
	Node n = new /*: hidden */ Node();
	n.key = k0;
	n.value = v0;
	Node first = table[hc];
	n.next = first;
	//: "n..con" := "{(k0, v0)} \<union> first..con";
	table[hc] = n;
	//: "contents" := "(old contents) \<union> {(k0, v0)}";

        //: note NewNotHT: "n \<notin> Hashtable";
        //: note ThisProps: "this \<in> alloc \<and> this \<in> old alloc \<and> this \<in> Hashtable";
        //: note HCBounds: "0 \<le> hc \<and> hc < table..length";
	//: note NewOldNEq: "n \<noteq> first";

        //: note ThisTableNotNull: "table \<noteq> null";

	/*: note OldNotRefInTable: 
	  "\<forall> ht i. ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init \<and> 0 \<le> i \<and> 
           i < ht..table..length \<and> first \<noteq> null \<longrightarrow> ht..table.[i] \<noteq> first"
	  from OldNotRefInTable, Init, ThisProps, HCBounds, ElementInjInvHash,
	    NewOldNEq, TableInjInvHash, NewNotHT, ThisTableNotNull; */

        //: note HashPost: "theinv HashInv" from HashPost, HashInv, NewNotHT;

	//: note KeyAlloc: "k0 \<in> alloc";
	//: note ValAlloc: "v0 \<in> alloc";
	//: note AllocChanged: "alloc = old alloc \<union> {n}";
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

	//: note AllocChange: "Object.alloc = old Object.alloc \<union> {n}";
	//: note HProp: "hc = h k0 (table..Array.length)";

	/*: note NewNotRefThisArr: 
	    "\<forall> i. 0 \<le> i \<and> i < table..length \<longrightarrow> 
	      (arrayRead (old arrayState) table i) \<noteq> n";*/
	/*: note NewNotRefArray:
	    "\<forall> a i. 0 \<le> i \<and> i < a..length \<longrightarrow> 
	      (arrayRead (old arrayState) a i) \<noteq> n"; */

	//: note NewNotAlloc: "n \<notin> old alloc";
	/*: note NewNotRefByNext: "\<forall> x. x..next \<noteq> n"
	  from NewOldNEq, NewNotAlloc, unalloc_lonely, NewNotRefByNext; */

	//: note NotInOldContents: "\<forall> v. (k0, v) \<notin> old contents";
	/*: note NotInOldConFirst: 
	    "\<forall> v. (k0, v) \<notin> (fieldRead (old con) first)"
	    from NotInOldConFirst, NotInOldContents, ContentsDef, ThisProps,
	      Init, HProp; */
	//: note FirstNotN: "first \<noteq> n";
	/*: note NewConDef: "theinv ConDef" 
	  from NewConDef, ConDef, NewNotRefByNext, FirstNotN, 
	    NotInOldConFirst; */

	/*: note ElemInj: "theinv ElementInjInv" 
	    from ElementInjInv, ThisProps, NewNotHT, NewNotRefArray, 
	    TableInjInv, ThisTableNotNull; */

	{
	    //: pickAny ht::obj;
	    {
		//: assuming h1: "ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init";
		{
		    //: pickAny i::int, k::obj, v::obj;
		    //: note g1: "arrayRead (old arrayState) (ht..table) i \<noteq> n";
		    //: note g2: "ht \<in> old alloc";
		    {
			//: assuming h2: "0 \<le> i \<and> i < ht..table..length \<and> (k,v) \<in> ht..table.[i]..con";
			{
			    //: assuming h3: "ht = this";
			    //: note c5: "h k (ht..table..length) = i" from c3, h1, h2, h3, Coherence, g1, g2, HProp;
			}
			{
			    //: assuming h4: "ht \<noteq> this";
			    //: note g3: "ht..table \<noteq> table";
			    //: note c4: "h k (ht..table..length) = i" from c4, h1, h2, h4, Coherence, g1, g2, g3;
			}
			//: note c3: "h k (ht..table..length) = i" from c4, c5;
		    }
		    //: note c2: "0 \<le> i \<and> i < ht..table..length \<longrightarrow> (k,v) \<in> ht..table.[i]..con \<longrightarrow> h k (ht..table..length) = i" forSuch i, k, v;
		}
		//: note c1: "\<forall> i k v. 0 \<le> i \<and> i < ht..table..length \<longrightarrow> (k,v) \<in> ht..table.[i]..con \<longrightarrow> h k (ht..table..length) = i";
	    }
	    //: note CohPost: "ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init \<longrightarrow> (\<forall> i k v. 0 \<le> i \<and> i < ht..table..length \<longrightarrow> (k,v) \<in> ht..table.[i]..con \<longrightarrow> h k (ht..table..length) = i)" forSuch ht;
	}

	{
	    //: pickAny ht::obj;
	    {
		//: assuming NewContentsHyp: "ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init";
		//: note ThisContents: "contents = {(k,v). (k,v) \<in> table.[(h k (table..length))]..con}" from ThisContents, HProp, NewNotRefThisArr, HashInv, ContentsDefInv,  ThisProps, Init;
		{
		    //: assuming OtherHyp: "ht \<noteq> this";
		    //: note OtherContents: "ht..contents = {(k,v). (k,v) \<in> ht..table.[(h k (ht..table..length))]..con}" from OtherHyp, NewContentsHyp, ContentsDefInvHash, NewNotHT, TableInjInvHash, NewNotRefArray, TableNotNullHash, HashInv;
		}

		//: cases "ht = this", "ht \<noteq> this" for NewContentsCases: "ht..contents = {(k,v). (k,v) \<in> ht..table.[(h k (ht..table..length))]..con}" from ThisContents, OtherContents;
		//: note NewContentsConc: "ht..contents = {(k,v). (k,v) \<in> ht..table.[(h k (ht..table..length))]..con}";
	    }
	    //: note NewContentsDef: "ht \<in> alloc \<and> ht \<in> Hashtable \<and> ht..init \<longrightarrow> ht..contents = {(k,v). (k,v) \<in> ht..table.[(h k (ht..table..length))]..con}" forSuch ht;
	}

	/*: note OldNotRefByNext: 
	  "\<forall> x. first \<noteq> null \<longrightarrow> old (x..next) \<noteq> first"
	  from FirstInjInv, Init, HCBounds, OldNotRefByNext, ThisProps; */

	/*: note NewFirstInj: "theinv FirstInjInv"
	  from FirstInjInv, NewNotRefByNext, OldNotRefByNext, TableInjInv,
	    OldNotRefInTable, HCBounds, NewFirstInj, ThisProps, ElementInjInv,
	    NewNotHT; */

	/*: note NewNextInj: "theinv NextInjInv"
	  from NextInjInv, OldNotRefByNext, NewNextInj; */
    }

    public void add(Object k0, Object v0)
    /*: requires "init \<and> k0 \<noteq> null \<and> v0 \<noteq> null \<and> 
                  ~(\<exists> v. (k0, v) \<in> contents)"
        modifies contents
        ensures "contents = old contents \<union> {(k0, v0)}"
    */
    {
        _add(k0, v0);
    }

    public Object replace(Object k0, Object v0)
    /*: requires "init \<and> k0 \<noteq> null \<and> v0 \<noteq> null \<and> (\<exists> v. (k0, v) \<in> contents)"
        modifies contents
	ensures "contents = old contents - {(k0, result)} \<union> {(k0, v0)} &
                 (k0, result) \<in> old contents"
    */
    {
	Object v1 = _remove(k0);
	_add(k0, v0);
	return v1;
    }

    public Object put(Object k0, Object v0)
    /*: requires "init \<and> k0 \<noteq> null \<and> v0 \<noteq> null"
        modifies contents
	ensures "contents = old contents - {(k0, result)} \<union> {(k0, v0)} \<and>
	         (result = null \<longrightarrow> \<not> (\<exists> v. (k0, v) \<in> old contents)) \<and>
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
    /*: requires "init \<and> k0 \<noteq> null"
        ensures "(result \<noteq> null \<longrightarrow> (k0, result) \<in> contents) \<and>
	         (result = null \<longrightarrow> \<not>(\<exists> v. (k0, v) \<in> contents))"
	         
    */
    {
	//: instantiate "theinv ContentsDefInv" with "this";
	//: mp ThisContentsDef: "this \<in> alloc \<and> this \<in> Hashtable \<and> init \<longrightarrow> contents = {(k, v). (k, v) \<in> table.[(h k (table..length))]..con}";
	int hc = compute_hash(k0);
	Node curr = table[hc];

        //: note HCDef: "hc = h k0 (table..length)";
        /*: note InCurr: "\<forall> v. (((k0, v) \<in> contents) = ((k0, v) \<in> curr..con))" 
	    from ThisContentsDef, HCDef; */

        while /*: inv "\<forall> v. ((k0, v) \<in> contents) = ((k0, v) \<in> curr..con)" */
            (curr != null) {
            if (curr.key == k0) {
                return curr.value;
            }

            curr = curr.next;
        }
        return null;
    }

    public boolean isEmpty()
    /*: requires "init"
        ensures "result = (contents = \<emptyset>)";
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
		/*: note ContentsNonEmpty: "contents \<noteq> \<emptyset>" 
		    from INonEmpty, ContentsDefInv, Coherence, IBounds, ILT, 
		    ThisProps; */
		return false;
	    }
	    i = i + 1;
	}
	//: note AllEmpty: "\<forall> j. 0 \<le> j \<and> j < table..length \<longrightarrow> table.[j]..con = \<emptyset>";
	/*: note ContentsEmpty: "contents = \<emptyset>" 
	    from AllEmpty, ContentsDefInv, HashInv, ThisProps; */
	return true;
    }

}
