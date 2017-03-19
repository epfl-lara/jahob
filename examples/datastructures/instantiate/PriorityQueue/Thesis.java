public /*: claimedby PriorityQueue */ class PQElement {
    public Object ob;
    public int pr;
}

public class PriorityQueue
{
    private PQElement[] queue;
    private int length;

    /*:
      public specvar init :: bool = "False";
      public specvar contents :: "(obj * int) set";
      public specvar capacity :: int;

      specvar elements :: "obj set";

      vardefs "init == (queue \<noteq> null)";
      vardefs "elements == {p. \<exists> i. 0 \<le> i \<and> i < length \<and> p = queue.[i]}";		   
      vardefs "contents == {(x, y). EX p. p : elements & p..ob = x & p..pr = y}";
      vardefs "capacity == queue..Array.length";
      
      invariant CapacityInv: "init \<longrightarrow> 0 < capacity \<and> capacity = queue..Array.length";
      invariant InitialLength: "\<not>init \<longrightarrow> length = 0";
      invariant CardInv: "init \<longrightarrow> length = card(contents)"
      invariant LengthLowerInv: "init \<longrightarrow> 0 \<le> length";
      invariant LengthUpperInv: "init \<longrightarrow> length \<le> queue..Array.length";
      invariant NonNullInv: "init \<longrightarrow> (\<forall> i. 0 \<le> i \<and> i < length \<longrightarrow> queue.[i] \<noteq> null)";
      invariant NullInv: 
       "init \<longrightarrow> (\<forall> i. length \<le> i \<and> i < queue..Array.length \<longrightarrow> queue.[i] = null)";
      invariant DistinctInv: "init \<longrightarrow> (\<forall> i j. 
        (0 \<le> i \<and> i < length \<and> 0 \<le> j \<and> j < length \<and> queue.[i] = queue.[j]) \<longrightarrow> i = j)"
      invariant OrderedInv: "init \<longrightarrow> (\<forall> i j.
       (0 \<le> i \<and> i < length \<and> 0 \<le> j \<and> j < length \<and> (j=i+i+1 \<or> j=i+i+2)
         \<longrightarrow> queue.[i]..pr \<ge> queue.[j]..pr))";
      invariant HiddenInv: "init \<longrightarrow> queue : hidden";
      invariant InjInv: "\<forall> x y. x..queue = y..queue \<and> x..queue \<noteq> null \<longrightarrow> x = y";

      invariant ContentsInj: 
      "ALL e1 e2. e1 : elements & e2 : elements & e1 ~= e2 --> (e1..ob ~= e2..ob | e1..pr ~= e2..pr)";

    */

    public void PriorityQueue(int initialCapacity)
    /*: requires "\<not>init \<and> 0 < initialCapacity"
        modifies init, contents, capacity
	ensures "init \<and> contents = \<emptyset> \<and> capacity = initialCapacity"
    */
    {
	queue = new /*: hidden */ PQElement[initialCapacity];
	{
	    //: pickAny x::obj;
	    {
		//: assuming CardHyp: "x \<in> alloc \<and> x \<in> PriorityQueue \<and> x..init";
		{
		    //: assuming XIsThisHyp: "x = this";
		    //: note LengthZero: "x..length = 0";
		    //: note ContentsEmpty: "x..contents = \<emptyset>";
		    //: note XIsThisCard: "x..length = card(x..contents)" from XIsThisHyp, LengthZero, ContentsEmpty;
		}
		{
		    //: assuming XNotThisHyp: "x \<noteq> this";
		    //: note XInOldAlloc: "x \<in> old alloc";
		    //: note XOldInit: "fieldRead (old PriorityQueue.init) x";
		    //: note OldCard: "fieldRead (old PriorityQueue.length) x = cardinality (fieldRead (old PriorityQueue.contents) x)" from CardHyp, XNotThisHyp, XInOldAlloc, XOldInit, CardInv;
		    //: note XLengthEq: "x..length = fieldRead (old PriorityQueue.length) x";
		    //: note XContentsUnchanged: "x..contents = fieldRead (old PriorityQueue.contents) x";
		    //: note XNotThisCard: "x..length = card(x..contents)" from XLengthEq, OldCard, XContentsUnchanged;
		}
		//: note CardConc: "x..length = card(x..contents)" from XIsThisCard, XNotThisCard;
	    }
	    //: note CardPostCond: "x \<in> alloc \<and> x \<in> PriorityQueue \<and> x..init \<longrightarrow> x..length = card(x..contents)" forSuch x;
	}
    }
    
    public void clear()
    /*: requires "init"
        modifies contents
        ensures "contents = \<emptyset>"
     */
    {
	int i = 0;
	while /*: inv "(\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> queue.[i] = null) \<and>
                       (\<forall> a i. a ~= queue \<longrightarrow> a.[i] = old (a.[i]))" */
	    (i < queue.length) {
	    queue[i] = null;
	}
	length = 0;
	{
	    //: pickAny x::obj;
	    {
		//: assuming CardHyp: "x \<in> alloc \<and> x \<in> PriorityQueue \<and> x..init";
		{
		    //: assuming XIsThisHyp: "x = this";
		    //: note LengthZero: "x..length = 0";
		    //: note ContentsEmpty: "x..contents = \<emptyset>";
		    //: note XIsThisCard: "x..length = card(x..contents)" from XIsThisHyp, LengthZero, ContentsEmpty;
		}
		{
		    //: assuming XNotThisHyp: "x \<noteq> this";
		    //: note XInOldAlloc: "x \<in> old alloc";
		    //: note XOldInit: "fieldRead (old PriorityQueue.init) x";
		    //: note OldCard: "fieldRead (old PriorityQueue.length) x = cardinality (fieldRead (old PriorityQueue.contents) x)" from CardHyp, XNotThisHyp, XInOldAlloc, XOldInit, CardInv;
		    //: note XLengthEq: "x..length = fieldRead (old PriorityQueue.length) x";
		    //: note XContentsUnchanged: "x..contents = fieldRead (old PriorityQueue.contents) x";
		    //: note XNotThisCard: "x..length = card(x..contents)" from XLengthEq, OldCard, XContentsUnchanged;
		}
		//: note CardConc: "x..length = card(x..contents)" from XIsThisCard, XNotThisCard;
	    }
	    //: note CardPostCond: "x \<in> alloc \<and> x \<in> PriorityQueue \<and> x..init \<longrightarrow> x..length = card(x..contents)" forSuch x;
	}
    }

    public int size()
    /*: requires "init"
        ensures "result = card(contents)"
    */
    {
	return length;
    }
    
    private static int parent(int i)
    /*: requires "i > 0"
        ensures "result >= 0 & result < i & 
	         (i = result + result + 1 | i = result + result +2) &
		 alloc = old alloc"
     */
    {
	return (i-1)/2;
    }

    private static int left(int i)
    /*: requires "0 \<le> i"
        ensures "0 \<le> result \<and> i < result \<and> result = 2 * i + 1 \<and> alloc = old alloc"
     */
    {
	return (2*i + 1);
    }

    private static int right(int i)
    /*: requires "0 \<le> i"
        ensures "0 \<le> result \<and> i < result \<and> result = 2 * i + 2 \<and> alloc = old alloc"
     */
    {
	return (2*i + 2);
    }

    private void resize()
    /*: requires "init \<and> theinvs"
        modifies queue, capacity, arrayState
        ensures "length < capacity \<and> theinvs \<and> 
	         (\<forall> a i. a \<noteq> queue \<longrightarrow> a.[i] = old (a.[i])) \<and>
		 (\<forall> x. x \<in> PriorityQueue \<longrightarrow> x..contents = old (x..contents)) \<and>
		 (\<forall> x. x \<in> PriorityQueue \<longrightarrow> x..init = old (x..init))"
    */
    {
	PQElement[] oldQueue = queue;
	queue = new /*: hidden */ PQElement[2 * oldQueue.length];
	int i = 0;
	while /*: inv "0 \<le> i \<and> 
		       comment ''ILeLength'' 
		       (i \<le> length) \<and>
		       comment ''Copied''
		       (\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> queue.[j] = arrayRead (old arrayState) oldQueue j) \<and>
		       comment ''NullLoopInv''
		       (\<forall> j. i \<le> j \<and> j < queue..Array.length \<longrightarrow> queue.[j] = null) \<and>
		       comment ''ArrayFrame''
		       (\<forall> a i. a \<noteq> queue \<longrightarrow> a.[i] = old (a.[i]))" */
	    (i < length) {
	    queue[i] = oldQueue[i];
	    i = i + 1;
	}
	{
	    //: pickAny x::obj;
	    //: note AllCopied: "(\<forall> j. 0 \<le> j \<and> j < length \<longrightarrow> queue.[j] = arrayRead (old arrayState) oldQueue j)";
	    //: note ThisContentsFrame: "contents = old contents" from contents_def, elements_def, AllCopied;
	    //: cases "x = this", "x \<noteq> this" for ContentsCases: "x \<in> PriorityQueue \<longrightarrow> x..contents = fieldRead (old PriorityQueue.contents) x";
	    //: note ContentsFrame: "x \<in> PriorityQueue \<longrightarrow> x..contents = fieldRead (old PriorityQueue.contents) x" forSuch x;
	}
	{
	    //: pickAny x::obj;
	    {
		//: assuming CardHyp: "x \<in> alloc \<and> x \<in> PriorityQueue \<and> x..init";
		//: note OldProps: "x \<in> old alloc \<and> fieldRead (old PriorityQueue.init) x";
		//: note OldCard: "x..length = card (fieldRead (old PriorityQueue.contents) x)" from OldProps, CardInv, CardHyp;
		//: note CardConc: "x..length = card (x..contents)" from ContentsFrame, CardHyp, OldCard;
	    }
	    //: note CardPostCond: "x \<in> alloc \<and> x \<in> PriorityQueue \<and> x..init \<longrightarrow> x..length = card(x..contents)" forSuch x;
	}
    }

    private boolean contains(Object o1, int p1)
    /*: requires "init \<and> o1 \<noteq> null \<and> theinvs"
        ensures "result = ((o1, p1) \<in> contents) \<and> theinvs"
     */
    {
	int i = 0;
	PQElement elem = null;
	  
	//: note LoopInvInit: "((o1, p1) \<in> contents) = (\<exists> j. i \<le> j \<and> j < length \<and> queue.[j]..ob = o1 \<and> queue.[j]..pr = p1)" from contents_def, elements_def;

	while /*: inv "0 \<le> i \<and> i \<le> length \<and>
		       ((o1, p1) \<in> contents) = 
		       (\<exists> j. i \<le> j \<and> j < length \<and> queue.[j]..ob = o1 \<and> queue.[j]..pr = p1)" */
	    (i < length) {
	    elem = queue[i];
	    if (elem.ob == o1 && elem.pr == p1) {
		return true;
	    }
	    i = i + 1;

	//: note LoopInvInduct: "((o1, p1) \<in> contents) = (\<exists> j. i \<le> j \<and> j < length \<and> queue.[j]..ob = o1 \<and> queue.[j]..pr = p1)" from contents_def, elements_def, FalseBranch, LoopInv;
	}
	//: note NotFound: "(o1, p1) \<notin> contents" from LoopInv, LoopCond, contents_def, elements_def;
	return false;
    }

    public void add(Object o1, int p1)
    /*: requires "init \<and> o1 \<noteq> null"
        modifies contents, capacity
	ensures "contents = old contents \<union> {(o1, p1)} \<and> capacity \<ge> old capacity"
    */
    {
	if (contains(o1,p1)) return;
	if (length == queue.length) resize();
	//: note ContentsUnchanged: "contents = old contents";
	//: note NotInOldContents: "(o1, p1) \<notin> old contents";
	//: note NotInNewContents: "(o1, p1) \<notin> contents" from ContentsUnchanged, NotInOldContents;
	addOnly(o1, p1);
	//: note PostCond: "contents = old contents \<union> {(o1, p1)}" from ContentsUnchanged, addOnly_Postcondition;
	//: note ContentsFrame: "\<forall>x. x \<in> old alloc \<and> x \<in> PriorityQueue \<and> x \<notin> hidden \<and> x \<noteq> this \<longrightarrow> x..contents = fieldRead (old PriorityQueue.contents) x" from contains_Postcondition, resize_Postcondition, addOnly_Postcondition;
    }
    
    private void addOnly(Object o1, int p1)
    /*: requires "init \<and> o1 \<noteq> null \<and> (o1, p1) \<notin> contents \<and> length < capacity \<and> theinvs"
        modifies contents, length, arrayState, ob, pr
	ensures "contents = old contents \<union> {(o1, p1)} \<and> length = old length + 1 \<and> theinvs \<and>
	         (\<forall>a i. a \<noteq> queue \<longrightarrow> a.[i] = old (a.[i])) \<and>
		 (\<forall>x. x \<in> old alloc \<and> x \<in> PriorityQueue \<and> x \<notin> hidden \<and> x \<noteq> this \<longrightarrow> x..contents = fieldRead (old PriorityQueue.contents) x)"
    */
    {
	int i = length;
	length = length + 1;
	
	PQElement e = new PQElement();
	e.ob = o1;
	e.pr = p1;

	while /*: inv "(comment ''IBounds'' (0 \<le> i \<and> i < length)) & 
		       e ~: elements &
		       alloc = old alloc Un {e} &
		       (comment ''RelToI''
		        (((i + i + 1 < length) -->
			  (queue.[(i + i + 1)]..PQElement.pr <
			   e..PQElement.pr)) &
			 ((i + i + 2 < length) -->
			  (queue.[(i + i + 2)]..PQElement.pr <
			   e..PQElement.pr)))) &
		       (comment ''ContentsPostLoop''
		       (old elements = { p. EX j. 0 <= j & j < length &
                                          j ~= i & p = queue.[j] })) &
		       (ALL j. 0 <= j & j < length & j ~= i --> 
		               queue.[j] ~= null) & 
		       (comment ''PDBefore''
		        (ALL j k. 0 <= j & j < length & 0 <= k & k < length &
		                 queue.[j] = queue.[k] & j ~= i & k ~= i --> 
				 j = k)) &
		       theinv NullInv &
		       (comment ''OrderedSkipLoop''
		       (i = (old length) -->
		        (ALL j k. 
			 (0 <= j & j < (old length) & 0 <= k & 
			  k < (old length) &
			  ((k = j + j + 1) | (k = j + j + 2)) -->
			   queue.[j]..PQElement.pr >=
			   queue.[k]..PQElement.pr)))) &
		       (comment ''OrderedPostLoop''
		       (i ~= (old length) -->
		        (ALL j k. 
		         (0 <= j & j < length & 0 <= k & k < length &
			  ((k = j + j + 1) | (k = j + j + 2)) -->
			   queue.[j]..PQElement.pr >=
			   queue.[k]..PQElement.pr)))) \<and>
                       (\<forall> a i. a ~= queue \<longrightarrow> a.[i] = old (a.[i])) \<and>
                       (comment ''OrderedFrame'' 
                       (\<forall> pq. pq : PriorityQueue \<and> pq : alloc \<and> pq..init \<and> 
                        pq \<noteq> this \<longrightarrow> (\<forall> i j. 0 \<le> i \<and> i < pq..length \<and> 0 \<le> j \<and> 
                        j < pq..length \<and> (j = i + i + 1 \<or> j = i + i + 2) \<longrightarrow> 
                        pq..queue.[i]..pr \<ge> pq..queue.[j]..pr)))"
	      */
	    (i > 0 && queue[parent(i)].pr < e.pr)
	{
	    int p = parent(i);

	    //: noteThat PBounds: "0 \<le> p \<and> p < old length";
	    //: noteThat PIRel: "i = p + p + 1 | i = p + p + 2";
	    //: note InLoop: "queue.[p]..pr < e..pr";

	    queue[i] = queue[p];

	    /*: note iEffect1: "ALL jj. (0 \<le> jj \<and> jj < length \<and> 
	        ((i = jj + jj + 1) | (i = jj + jj + 2)) \<longrightarrow> 
	        queue.[jj]..pr \<ge> queue.[i]..pr)"; */

	    /*: note iEffect2: "ALL kk. (0 \<le> kk \<and> kk < length \<and>
	        ((kk = i + i + 1) | (kk = i + i + 2)) \<longrightarrow>
	        queue.[i]..pr \<ge> queue.[kk]..pr)" 
	        from OrderedPostLoop, InLoop, PIRel, PBounds; */

	    /*: note OtherEffect: 
	      "ALL jj kk. (0 \<le> jj \<and> jj < length \<and> 0 \<le> kk \<and> kk < length \<and> 
	       jj \<noteq> i \<and> kk \<noteq> i \<and> ((kk = jj + jj + 1) | (kk = jj + jj + 2)) \<longrightarrow> 
	       queue.[jj]..pr \<ge> queue.[kk]..pr)"; */

	    i = p;

	    /*: noteThat sameAfter:
	      "ALL jj kk. (0 <= jj & jj < length & 0 <= kk & kk < length & 
	      ((kk = jj + jj + 1) | (kk = jj + jj + 2)) -->
	      queue.[jj]..PQElement.pr >=
	      queue.[kk]..PQElement.pr)" 
	      from iEffect1, iEffect2, OtherEffect; */

	    /*: noteThat ContentsAfter:
	      "old elements = 
	       { p. EX j. 0 <= j & j < length & j ~= i & p = queue.[j] }"
	      from ContentsPostLoop, IBounds, PBounds;
	    */
	    /*: noteThat PDAfter:
	      "(ALL j k. 0 <= j & j < length & 0 <= k & k < length &
	                 queue.[j] = queue.[k] & j ~= i & k ~= i --> j = k)"
	      from PDBefore, PBounds;
	    */
	}
	queue[i] = e;

	//: noteThat ContentsDef: "elements = {p. (EX i. 0 <= i & i < length & p = queue.[i])}";
	//: noteThat NewElements: "elements = old elements Un { e }" from ContentsPostLoop, ContentsDef, IBounds;

	//: note ContentsFrame: "\<forall>x. x \<in> old alloc \<and> x \<in> PriorityQueue \<and> x \<notin> hidden \<and> x \<noteq> this \<longrightarrow> x..contents = fieldRead (old PriorityQueue.contents) x";

	{
	    //: localize;
	    //: note ContentsForw: "ALL x y. (x, y) : contents --> (x, y) : old contents Un {(o1, p1)}" from contents_def, Hyp, NewElements;
	    {
		//: pickAny x::obj, y::int;
		{
		    //: assuming Hyp: "(x, y) : old contents Un {(o1, p1)}";
		    {
			//: assuming Hyp1: "(x, y) : old contents";
			//: note ENotInOld: "e ~: old elements";
			//: note Conc1: "(x, y) : contents" from contents_def, ContentsDef, NewElements, Hyp1, ENotInOld;
		    }
		    //: note NewElemInContents: "(o1, p1) : contents";
		    //: note Conc: "(x, y) : contents" from NewElemInContents, Conc1, Hyp;
		}
		//: note ContentsBack: "(x, y) : old contents Un {(o1, p1)} --> (x, y) : contents" forSuch x, y;
	    }
	    //: note ContentsPost: "contents = old contents Un {(o1, p1)}" from ContentsForw, ContentsBack;
	}

	{
	    //: pickAny pq::obj;
	    {
		//: assuming ContentsHyp: "pq : alloc & pq : PriorityQueue";
		{
		    //: pickAny e1::obj, e2::obj;
		    {
			//: assuming Hyp: "e1 : elements & e2 : elements & e1 ~= e2";
			{
			    //: assuming OldEs: "e1 : old elements & e2 : old elements";
			    //: note Conc1: "e1..ob ~= e2..ob | e1..pr ~= e2..pr";
			}
			{
			    //: assuming NewE1: "e1 ~: old elements";
			    //: note NewEntry: "(o1, p1) ~: old contents";
			    //: note Conc2: "e1..ob ~= e2..ob | e1..pr ~= e2..pr" from Hyp, NewE1, contents_def, NewElements, NewEntry;
			}
			{
			    //: assuming NewE2: "e2 ~: old elements";
			    //: note NewEntry: "(o1, p1) ~: old contents";
			    //: note Conc3: "e1..ob ~= e2..ob | e1..pr ~= e2..pr" from Hyp, NewE2, contents_def, NewElements, NewEntry;
			}
			//: note Conc: "e1..ob ~= e2..ob | e1..pr ~= e2..pr" from Conc1, Conc2, Conc3;
		    }
		    //: note ContentsThis: "e1 : elements & e2 : elements & e1 ~= e2 --> (e1..ob ~= e2..ob | e1..pr ~= e2..pr)" forSuch e1, e2;
		}
		{
		    //: assuming NotThisHyp: "pq ~= this";
		    {
			//: pickAny e1::obj, e2::obj;
			{
			    //: assuming Hyp1: "e1 : pq..elements & e2 : pq..elements & e1 ~= e2";
			    //: note PQInOldAlloc: "pq : old alloc";
			    //: note ObKeyFrame: "e1 ~= e & e2 ~= e";
			    //: instantiate OldContentsInst: "old (theinv ContentsInj)" with "pq";
			    //: note OldContentsInj: "e1 : fieldRead (old PriorityQueue.elements) pq & e2 : fieldRead (old PriorityQueue.elements) pq & e1 ~= e2 --> (e1..ob ~= e2..ob | e1..pr ~= e2..pr)" from OldContentsInst,  ContentsHyp, PQInOldAlloc, ObKeyFrame;
			    //: note ElementsFrame: "pq..elements = fieldRead (old PriorityQueue.elements) pq";
			    //: note Conc1: "(e1..ob ~= e2..ob | e1..pr ~= e2..pr)" from Hyp1, OldContentsInj, ElementsFrame, ObKeyFrame;
			}
			//: note NotThisConc: "e1 : pq..elements & e2 : pq..elements & e1 ~= e2 --> (e1..ob ~= e2..ob | e1..pr ~= e2..pr)" forSuch e1, e2;
		    }
		    //: note NotThisConc: "ALL e1 e2. e1 : pq..elements & e2 : pq..elements & e1 ~= e2 --> (e1..ob ~= e2..ob | e1..pr ~= e2..pr)";
		}
		//: note ContentsInjConc: "ALL e1 e2. e1 : pq..elements & e2 : pq..elements & e1 ~= e2 --> (e1..ob ~= e2..ob | e1..pr ~= e2..pr)" from ContentsThis, NotThisConc;
	    }
	    //: note ContentsInjPost: "pq : alloc & pq : PriorityQueue --> (ALL e1 e2. e1 : pq..elements & e2 : pq..elements & e1 ~= e2 --> (e1..ob ~= e2..ob | e1..pr ~= e2..pr))" forSuch pq;
	}
	{
	    //: pickAny x::obj;
	    {
		//: assuming CardHyp: "x \<in> alloc \<and> x \<in> PriorityQueue \<and> x..init";
		{
		    //: note ThisProps: "this \<in> old alloc \<and> this \<in> PriorityQueue \<and> old init";
		    //: note OldCard: "old length = card(old contents)" from ThisProps, CardInv;
		    //: note NewLength: "length = old length + 1";
		    //: note NewNotInOld: "(o1, p1) \<notin> old contents";
		    //: note XIsThisCard: "length = card(contents)" from OldCard, NewLength, NewNotInOld, ContentsPost;
		}
		{
		    //: assuming XNotThisHyp: "x \<noteq> this";
		    //: note XInOldAlloc: "x \<in> old alloc";
		    //: note XOldInit: "fieldRead (old PriorityQueue.init) x";
		    //: note OldCard: "fieldRead (old PriorityQueue.length) x = cardinality (fieldRead (old PriorityQueue.contents) x)" from CardHyp, XNotThisHyp, XInOldAlloc, XOldInit, CardInv;
		    //: note XLengthEq: "x..length = fieldRead (old PriorityQueue.length) x";
		    {
			//: localize;
			//: note XContentsForw: "\<forall>y z.(y,z)\<in>x..contents\<longrightarrow>(y,z)\<in>(fieldRead (old PriorityQueue.contents) x)";
			//: note XContentsBack: "\<forall>y z.(y,z)\<in>(fieldRead (old PriorityQueue.contents) x)\<longrightarrow>(y,z)\<in>x..contents";
			//: note XContentsUnchanged: "x..contents = fieldRead (old PriorityQueue.contents) x" from XContentsForw, XContentsBack;
		    }
		    //: note XNotThisCard: "x..length = card(x..contents)" from XLengthEq, OldCard, XContentsUnchanged;
		}
		//: note CardConc: "x..length = card(x..contents)" from XIsThisCard, XNotThisCard;
	    }
	    //: note CardPostCond: "x \<in> alloc \<and> x \<in> PriorityQueue \<and> x..init \<longrightarrow> x..length = card(x..contents)" forSuch x;
	}
    }

    private void inductProof()
    /*: requires "init \<and> 0 < length \<and> theinvs"
        ensures "(ALL k. 0 <= k & k < length --> queue.[0]..pr >= queue.[k]..pr) \<and> theinvs" 
    */
    {
	//: note InContents: "(queue.[0]..ob, queue.[0]..pr) \<in> contents" from contents_def, elements_def, Precondition;
	//: note IsOrdered: "\<forall> i j. 0 \<le> i \<and> i < length \<and> 0 \<le> j \<and> j < length \<and> (j = i + i + 1 \<or> j = i + i + 2) \<longrightarrow> queue.[i]..pr \<ge> queue.[j]..pr";
	{
	    {
		//: induct InGeneral: "\<forall> x. x \<le> kk \<and> 0 \<le> x \<and> x < length \<longrightarrow> queue.[0]..pr \<ge> queue.[x]..pr" over kk::int;
		
	        // we can omit the following note, which follows directly from the inductive hypothesis
	        // note BaseCase: "\<forall> x. x \<le> 0 \<and> 0 \<le> x \<and> x < length \<longrightarrow> queue.[0]..pr \<ge> queue.[x]..pr";
		{
		    //: assuming InductHyp: "\<forall> x. x \<le> kk \<and> 0 \<le> x \<and> x < length \<longrightarrow> queue.[0]..pr \<ge> queue.[x]..pr";
		    {
			//: pickAny x::int;
			{
			    //: assuming BoundsHyp: "x \<le> (kk + 1) \<and> 0 \<le> x \<and> x < length";

			    // we can omit the following note, which follows directly from the inductive hypothesis
			    // note LtCase: "x < kk + 1 \<longrightarrow> queue.[0]..pr \<ge> queue.[x]..pr";
			    {
				//: assuming EqHyp: "x = kk + 1";
				{
				    //: assuming EvenHyp: "x mod 2 = 0";
				    //: note EvenParent: "\<exists> y. y + y = x" from EvenHyp;
				    {
					//: pickWitness evenp::int suchThat ParentRel: "evenp + evenp = x";
					//: note ParentGe: "queue.[evenp - 1]..pr \<ge> queue.[x]..pr";
					//: note ParentInduct: "queue.[0]..pr \<ge> queue.[evenp - 1]..pr";
					//: note EvenConc: "queue.[0]..pr \<ge> queue.[x]..pr";
				    }
				    //: note EvenCase: "queue.[0]..pr \<ge> queue.[x]..pr";
				}
				{
				    //: assuming OddHyp: "x mod 2 = 1";
				    //: note OddParent: "\<exists> y. y + y + 1 = x" from OddHyp;
				    {
					//: pickWitness oddp::int suchThat ParentRel: "oddp + oddp + 1 = x";
					//: note ParentGe: "queue.[oddp]..pr \<ge> queue.[x]..pr";
					//: note ParentInduct: "queue.[0]..pr \<ge> queue.[oddp]..pr";
					//: note OddConc: "queue.[0]..pr \<ge> queue.[x]..pr";
				    }
				    //: note OddCase: "queue.[0]..pr \<ge> queue.[x]..pr";
				}
				//: note EqConc: "queue.[0]..pr \<ge> queue.[x]..pr" from OddCase, EvenCase;
			    }
			    //: note OrderingConc: "queue.[0]..pr \<ge> queue.[x]..pr";
			}
			//: note InductConc: "x \<le> (kk + 1) \<and> 0 \<le> x \<and> x < length \<longrightarrow> queue.[0]..pr \<ge> queue.[x]..pr" forSuch x;
		    }
		    //: note InductCase: "\<forall> x. x \<le> (kk + 1) \<and> 0 \<le> x \<and> x < length \<longrightarrow> queue.[0]..pr \<ge> queue.[x]..pr";
		}
	    }
	    //: note MaxInQueue: "\<forall> k. 0 \<le> k \<and> k < length \<longrightarrow> queue.[0]..pr \<ge> queue.[k]..pr" from InGeneral;
	}
    }

    public Object peek()
    /*: requires "init"
        ensures "(contents=\<emptyset>\<longrightarrow>result=null)\<and>
	         (contents\<noteq>\<emptyset>\<longrightarrow>
		   (\<exists>p.(result,p)\<in>contents\<and>
	             (\<forall>x y.(x,y)\<in>contents\<longrightarrow>p\<ge>y)))" */
    {
	if (length == 0) return null;

	inductProof();

	/*: note Found: "(queue.[0]..ob, queue.[0]..pr) \<in> contents"
	  from ProcedurePrecondition, LengthLowerInv, FalseBranch, thisType, elements_def, contents_def; */
	
	//: witness "queue.[0]..pr" for PostCond: "\<exists>p.(queue.[0]..ob,p)\<in>contents\<and> (\<forall>x y.(x,y)\<in>contents\<longrightarrow>p\<ge>y)";

	return queue[0].ob;
    }

    public Object poll()
    /*: requires "init"
        modifies contents
        ensures  "(old contents = {} --> result = null) \<and>
	          (old contents ~= {} -->
		    (EX pr. (result, pr) \<in> old contents \<and>
                      contents = old contents - { (result, pr) } \<and>
		      (\<forall> x y. (x, y) \<in> (old contents) \<longrightarrow> pr \<ge> y)))" */
    {
	if (length == 0) return null;

	PQElement elem = queue[0];

	inductProof();

	length = length - 1;
	queue[0] = queue[length];
	queue[length] = null;
	//: note IntQueueContents: "elements = old elements - { elem }" from elements_def, ProcedurePrecondition, thisType;

	//: note Found: "(elem..ob, elem..pr) \<in> old contents" from ProcedurePrecondition, LengthLowerInv, FalseBranch, thisType, elements_def, contents_def;

	{
	    //: localize;
	    //: note Init: "init";
	    //: note ElemInOld: "elem \<in> old elements" from Init, LengthLowerInv, FalseBranch, thisType, elements_def;
	    //: note RemovedForw: "\<forall> y z. (y, z) \<in> contents \<longrightarrow> (y, z) \<in> old contents - {(elem..ob, elem..pr)}" from ContentsInj, Init, thisType, contents_def, IntQueueContents, ElemInOld;
	    //: note RemovedBack: "\<forall> y z. (y, z) \<in> old contents - {(elem..ob, elem..pr)} \<longrightarrow> (y, z) \<in> contents" from contents_def, IntQueueContents; 
	    //: note RemovedPair: "contents = old contents - {(elem..ob, elem..pr)}" from RemovedForw, RemovedBack;
	}
	{
	    //: pickAny x::obj;
	    {
		//: assuming CardHyp: "x \<in> alloc \<and> x \<in> PriorityQueue \<and> x..init";
		{
		    //: note ThisProps: "this \<in> old alloc \<and> this \<in> PriorityQueue \<and> old init";
		    //: note OldCard: "old length = card(old contents)" from ThisProps, CardInv;
		    //: note NewLength: "length = old length - 1";
		    //: note XIsThisCard: "length = card (contents)" from OldCard, NewLength, Found, RemovedPair;
		}
		{
		    //: assuming XNotThisHyp: "x \<noteq> this";
		    //: note XInOldAlloc: "x \<in> old alloc";
		    //: note XOldInit: "fieldRead (old PriorityQueue.init) x";
		    //: note OldCard: "fieldRead (old PriorityQueue.length) x = cardinality (fieldRead (old PriorityQueue.contents) x)" from CardHyp, XNotThisHyp, XInOldAlloc, XOldInit, CardInv;
		    //: note XLengthEq: "x..length = fieldRead (old PriorityQueue.length) x";
		    {
			//: localize;
			//: note XContentsForw: "\<forall>y z.(y,z)\<in>x..contents\<longrightarrow>(y,z)\<in>(fieldRead (old PriorityQueue.contents) x)";
			//: note XContentsBack: "\<forall>y z.(y,z)\<in>(fieldRead (old PriorityQueue.contents) x)\<longrightarrow>(y,z)\<in>x..contents";
			//: note XContentsUnchanged: "x..contents = fieldRead (old PriorityQueue.contents) x" from XContentsForw, XContentsBack;
		    }
		    //: note XNotThisCard: "x..length = card(x..contents)" from XLengthEq, OldCard, XContentsUnchanged;
		}
		//: note CardConc: "x..length = card(x..contents)" from XIsThisCard, XNotThisCard;
	    }
	    //: note CardPostCond: "x \<in> alloc \<and> x \<in> PriorityQueue \<and> x..init \<longrightarrow> x..length = card(x..contents)" forSuch x;
	}
	if (0 < length) heapify(0);

	{
	    //: localize;
	    //: note Init: "init";
	    //: note ElemInOld: "elem \<in> old elements" from Init, LengthLowerInv, FalseBranch, thisType, elements_def;
	    //: note FinalElements: "elements = old elements - {elem}" from IntQueueContents, heapify_Postcondition;
	    //: note RemovedForw: "\<forall> x1 y1. (x1, y1) : contents --> (x1, y1) : old contents - {(elem..ob, elem..pr)}" from ContentsInj, Init, thisType, contents_def, FinalElements, ElemInOld;
	    //: note RemovedBack: "\<forall> x2 y2. (x2, y2) \<in> old contents - {(elem..ob, elem..pr)} \<longrightarrow> (x2, y2) \<in> contents" from contents_def, FinalElements;
	    //: note RemovedPair: "contents = old contents - {(elem..ob, elem..pr)}" from RemovedForw, RemovedBack;
	}
	    
	//: note IsMax: "ALL x y. (x, y) : old contents --> elem..pr >= y";
	/*: witness "elem..pr" for
	  PostCond: "EX pr. (elem..ob, pr) \<in> old contents \<and> contents = old contents - {(elem..ob, pr)} & (ALL x y. (x, y) : (old contents) --> pr >= y)"
	  from RemovedPair, IsMax; */

	{
	    //: pickAny pq::obj;
	    {
		//: assuming Hyp: "pq : old alloc & pq : PriorityQueue & pq \<notin> hidden \<and> pq ~= this";
		//: note ConcForw: "ALL x y. (x, y) : pq..contents --> (x, y) : (fieldRead (old PriorityQueue.contents) pq)";
		//: note ConcBack: "ALL x y. (x, y) : (fieldRead (old PriorityQueue.contents) pq) --> (x, y) : pq..contents";
		//: note ContentsFrameConc: "pq..contents = (fieldRead (old PriorityQueue.contents) pq)" from ConcForw, ConcBack;
	    }
	    //: note ContentsFrame: "pq : old alloc & pq : PriorityQueue & pq \<notin> hidden \<and> pq ~= this --> pq..contents = (fieldRead (old PriorityQueue.contents) pq)" forSuch pq;
	}
	return elem.ob;
    }

    private void heapify(int i)
    /*: requires "init \<and> 0 \<le> i \<and> i < length \<and> 
                  theinv CapacityInv \<and>
		  theinv InitialLength \<and>
		  theinv CardInv \<and>
                  theinv LengthLowerInv \<and>
                  theinv LengthUpperInv \<and> 
		  theinv NonNullInv \<and>
		  theinv NullInv \<and> 
		  theinv DistinctInv \<and>
		  (comment ''GlobalOrderingPre''
		   (ALL k j.
		    (0 <= k & k < length & k ~= i & 0 < j & j < length &
		    ((j = k + k + 1) | (j = k + k + 2)) -->
		    queue.[k]..PQElement.pr >=
		    queue.[j]..PQElement.pr))) \<and> 
		  (comment ''LocalOrderingPre''
		   (ALL x. 
		    ((0 <= x & (i = x + x + 1 | i = x + x + 2)) -->
		     (((i + i + 1 < length) --> 
		      queue.[x]..PQElement.pr >=
		      queue.[(i + i + 1)]..PQElement.pr) &
		      ((i + i + 2 < length) -->
		      queue.[x]..PQElement.pr >=
		      queue.[(i + i + 2)]..PQElement.pr))))) \<and> 
                  (comment ''OrderedFrame'' 
                   (\<forall> pq. pq : PriorityQueue \<and> pq : alloc \<and> pq..init \<and> pq \<noteq> this \<longrightarrow> 
	            (\<forall> i j. 0 \<le> i \<and> i < pq..length \<and> 0 \<le> j \<and> j < pq..length \<and> 
	             (j = i + i + 1 \<or> j = i + i + 2) \<longrightarrow> 
	             pq..queue.[i]..pr \<ge> pq..queue.[j]..pr))) \<and>
	         theinv HiddenInv \<and> 
		 theinv InjInv \<and>
		 theinv ContentsInj"
        modifies "Array.arrayState"
        ensures "(\<forall> pq. pq..elements = old (pq..elements)) \<and> 
	         alloc = old alloc \<and> theinvs \<and>
	         (\<forall> a i. a \<noteq> queue \<longrightarrow> a.[i] = old (a.[i]))" */
    {
	int m = i;

	int l = left(i);
	if (l < length && queue[l].pr > queue[i].pr)
	    m = l;

	int r = right(i);
	if (r < length && queue[r].pr > queue[m].pr)
	    m = r;

	if (m != i)
	{
	    //: noteThat LeftDef: "l = i + i + 1";
	    //: noteThat RightDef: "r = i + i + 2";
	    /*: noteThat mLeft: 
	      "m = l --> ((queue.[l]..PQElement.pr > 
	                   queue.[i]..PQElement.pr) &
			 (r < length -->
			  (queue.[l]..PQElement.pr >=
			   queue.[r]..PQElement.pr)))";
	     */
	    /*: noteThat mRight:
	      "m = r --> ((queue.[r]..PQElement.pr >
	                   queue.[i]..PQElement.pr) &
			 (l < length -->
			  (queue.[r]..PQElement.pr >=
			   queue.[l]..PQElement.pr)))";
	     */

	    PQElement p = queue[m];
	    queue[m] = queue[i];
	    queue[i] = p;

	    //: noteThat iLB: "0 \<le> i";
	    //: noteThat iUB: "i < length";
	    //: noteThat mBounds: "0 \<le> m \<and> m < length";
	    /*: noteThat LocalOrder:
	      "(i + i + 1 < length \<longrightarrow> (queue.[i]..pr \<ge> queue.[(i + i + 1)]..pr)) \<and> 
	       (i + i + 2 < length \<longrightarrow> (queue.[i]..pr \<ge> queue.[(i + i + 2)]..pr))"
	       from LeftDef, RightDef, mRight, mLeft, iLB; */
	    /*: noteThat OrderingLem:
	      "(\<forall> k j.
		(0 \<le> k \<and> k < length \<and> k \<noteq> m \<and> 0 < j \<and> j < length \<and>
		((j = k + k + 1) \<or> (j = k + k + 2)) \<longrightarrow> 
		  queue.[k]..pr \<ge> queue.[j]..pr))"
	      from LeftDef, RightDef, GlobalOrderingPre, LocalOrder, iLB, iUB, 
	      mBounds, LocalOrderingPre;
	    */
	    //: note ContentsBefore: "\<forall> pq. pq..elements = old (pq..elements)";
	    {
		//: localize;
		//: note ContentsFrame: "\<forall> x. x..contents = fieldRead (old PriorityQueue.contents) x";
		//: note AllocUnchanged: "alloc = old alloc";
		//: note CardLemma: "theinv CardInv" from CardInv, ContentsFrame, AllocUnchanged;
	    }
	    heapify(m);
	    /*: note ContentsAfter: "\<forall> pq. pq..elements = old (pq..elements)"
	      from ContentsBefore, heapify_Postcond; */
	    /*: note ElementsFrame: 
		"\<forall> pq. pq \<in> PriorityQueue \<longrightarrow> pq..elements = old (pq..elements)"
	      from ContentsAfter; */
	} else {
	    //: localize;
	    //: note AllocUnchanged: "alloc = old alloc";
	    //: note CardPostCond: "theinv CardInv" from CardInv, AllocUnchanged;
	}
    }
}
