class PriorityQueueElement
{
    public Object ob;
    public final int key;
}

public class PriorityQueue
{
    private PriorityQueueElement[] queue;
    private int length;

    /*:
      public specvar init :: bool = "False";
      public specvar spqueue :: "obj set";
      public specvar smaxlen :: int;
      public specvar slength :: int;

      vardefs "init == (queue \<noteq> null)";
      vardefs "spqueue == {p. \<exists> i. 0 \<le> i \<and> i < length \<and> p = queue.[i]}";		   
      vardefs "smaxlen == queue..Array.length";
      vardefs "slength == length";
      
      invariant LengthLowerInv: "init \<longrightarrow> 0 \<le> length";
      invariant LengthUpperInv: "init \<longrightarrow> length \<le> queue..Array.length";
      invariant NonNullInv: "init \<longrightarrow> (\<forall> i. 0 \<le> i \<and> i < length \<longrightarrow> queue.[i] \<noteq> null)";
      invariant NullInv: 
       "init \<longrightarrow> (\<forall> i. length \<le> i \<and> i < queue..Array.length \<longrightarrow> queue.[i] = null)";
      invariant DistinctInv: "init \<longrightarrow> (\<forall> i j. 
        (0 \<le> i \<and> i < length \<and> 0 \<le> j \<and> j < length \<and> queue.[i] = queue.[j]) \<longrightarrow> i = j)"
      invariant OrderedInv: "init \<longrightarrow> (\<forall> i j.
       (0 \<le> i \<and> i < length \<and> 0 \<le> j \<and> j < length \<and> (j=i+i+1 \<or> j=i+i+2)
         \<longrightarrow> queue.[i]..key \<ge> queue.[j]..key))";
      invariant HiddenInv: "init \<longrightarrow> queue : hidden";
      invariant InjInv: "\<forall> x y. x..queue = y..queue \<and> x..queue \<noteq> null \<longrightarrow> x = y";
    */

    public void PriorityQueue(int len)
    /*: requires "\<not>init \<and> 0 \<le> len"
        modifies init, spqueue, smaxlen, slength
	ensures "init \<and> spqueue = {} \<and> smaxlen = len \<and> slength = 0"
    */
    {
	queue = new /*: hidden */ PriorityQueueElement[len];
	
	int i = 0;

	while /*: inv "(\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> queue.[i] = null) \<and>
                       (\<forall> a i. a ~= queue \<longrightarrow> a.[i] = old (a.[i]))" */
	    (i < queue.length) {
	    queue[i] = null;
	}
	length = 0;
    }

    public int currLength()
    /*: requires "init"
        ensures "result = slength"
    */
    {
	return length;
    }
    
    public int maxLength()
    /*: requires "init"
        ensures "result = smaxlen"
    */
    {
	return queue.length;
    }
    
    public boolean isEmpty()
    /*: requires "init"
        ensures "result = (slength = 0)"
    */
    {
	return (length == 0);
    }

    public boolean isFull()
    /*: requires "init"
        ensures "result = (slength = smaxlen)"
    */
    {
	return (length == queue.length);
    }
   
    private static int parent(int i)
    /*: requires "i > 0"
        ensures "result >= 0 & result < i & 
	         (i = result + result + 1 | i = result + result +2)"
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

    public void insert(PriorityQueueElement e)
    /*: requires "init & e ~= null & slength < smaxlen & e ~: spqueue"
        modifies spqueue, slength
	ensures "spqueue = old spqueue Un {e} & 
                 (slength = (old slength) + 1)"
    */
    {
	int i = length;
	length = length + 1;

	while /*: inv "(comment ''IBounds'' (0 \<le> i \<and> i < length)) & 
		       e ~: spqueue &
		       (comment ''RelToI''
		        (((i + i + 1 < length) -->
			  (queue.[(i + i + 1)]..PriorityQueueElement.key <
			   e..PriorityQueueElement.key)) &
			 ((i + i + 2 < length) -->
			  (queue.[(i + i + 2)]..PriorityQueueElement.key <
			   e..PriorityQueueElement.key)))) &
		       (comment ''ContentPostLoop''
		       (old spqueue = { p. EX j. 0 <= j & j < length &
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
			   queue.[j]..PriorityQueueElement.key >=
			   queue.[k]..PriorityQueueElement.key)))) &
		       (comment ''OrderedPostLoop''
		       (i ~= (old length) -->
		        (ALL j k. 
		         (0 <= j & j < length & 0 <= k & k < length &
			  ((k = j + j + 1) | (k = j + j + 2)) -->
			   queue.[j]..PriorityQueueElement.key >=
			   queue.[k]..PriorityQueueElement.key)))) \<and>
                       (\<forall> a i. a ~= queue \<longrightarrow> a.[i] = old (a.[i])) \<and>
                       (comment ''OrderedFrame'' 
                       (\<forall> pq. pq : PriorityQueue \<and> pq : alloc \<and> pq..init \<and> 
                        pq \<noteq> this \<longrightarrow> (\<forall> i j. 0 \<le> i \<and> i < pq..length \<and> 0 \<le> j \<and> 
                        j < pq..length \<and> (j = i + i + 1 \<or> j = i + i + 2) \<longrightarrow> 
                        pq..queue.[i]..key \<ge> pq..queue.[j]..key)))"
	      */
	    (i > 0 && queue[parent(i)].key < e.key)
	{
	    int p = parent(i);

	    //: noteThat PBounds: "0 \<le> p \<and> p < old length";
	    //: noteThat PIRel: "i = p + p + 1 | i = p + p + 2";
	    //: note InLoop: "queue.[p]..key < e..key";

	    queue[i] = queue[p];

	    /*: note iEffect1: "ALL jj. (0 \<le> jj \<and> jj < length \<and> 
	        ((i = jj + jj + 1) | (i = jj + jj + 2)) \<longrightarrow> 
	        queue.[jj]..key \<ge> queue.[i]..key)"; */
	    /*: note iEffect2: "ALL kk. (0 \<le> kk \<and> kk < length \<and>
                ((kk = i + i + 1) | (kk = i + i + 2)) \<longrightarrow>
	        queue.[i]..key \<ge> queue.[kk]..key)" 
	        from iEffect2, OrderedPostLoop, InLoop, PIRel, PBounds; */
	    /*: note OtherEffect: 
	      "ALL jj kk. (0 \<le> jj \<and> jj < length \<and> 0 \<le> kk \<and> kk < length \<and> 
	       jj \<noteq> i \<and> kk \<noteq> i \<and> ((kk = jj + jj + 1) | (kk = jj + jj + 2)) \<longrightarrow> 
	       queue.[jj]..key \<ge> queue.[kk]..key)"; */

	    i = p;

	    /*: noteThat sameAfter:
	      "ALL jj kk. (0 <= jj & jj < length & 0 <= kk & kk < length & 
	      ((kk = jj + jj + 1) | (kk = jj + jj + 2)) -->
	      queue.[jj]..PriorityQueueElement.key >=
	      queue.[kk]..PriorityQueueElement.key)" 
	      from sameAfter, iEffect1, iEffect2, OtherEffect; */

	    /*: noteThat ContentAfter:
	      "old spqueue = 
	       { p. EX j. 0 <= j & j < length & j ~= i & p = queue.[j] }"
	      from ContentPostLoop, IBounds, PBounds, ContentAfter;
	    */
	    /*: noteThat PDAfter:
	      "(ALL j k. 0 <= j & j < length & 0 <= k & k < length &
	                 queue.[j] = queue.[k] & j ~= i & k ~= i --> j = k)"
	      from PDBefore, PBounds, PDAfter;
	    */
	}
	queue[i] = e;
	/*: noteThat ContentDef:
	  "spqueue = {p. (EX i. 0 <= i & i < length & p = queue.[i])}";
	*/
	/*: noteThat ContentFinal: "spqueue = old spqueue Un { e }"
	  from ContentPostLoop, ContentDef, IBounds, ContentFinal;
	*/
    }

    public PriorityQueueElement findMax()
    /*: requires "init \<and> slength > 0"
        ensures "result \<noteq> null \<and> result \<in> spqueue \<and>
	         (\<forall> x. x \<in> spqueue \<longrightarrow> result..key \<ge> x..key)" */
    {
	//: noteThat ArrLength: "0 < length";
	/*: noteThat Ordering:
	  "(\<forall> i j.
	    ((0 \<le> i \<and> i < length \<and> 0 \<le> j \<and> j < length \<and> 
             ((j = i + i + 1) | (j = i + i + 2)) \<longrightarrow> 
	     queue.[i]..key \<ge> queue.[j]..key))) \<longrightarrow>
	   (\<forall> k. ((0 \<le> k \<and> k < length) \<longrightarrow> queue.[0]..key \<ge> queue.[k]..key))" 
          from ArrLength, Ordering; */
	return queue[0];
    }

    public PriorityQueueElement extractMax()
    /*: requires "init \<and> slength > 0"
        modifies spqueue, slength
        ensures  "slength = old slength - 1 \<and> result \<noteq> null \<and>
	          spqueue = old spqueue - { result } \<and>
		  (\<forall> x. (x \<in> (old spqueue) \<longrightarrow> result..key \<ge> x..key))" */
    {
	PriorityQueueElement result = queue[0];
	//: noteThat ArrLength: "0 < length";
	/*: noteThat Ordering:
	  "(\<forall> i j.
	    ((0 \<le> i \<and> i < length \<and> 0 \<le> j \<and> j < length \<and>
	     ((j = i + i + 1) | (j = i + i + 2)) \<longrightarrow> 
	     queue.[i]..key \<ge> queue.[j]..key))) \<longrightarrow>
	   (ALL k. ((0 \<le> k \<and> k < length) \<longrightarrow> queue.[0]..key \<ge> queue.[k]..key))"
          from ArrLength, Ordering; */
	length = length - 1;
	queue[0] = queue[length];
	queue[length] = null;
	//: noteThat IntQueueContent: "spqueue = old spqueue - { result }";
	if (0 < length) heapify(0);
	/*: noteThat FinalQueueContent: "spqueue = old spqueue - { result }"
	  from IntQueueContent, heapify_Postcond, FinalQueueContent; */
	return result;
    }

    private void heapify(int i)
    /*: requires "init \<and> 0 \<le> i \<and> i < length \<and> theinv LengthLowerInv \<and>
                  theinv LengthUpperInv \<and> theinv NonNullInv \<and>
		  theinv NullInv \<and> theinv DistinctInv \<and>
		  (comment ''GlobalOrderingPre''
		   (ALL k j.
		    (0 <= k & k < length & k ~= i & 0 < j & j < length &
		    ((j = k + k + 1) | (j = k + k + 2)) -->
		    queue.[k]..PriorityQueueElement.key >=
		    queue.[j]..PriorityQueueElement.key))) \<and> 
		  (comment ''LocalOrderingPre''
		   (ALL x. 
		    ((0 <= x & (i = x + x + 1 | i = x + x + 2)) -->
		     (((i + i + 1 < length) --> 
		      queue.[x]..PriorityQueueElement.key >=
		      queue.[(i + i + 1)]..PriorityQueueElement.key) &
		      ((i + i + 2 < length) -->
		      queue.[x]..PriorityQueueElement.key >=
		      queue.[(i + i + 2)]..PriorityQueueElement.key))))) \<and> 
                  (comment ''OrderedFrame'' 
                   (\<forall> pq. pq : PriorityQueue \<and> pq : alloc \<and> pq..init \<and> pq \<noteq> this \<longrightarrow> 
	            (\<forall> i j. 0 \<le> i \<and> i < pq..length \<and> 0 \<le> j \<and> j < pq..length \<and> 
	             (j = i + i + 1 \<or> j = i + i + 2) \<longrightarrow> 
	             pq..queue.[i]..key \<ge> pq..queue.[j]..key))) \<and>
	         theinv HiddenInv \<and> theinv InjInv"
        modifies "Array.arrayState"
        ensures "(\<forall> pq. pq..init = old (pq..init)) \<and> 
	         (\<forall> pq. pq..spqueue = old (pq..spqueue)) \<and> 
	         (\<forall> pq. pq..smaxlen = old (pq..smaxlen)) \<and> 
	         (\<forall> pq. pq..slength = old (pq..slength)) \<and> 
	         alloc = old alloc \<and> theinvs \<and>
	         (\<forall> a i. a \<noteq> queue \<longrightarrow> a.[i] = old (a.[i]))" */
    {
	int m = i;

	int l = left(i);
	if (l < length && queue[l].key > queue[i].key)
	    m = l;

	int r = right(i);
	if (r < length && queue[r].key > queue[m].key)
	    m = r;

	if (m != i)
	{
	    //: noteThat LeftDef: "l = i + i + 1";
	    //: noteThat RightDef: "r = i + i + 2";
	    /*: noteThat mLeft: 
	      "m = l --> ((queue.[l]..PriorityQueueElement.key > 
	                   queue.[i]..PriorityQueueElement.key) &
			 (r < length -->
			  (queue.[l]..PriorityQueueElement.key >=
			   queue.[r]..PriorityQueueElement.key)))";
	     */
	    /*: noteThat mRight:
	      "m = r --> ((queue.[r]..PriorityQueueElement.key >
	                   queue.[i]..PriorityQueueElement.key) &
			 (l < length -->
			  (queue.[r]..PriorityQueueElement.key >=
			   queue.[l]..PriorityQueueElement.key)))";
	     */

	    PriorityQueueElement p = queue[m];
	    queue[m] = queue[i];
	    queue[i] = p;

	    //: noteThat iLB: "0 \<le> i";
	    //: noteThat iUB: "i < length";
	    //: noteThat mBounds: "0 \<le> m \<and> m < length";
	    /*: noteThat LocalOrder:
	      "(i + i + 1 < length \<longrightarrow> (queue.[i]..key \<ge> queue.[(i + i + 1)]..key)) \<and> 
	       (i + i + 2 < length \<longrightarrow> (queue.[i]..key \<ge> queue.[(i + i + 2)]..key))"
		from LeftDef, RightDef, mRight, mLeft, iLB, LocalOrder; */
	    /*: noteThat OrderingLem:
	      "(\<forall> k j.
		(0 \<le> k \<and> k < length \<and> k \<noteq> m \<and> 0 < j \<and> j < length \<and>
		((j = k + k + 1) \<or> (j = k + k + 2)) \<longrightarrow> 
		  queue.[k]..key \<ge> queue.[j]..key))"
	      from LeftDef, RightDef, GlobalOrderingPre, LocalOrder, iLB, iUB, 
	      mBounds, LocalOrderingPre, OrderingLem;
	    */
	    //: note ContentBefore: "\<forall> pq. pq..spqueue = old (pq..spqueue)";
	    heapify(m);
	    /*: note ContentAfter: "\<forall> pq. pq..spqueue = old (pq..spqueue)"
	      from ContentAfter, ContentBefore, heapify_Postcond; */
	    /*: note ContentFrame: 
		"\<forall> pq. pq \<in> PriorityQueue \<longrightarrow> pq..spqueue = old (pq..spqueue)"
	      from ContentFrame, ContentAfter; */
	}
    }
}
