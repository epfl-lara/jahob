/*
  Priority queue with content specifications

PLUS:
  non-trivial data structure, 
  verifies very fast with only z3
MINUS:
  heap property not verified
  noteThat statements and 'from' specs essential
 */

public class PriorityQueue
{
    private static PriorityQueueElement[] queue;
    private static int length;

    /*:
      public static specvar init :: bool;
      public static specvar spqueue :: "obj set";
      public static specvar smaxlen :: int;
      public static specvar slength :: int;

      vardefs "init == queue ~= null";
      vardefs "spqueue == 
                 { p. EX i. 0 <= i & i < length & p = queue.[i] }";
		   
      vardefs "smaxlen == queue..Array.length";
      vardefs "slength == length";
      
      invariant LengthLowerInv: "init --> 0 <= length";
      invariant LengthUpperInv: "init --> length <= queue..Array.length";
      invariant NonNullInv: "init -->
                   (ALL i. 0 <= i & i < length --> queue.[i] ~= null)";
      invariant NullInv: "init -->
                   (ALL i. length <= i & i < queue..Array.length -->
		           queue.[i] = null)";
      invariant DistinctInv:
        "init --> 
	  (ALL i j. 0 <= i & i < length & 0 <= j & j < length &
	    queue.[i] = queue.[j] --> i = j)"
    */

    public static void init(int len)
    /*: requires "~init & 0 <= len"
        modifies init, spqueue, smaxlen, slength, "Array.arrayState"
	ensures "init & spqueue = {} & smaxlen = len & slength = 0"
    */
    {
	queue = new PriorityQueueElement[len];
	
	int i = 0;

	while /*: inv "ALL j. 0 <= j & j < i --> queue.[i] = null" */
	    (i < queue.length) {
	    queue[i] = null;
	    i = i + 1;
	}
	length = 0; // the queue is initially empty
    }

    public static int currLength()
    /*: requires "init"
        ensures "result = slength"
    */
    {
	return length;
    }
    
    public static int maxLength()
    /*: requires "init"
        ensures "result = smaxlen"
    */
    {
	return queue.length;
    }
    
    public static boolean isEmpty()
    /*: requires "init"
        ensures "result = (slength = 0)"
    */
    {
	return (length == 0);
    }

    public static boolean isFull()
    /*: requires "init"
        ensures "result = (slength = smaxlen)"
    */
    {
	return (length == queue.length);
    }
   
    private static int parent(int i)
    /*: requires "i > 0"
        ensures "result >= 0 & result < i"
     */
    {
	return (i-1)/2;
    }

    private static int left(int i)
    /*: requires "0 <= i"
        ensures "result >= 0 & result > i"
     */
    {
	return (2*i + 1);
    }

    private static int right(int i)
    /*: requires "0 <= i"
        ensures "result >= 0 & result > i"
     */
    {
	return (2*i + 2);
    }

    public static void insert(PriorityQueueElement e)
    /*: requires "init & e ~= null & slength < smaxlen & e ~: spqueue"
        modifies spqueue, slength, "Array.arrayState"
	ensures "spqueue = old spqueue Un {e} & 
                 (slength = (old slength) + 1)"
    */
    {
	int i = length;
	length = length + 1;
       
	while /*: inv "0 <= i & i < length & e ~: spqueue &
		       old spqueue = { p. EX j. 0 <= j & j < length &
                                          j ~= i & p = queue.[j] } &
		       (ALL j. 0 <= j & j < length & j ~= i --> 
		               queue.[j] ~= null) & 
		       (ALL j k. 0 <= j & j < length & 0 <= k & k < length &
		                 queue.[j] = queue.[k] & j ~= i & k ~= i --> 
				 j = k) &
		       theinv NullInv"
	      */
	    (i > 0 && queue[parent(i)].key < e.key)
	{
	    /*: noteThat ContentBefore:
	      "old spqueue = 
	       { p. EX j. 0 <= j & j < length & j ~= i & p = queue.[j] }";
	    */
	    //: noteThat IBounds: "0 <= i & i < length";
	    int p = parent(i);
	    //: noteThat PBounds: "0 <= p & p < length";
	    queue[i] = queue[p];
	    i = p;
	    /*: noteThat ContentAfter:
	      "old spqueue = 
	       { p. EX j. 0 <= j & j < length & j ~= i & p = queue.[j] }"
	      from ContentBefore, IBounds, PBounds, ContentAfter;
	    */
	}
	/*: noteThat ContentPostLoop:
	  "old spqueue = 
	   { p. EX j. 0 <= j & j < length & j ~= i & p = queue.[j] }"
	*/
	//: noteThat IFinalBounds: "0 <= i & i < length";
	queue[i] = e;
	/*: noteThat ContentDef: "spqueue = {p. \<exists> i. (0 <= i & i < length & p = queue.[i])}";
	    noteThat ContentFinal: "spqueue = old spqueue Un {e}"
	        from ContentPostLoop, ContentDef, IFinalBounds, ContentFinal;
	*/
    }

    public static PriorityQueueElement findMax()
    /*: requires "init & slength > 0"
        ensures "result ~= null & result : spqueue"
    */
    {
	return queue[0];
    }

    public static PriorityQueueElement extractMax()
    /*: requires "init & slength > 0"
        modifies "Array.arrayState", spqueue, slength
        ensures  "slength = old slength - 1 & result ~= null &
	          spqueue = old spqueue - { result }"
    */
    {
	PriorityQueueElement result = queue[0];
	
	length = length - 1;
	queue[0] = queue[length];
	queue[length] = null;
	//: noteThat IntQueueContent: "spqueue = old spqueue - { result }";
	heapify(0);
	/*: noteThat FinalQueueContent: "spqueue = old spqueue - { result }"
	  from IntQueueContent, heapify_Postcondition, FinalQueueContent;
	*/
	return result;
    }

    private static void heapify(int i)
    /*: requires "init & (0 <= i) & theinvs"
        modifies "Array.arrayState"
        ensures "init = old init & spqueue = old spqueue &
	         smaxlen = old smaxlen & slength = old slength & theinvs"
     */
    {
	int l = left(i);
	int m;
	if (l < length && queue[l].key > queue[i].key)
	    m = l;
	else
	    m = i;
	int r = right(i);
	if (r < length && queue[r].key > queue[m].key)
	    m = r;
	if (m != i)
	{
	    PriorityQueueElement p = queue[m];
	    queue[m] = queue[i];
	    queue[i] = p;
	    //: noteThat "spqueue = old spqueue";
	    heapify(m);
	}
    }

    /*
    public static void main(String[] args)
    {
	int size = 32;
	Random generator = new Random();
	init(size);

	System.out.println("Inserting...");
	int r = generator.nextInt(size);
	int max = r;
	while(!isFull())
        {
	    PriorityQueueElement elem;

	    if (r > max) max = r;
	    elem = new PriorityQueueElement();
	    elem.ob = new Integer(r);
	    elem.key = r;

	    insert(elem);
	    System.out.println(r);
	    elem = (PriorityQueueElement) findMax();
	    if (elem.key != max)
		System.err.println("There is a bug!");
	    r = generator.nextInt(size);
	}

	System.out.println("\nExtracting...");
	while(!isEmpty())
	{
	    PriorityQueueElement elem;
	    elem = (PriorityQueueElement)extractMax();
	    System.out.println((Integer)elem.ob);
	}
    }
    */
}
