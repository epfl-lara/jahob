import java.util.Random;

class Queue
{
    private static Element[] queue;
    public /*: readonly */ static int length;

    /*: 
      public static ghost specvar init :: bool = "False";

      public static ghost specvar content :: "(obj * obj) set"

      invariant contentUpper: "ALL k v. (k,v) : content --> 
                 (EX j. 1 <= j & j <= length & 
                   k = queue.[j]..Element.key & v = queue.[j]..Element.value)";

      invariant contentLower:
        "ALL j. 1 <= j & j <= length --> (queue.[j]..Element.key, queue.[j]..Element.value) : content";

      public static specvar maxlen :: int;
      vardefs "maxlen == queue..Array.length - 1";

      invariant "init --> 0 <= length";
      invariant "init --> length <= maxlen";
      invariant "init --> queue ~= null";
      invariant "init --> (ALL i. 0 < i & i <= length --> queue.[i] ~= null)";

     */

    public static void init(int len)
    /*: requires "0 <= len"
        modifies content, maxlen, length, "Array.arrayState", init
	ensures "content = {} & maxlen = len & length = 0 & init"
    */
    {
	queue = new Element[len];
	length = 0; // the queue is initially empty
        //: "GlobalPriorityQueue.init" := "True";
    }

    public static int maxLengthBuggy()
    /*: 
      requires "init"
      ensures "result = maxlen"
    */
    {
	return queue.length;
    }   
    
    public static int maxLength()
    /*: 
      requires "init"
      ensures "result = maxlen"
    */
    {
	return queue.length - 1;
    }

    public static boolean isEmpty()
    /*: 
      requires "init"
      ensures "result = (length = 0)"
    */
    {
	return (length == 0);
    }

    public static boolean isFullBuggy()
    /*: 
      requires "init"
      ensures "result = (length = maxlen)"
    */
    {
	return (length == queue.length);
    }
   
    public static boolean isFull()
    /*: 
      requires "init"
      ensures "result = (length = maxlen)"
    */
    {
	return (length + 1 == queue.length);
    }
   
    private static int parent(int i)
    {
	return i/2;
    }

    private static int left(int i)
    {
	return 2*i;
    }

    private static int right(int i)
    {
	return 2*i + 1;
    }

    private static int code(Object ob)
    //: ensures "result >= 0"
    {
	return 0;
    }

    public static void insert(Object key, Object value)
    /*: requires "init & length < maxlen"
        modifies content, length, "Array.arrayState"
	ensures "content = old content Un {(key, value)} & 
                 length = old length + 1"
    */
    {
        //: assume "ALL k. 1 < k --> 0 < k div 2";
        //: assume "ALL k. 1 < k --> k div 2 < k";
        length = length + 1;
        int i = length;
        while /*: inv "1 <= i & i <= length &
                       length <= maxlen &
                       (ALL j. 0 < j & j <= length & j ~= i --> queue.[j] ~= null) &
            (ALL j. 1 <= j & j <= length & j ~= i --> 
              (queue.[j]..Element.key, queue.[j]..Element.value) : content) &
                     (ALL k v. (k,v) : content --> 
                          (EX j. 1 <= j & j <= length & j ~= i &
                      k = queue.[j]..Element.key & v = queue.[j]..Element.value))";
               */
            (i > 1 && code(queue[i/2].key) < code(key)) {
            queue[i] = queue[i/2];
            i = i/2;
        }
        //: assume "False";
        Element e = new Element();
        /*: noteThat "(ALL j. 0 < j & j <= length & j ~= i --> 
                        queue.[j] : Object.alloc)" */
        e.key = key;
        e.value = value;
        queue[i] = e;
        //: content := "content Un {(key,value)}";
    }


    /*
    public static void main(String[] args)
    {
	int size = 64;
	Random generator = new Random();
        init(size);

	System.out.println("Inserting...");
	int r = generator.nextInt(size);
	int max = r;
	while(!isFull()) {
	    if (r > max) max = r;
	    insert(new Integer(r), r);
            System.out.println(r);
            if (((Integer)findMax()).intValue() != max)
		System.err.println("There is a bug!");
	    r = generator.nextInt(size);
	}

	System.out.println("\nExtracting...");
	while(!isEmpty())
	{
	    Integer s = (Integer)extractMax();
	    System.out.println(s);
	}
    }
    */
}
