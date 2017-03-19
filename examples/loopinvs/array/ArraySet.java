class ArraySet {
    private static Object[] a;
    public  static int size;

    /*:
      public static specvar init :: bool;
      public static specvar content :: objset;

      vardefs "init == a ~= null" 
      vardefs
        "content == {n. EX j. n = a.[j] & 0 <= j & j < size}";

      invariant "init --> a ~= null & 0 < a..Array.length & 
          0 <= size & size <= a..Array.length";

      invariant ("a is part of private rep") "init --> a : hidden"
    */

    public static void initialize() 
    /*:
      requires "~init"
      modifies init, content
      ensures "init & content = {}";
    */
    {
        a = new /*: hidden */ Object[100];
        size = 0;
    }

    public static void add(Object x)
    /*:
      requires "init & x ~: content"
      modifies content, "Array.arrayState", size
      ensures "(content = old content Un {x}) & (size = (old size) + 1)"
    */
    {
        if (size < a.length) {
            a[size] = x;
            size = size + 1;
        } else {
            //: assume "False" 
	    Object[] b = new Object[2 * a.length];
            int i = 0;
            while (i < a.length) {
                b[i] = a[i];
                i = i + 1;
            }
            b[size] = x;
            size = size + 1;
            a = b;
        }
    }

    public static boolean contains(Object x)
    /*:
      requires "init & x ~= null"
      ensures "result = (x : content)";
     */
    {
	/*: private static ghost specvar content_i :: objset;
	 */

        int i = 0;
        //: content_i := "{}";
        while /*: inv "0 <= i & i <= size &
                 (content_i = {n. EX j. n = a.[j] & 0 <= j & j < i }) &
                 (x ~: content_i)" */
            (i < size) {
            if (a[i] == x) {
                return true;
            } else {
                //: content_i := "content_i Un {a.[i]}";
                i = i + 1;
            }
        }
	//: noteThat "content = content_i";
        return false;
    }

    public static void driver()
    /*: modifies init, "Array.arrayState", size, content
        ensures "init";
    */
    {
	int i = 0;
	int n = 10;
	boolean b0;
	boolean b1;
	Object j = null; 
	
	initialize();
	
	while (i < n)
	{
	    j = new Object ();
	    add(j);
	    i = i + 1;
	}
	Object k = new Object ();

	b0 = contains(j);
	b1 = contains(k);

	//: assert "b0";
	//: assert "~b1";
    }
}
