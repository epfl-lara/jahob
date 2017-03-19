class Hashtable {
    /*
      Uses AssocList.java to implement buckets.
      Uses private (static for now) array.
      Assumes no reentrancy.
     */

    /*:
      public static ghost specvar content :: "(obj * obj) set" 
      public static ghost specvar init :: "bool" = "False :: bool"

      private static ghost specvar h :: "obj => int"
      
     */

    private static AssocList[] table;

    private static int size;

    /*:
      invariant HiddenArray: "init --> table : hidden"

      invariant contentDefinition1: "init --> (ALL k v.
      (k,v) : content --> (EX i. (0 <= i & i < table..Array.length & (k,v) : table.[i]..AssocList.content)))"

      invariant contentDefinition2: "init --> (ALL k v.
      (EX i. (0 <= i & i < table..Array.length & (k,v) : table.[i]..AssocList.content)) --> (k,v) : content)"

      invariant TableNotNull: "init --> table ~= null"
      invariant Coherence: "init --> (ALL i. ((0<= i & i < table..Array.length) --> 
                                         (ALL k. (ALL v. (
					    (k,v) : table.[i]..AssocList.content --> h k = i)))))"
    */

    private static int compute_hash(Object o1)
    /*: requires "True"
        ensures "result = h o1 & 0 <= result & result < table..Array.length"
    */
    {
	// some Object.hashCode magic here
	//:assume "False"
	return 0;
    }

    public static void init(int n)
	/*: requires "n > 0"
	    modifies content, init
	    ensures "content = {} & init"
	*/
    {
	//: init := "False"
	table = new /*: hidden */ AssocList[n];
	size = n;
	int i = 0;
	while 
	    /*: inv "(ALL j. ((0 <= j & j < i) --> table.[j]..AssocList.content = {}))
	           & (0 <= i)
		   & (i <= table..Array.length)
	           & (ALL a. a ~= table --> (ALL p. Array.arrayState a p = (old Array.arrayState) a p))"*/ 
            // (ALL a. a ~= table --> (ALL p. (a..Array.arrayState) p = (old (a..Array.arrayState)) p))"*/ 

	    (i < table.length) {
	    table[i] = AssocList.nil();
	    i = i+1;
	}
	//: content := "{}"
	//: init := "True"
    }

    public static void add(Object key, Object value)
    /*: requires "init & key ~= null & value ~= null"
	modifies content
	ensures "content = (old content) Un {(key, value)}"
    */
    {
	int hash = compute_hash(key);
        table[hash] = AssocList.cons(key, value, table[hash]);
	//: content := "(old content) Un {(key, value)}"
    }

    public static Object lookup(Object key)
    /*: requires "init & key ~= null"
	ensures " (result ~= null --> (key, result)  : content) 
	        & (result = null --> (ALL v. (key, v) ~: content))"
    */
    {
	int hash = compute_hash (key);
	Object res = AssocList.lookup (key, table[hash]);
	return res;
    }

    public static void remove(Object key)
    /*: requires "init & key ~= null"
	modifies content
	ensures "content = (old content) - {(x,y) . x = key}"
    */
    {
	int hash = compute_hash (key);
	table[hash] = AssocList.remove_all (key, table[hash]);
	//: content := "(old content) - {(x,y) . x = key}"
    }

    public static void update(Object key, Object new_value)
    /*: requires "init & key ~= null & new_value ~= null"
	modifies content
	ensures "content = ((old content) \<setminus> {(x,y) . x = key}) Un {(key, new_value)}"
    */
    {
	remove(key);
	add(key, new_value);
    }

}
