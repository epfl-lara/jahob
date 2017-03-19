class Hashtable {

    /*
      Uses AssocList.java to implement buckets.
     */

    private AssocList[] table = null;

    private int size;

    /*:
      public ghost specvar content :: "(obj * obj) set" 
      public ghost specvar init :: "bool" = "False :: bool"

      private static ghost specvar h :: "obj => int"
      
      invariant HiddenArray: "init --> table : hidden"

      invariant contentDefinition1: "init --> (ALL k v.
      (k,v) : content --> (EX i. (0 <= i & i < table..Array.length & (k,v) : table.[i]..AssocList.content)))"

      invariant contentDefinition2: "init --> (ALL k v.
      (EX i. (0 <= i & i < table..Array.length & (k,v) : table.[i]..AssocList.content)) --> (k,v) : content)"

      invariant TableNotNull: "init --> table ~= null"
      invariant Coherence: "init --> (ALL i. ((0<= i & i < table..Array.length) --> 
                                         (ALL k. (ALL v. (
					    (k,v) : table.[i]..AssocList.content --> h k = i)))))"

      invariant TableInjectivity: "(ALL u v. ((u : Object.alloc & v : Object.alloc 
         & u ~= v & u ~= null & u : Hashtable & v : Hashtable) --> 
      u..table ~= v..table))"	

      invariant ArrayAlloc: "table : Object.alloc"
				    
    */


    private static int compute_hash(Object o1)
    /*: requires "True"
        ensures "result = h o1 & 0 <= result & result < table..Array.length &
                 Object.alloc = old Object.alloc"
    */
    {
	//:assume "False"
	return 0;
    }

    /*
    public void init(int n)
	/: requires "n > 0"	    
	    modifies content, init
	    ensures "content = {} & init"
	/
    {
	//: assume "ALL t. t : Object.alloc --> t..Hashtable.table : Object.alloc"
	//: init := "False"
        AssocList[] t = new /: hidden / AssocList[n];
	int i = 0;

	while 
	    /: inv "(ALL j. ((0 <= j & j < i) --> t.[j]..AssocList.content = {}))
	           & (0 <= i)
		   & (i <= t..Array.length)
	           & (ALL a. a ~= t --> 
                      (ALL p. Array.arrayState a p = (old Array.arrayState) a p))
                   & Object.alloc = old Object.alloc Un {t}"
		//   & (ALL ht. ((ht : Hashtable & ht : Object.alloc & ht ~= this) --> ht..table ~= t)) / 
	    (i < t.length) {
	    t[i] = AssocList.nil();
	    i = i+1;
	}
	size = n;
	table = t;
	//: content := "{}"
	//: init := "True"
    }
*/

    public void init2(int n)
	/*: requires "n > 0"	    
	    modifies content, init
	    ensures "content = {} & init"
	*/
    {
	//: init := "False"
        AssocList[] t = new /*: hidden */ AssocList[n];
	size = n;
	table = t;
	//: content := "{}"
	//: init := "True"
    }

    public void add(Object key, Object value)
    /*: requires "init & key ~= null & value ~= null"
	modifies content
	ensures "content = (old content) Un {(key, value)}"
    */
    {
	int hash = compute_hash(key);
        AssocList al = AssocList.cons(key, value, table[hash]);
        table[hash] = al;
	//: content := "(old content) Un {(key, value)}"
    }
 
    public Object lookup(Object key)
    /*: requires "init & key ~= null"
	ensures " (result ~= null --> (key, result)  : content) 
	        & (result = null --> (ALL v. (key, v) ~: content))"
    */
    {
	int hash = compute_hash (key);
	Object res = AssocList.lookup (key, table[hash]);
	return res;
    }

    public void remove(Object key)
    /*: requires "init & key ~= null"
	modifies content
	ensures "content = (old content) - {(x,y) . x = key}"
    */
    {
	int hash = compute_hash (key);
	AssocList new_bucket = AssocList.remove_all (key, table[hash]);
	table[hash] = new_bucket;
	//: content := "(old content) - {(x,y) . x = key}"
    }

    public void update(Object key, Object new_value)
    /*: requires "init & key ~= null & new_value ~= null"
	modifies content
	ensures "content = ((old content) \<setminus> {(x,y) . x = key}) Un {(key, new_value)}"
    */
    {
	remove(key);
	add(key, new_value);
    }

}
