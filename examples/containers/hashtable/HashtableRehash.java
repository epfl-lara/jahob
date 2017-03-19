class Hashtable {
    /*
      Uses AssocList.java to implement buckets.
     */

    private AssocList[] table = null;

    private int size;

    /*:
      public ghost specvar content :: "(obj * obj) set" 
      public ghost specvar init :: "bool" = "False :: bool"

      private static ghost specvar h :: "obj => int => int"
      
      invariant HiddenArray: "init --> table : hidden"

      invariant contentDefinition: "init --> 
        content = {(k,v). EX i. 0 <= i & i < table..Array.length & (k,v) : table.[i]..AssocList.content}"

      invariant TableNotNull: "init --> table ~= null"
      invariant TableAlloc: "table : Object.alloc"

      invariant Coherence: "init --> (ALL i k v. 0 <= i & i < table..Array.length --> 
          (k,v) : table.[i]..AssocList.content --> h k (table..Array.length) = i)"

      invariant TableInjectivity: "ALL u v. 
         u : Object.alloc & u : Hashtable & u ~= null &
         v : Object.alloc & v : Hashtable & v ~= u  -->  u..table ~= v..table"

      invariant TableSize: "init --> table..Array.length > 0"
    */


    private int compute_hash(Object o1)
    /*: requires "True"
        ensures "result = h o1 (table..Array.length) & 0 <= result & result < table..Array.length &
                 Object.alloc = old Object.alloc"
    */
    {
	//:assume "False"
	return o1.hashCode() % table.length;
    }

    public void init(int n)
	/*: requires "n > 0"	    
	    modifies content, init
	    ensures "content = {} & init"
	*/
    {
	//: init := "False"
        AssocList[] t = new /*: hidden */ AssocList[n];
	size = 0;
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
	add1(key, value);
        if (size > (4 *table.length) / 5) rehash(table.length + table.length);
	    
    }

    private void add1(Object key, Object value)
    /*: requires "init & key ~= null & value ~= null & theinvs"
	modifies content, size
	ensures "content = (old content) Un {(key, value)} & theinvs &
		Object.alloc Int Hashtable = (old Object.alloc) Int Hashtable"
    */
    {
	int hash = compute_hash(key);
        AssocList al = AssocList.cons(key, value, table[hash]);
        table[hash] = al;
	//: content := "(old content) Un {(key, value)}"
	size = size + 1;
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
	size = size - 1;
    }

    public void update(Object key, Object new_value)
    /*: requires "init & key ~= null & new_value ~= null"
	modifies content
	ensures "content = ((old content) \<setminus> {(x,y) . x = key}) Un {(key, new_value)}"
    */
    {
	remove(key);
	add1(key, new_value);
    }

    /*
    public boolean isEmpty() 
    // because we cannot check size, must iterate over all buckets!
    // We seem to need BAPA to do this in constant time?  Or add some BAPA axioms?
    {
        return (size<=0);
    }
    */
    
    private void rehash_bucket(AssocList bucket)
    /*: requires "theinvs & init"
        modifies content
	ensures "theinvs & content = (old content) Un bucket..AssocList.content"
    */
    {
	AssocList l = bucket;
	
	while 
	    /*: inv "content Un l..AssocList.content = (old content) Un (old (bucket..AssocList.content)) 
	      & theinvs
	      & Object.alloc Int Hashtable = (old Object.alloc) Int Hashtable
	      & (ALL h. ((h ~= this & h : Hashtable & h : Object.alloc) --> h..content = (old (h..content))))" */ 
	    (! AssocList.is_nil(l)) {
	    Pair p = AssocList.getOne(l);
	    l = AssocList.remove(p.key, p.value, l);
	    add1(p.key, p.value);
	}
    }

    private void rehash_aux(int i, AssocList[] t)
   /*: requires "t ~= null & 0 <= i & i < t..Array.length & theinvs & init"
        modifies content
	ensures "theinvs & content = (old content) Un {(k,v). (EX j. (i <= j & j < t..Array.length & (k,v) : t.[j]..AssocList.content))}"
   */
    {
	rehash_bucket(t[i]);
	int j = i+1;
	if (j < t.length) rehash_aux(j, t);
    }

    private void rehash(int m)
    /*: requires "m > 0 & theinvs & init"
        modifies table, size
	ensures "theinvs"
     */
    {
        AssocList[] t = table; 
	init(m);
	rehash_aux(0, t);
        // System.out.println("Rehash ran with " + m);
    }

    /*
    private static void test()
    {
        Hashtable h1 = new Hashtable();
        h1.init(1);
        Object k1 = new Object();
        Object v1 = new Object();
        Object k2 = new Object();
        Object v2 = new Object();
        Object k3 = new Object();
        Object v3 = new Object();
        h1.add(k1, v1);
        h1.add(k2, v2);
        h1.add(k3, v3);
        h1.remove(k2);
        h1.update(k1,v3);
        h1.update(k2,v2);
        if (h1.lookup(k1)==null)
            System.out.println("Lookup returned null!");
        if (h1.lookup(k1)==v1)
            System.out.println("Lookup returned the old value!");
        if (h1.lookup(k1)==v3)
            System.out.println("Lookup returned the right value.");
    }

    public static void main(String[] args)
    {
        test();
    }
    */
}
