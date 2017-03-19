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

      invariant contentDefinition1: "init --> (ALL k v.
      (k,v) : content --> (EX i. (0 <= i & i < table..Array.length & (k,v) : table.[i]..AssocList.content)))"

      invariant contentDefinition2: "init --> (ALL k v.
      (EX i. (0 <= i & i < table..Array.length & (k,v) : table.[i]..AssocList.content)) --> (k,v) : content)"

      invariant TableNotNull: "init --> table ~= null"
      invariant TableAlloc: "table : Object.alloc"

      invariant Coherence: "(ALL i k v. (init --> ( ((0<= i & i < table..Array.length) --> 
                                         ((k,v) : table.[i]..AssocList.content --> h k (table..Array.length) = i)))))"

      invariant TableInjectivity: "(ALL u v. ((u : Object.alloc & v : Object.alloc 
         & u ~= v & u ~= null & u : Hashtable & v : Hashtable) --> 
      u..table ~= v..table))"					  

      invariant TableSize: "table..Array.length > 0"
    */


    private static int compute_hash(Object o1)
    /*: requires "True"
        ensures "result = h o1 (table..Array.length) & 0 <= result & result < table..Array.length &
                 Object.alloc = old Object.alloc"
    */
    {
	// some Object.hashCode magic here
	//:assume "False"
	return 0;
    }

    public void init2(int n)
	/*: requires "n > 0"	    
	    modifies content, init
	    ensures "content = {} & init"
	*/
    {
	//: init := "False"
        AssocList[] t = new /*: hidden */ AssocList[n];
        //: assume "ALL j. 0 <= j & j < n --> t.[j] = null"
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
	add(key, new_value);
    }

    ////////// future improvements

    public boolean isEmpty() 
    // because we cannot check size, must iterate over all buckets!
    // We seem to need BAPA to do this in constant time?  Or add some BAPA axioms?
    {
        return (size<=0);
    }

    
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

/*	table = new /: hidden / AssocList[m];
	
	// assume "ALL j. 0 <= j & j < m --> table.[j] = null"	
	// content := "{}"
        */
	init2(m);
	
	rehash_aux(0, t);
    }

    private void testinv1(int n)
    {
        int i;
        //: havoc "i";
        //: havoc "Hashtable.content";
        AssocList[] t = new AssocList[n];
        /*: assume "0 <= i 
          & comment ''previouslyHad'' (old content \<subseteq> content Un {(k,v). (EX j. (i <= j & j < t..Array.length & (k,v) : t.[j]..AssocList.content))})
          & {(k,v). (EX j. (i <= j & j < t..Array.length & (k,v) : t.[j]..AssocList.content))}  \<subseteq>  old content
          & content \<subseteq> old content
          & theinvs & init"
        */
        /*: noteThat breakdown1: "{p. (EX j. (i <= j & j < t..Array.length & p : t.[j]..AssocList.content))} \<subseteq>
                                 t.[i]..AssocList.content Un
                                {p. (EX j. (i + 1 <= j & j < t..Array.length & p : t.[j]..AssocList.content))}"; */
        //: assume "i < Array.length t";
        rehash_bucket(t[i]);
        /*: noteThat breakdown2: "{p. (EX j. (i <= j & j < t..Array.length & p : t.[j]..AssocList.content))} \<subseteq>
                                 t.[i]..AssocList.content Un
                                {p. (EX j. (i + 1 <= j & j < t..Array.length & p : t.[j]..AssocList.content))}"; */
        i = i+1;
        //: assert "old content \<subseteq> content Un {(k,v). (EX j. (i <= j & j < t..Array.length & (k,v) : t.[j]..AssocList.content))}";
        //: assume "False";
    }

    private void testinv2(int n) // should work with :OrderAxioms:ArithAxioms
    {
        int i;
        //: havoc "i";
        //: havoc "Hashtable.content";
        AssocList[] t = new AssocList[n];
        //: ghost specvar tsize :: int;
        //: assume "i < tsize";
        /*: assert "{p. (EX j. (i <= j & j < tsize & p : t.[j]..AssocList.content))} \<subseteq>
                    t.[i]..AssocList.content Un
                    {p. (EX j. (i + 1 <= j & j < tsize & p : t.[j]..AssocList.content))}"; */
        //: assume "False";
    }

    private void testp()
    {
        int i;
        //: ghost specvar P :: "int => bool";
        //: assume "ALL j. i <= i --> P j ";
        i = i + 1;
        //: assume "P i";
        //: assert "ALL j. i <= i --> P j ";
        //: assume "False";
    }

    private void testm1(Hashtable ht)
    {
        //: assume "ALL (u::obj). u = u";
        //: assert "ALL (v::obj). v = v";
    }

    private void test0(Hashtable ht)
    {
        //: assume "ALL (u::obj). u = ht --> u..content = {}";
        //: assert "ALL (v::obj). v = ht --> v..content = {}";
    }

    private void test1()
    {
        //: assume "theinvs";
        //: assert "theinvs";
    }

    private void test2()
    {
        int i;
        boolean b1, b2;
        //: assume "theinvs";
        if (b1) {
            b2 = true;
        } else {
            b2 = b1;
        }
        //: assert "theinvs";
    }

    private void test3(AssocList al)
    {
        /*: assume "theinvs & init"; */
        rehash_bucket(al);
        //: assume "False";
    }

    private void test4()
    {
        AssocList[] t = new AssocList[1];

        /*: assume "theinvs & init"; */
        rehash_bucket(t[0]);
        //: assume "False";
    }

        /* One could also all invariants and specvars as applying not to
           hash table but to the array object itself.  Then one could talk about
           of an Array object as opposed to a content of a Hashtable object.  We would
           have static methods that insert and remove elements on the array, and then
           have hashtable methods that simply invoke them on their array.
           When rehashing, we only need these static methods.

           The added benefit is one level of redirection less, so perhaps they would
           be easier to verify.
        */


}
