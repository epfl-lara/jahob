class Calls {
    private Calls another;

    private static Calls foo;

    static Calls arr[];
    public static boolean init;

    //: invariant ci: "init --> foo ~= null & arr ~= null & arr..length > 0 & arr : hidden & hidden \<subseteq> alloc"

    private static void changeArray()
	//: requires "init & theinvs" modifies arrayState ensures "True"
	//ensures "ALL i a. a : Array & a ~: old hidden --> a.[i] = old (a.[i])"
    {
	arr[0] = new Calls();
    }

    public static void pchangeArray()
	//: requires "init" ensures "True"
    {
	arr[0] = new Calls();
	changeArray();
    }

    private static void checkArray()
	//: requires "init & theinvs" modifies arrayState ensures "True"
    {
	Calls c1 = arr[0];
	changeArray();
	// assert same: "arr.[0] = c1"
    }

    private static void checkArray1()
	//: requires "init & theinvs" ensures "True"
    {
	Calls c1 = arr[0];
	pchangeArray();
	// assert same: "arr.[0] = c1"
    }

    private static void checkArray2()
	//: requires "init & theinvs" ensures "True"
    {
	Calls c1 = arr[0];
	checkArray1();
	//: assert same: "arr.[0] = c1"
    }

    private static Calls changeNew()
    /*: requires "theinvs & init"
        modifies "foo..another"
        ensures "result ~: old alloc & result..another ~= null"
     */
    {
	foo.another = new Calls();
	Calls c = new Calls();
	c.another = new Calls();
	return c;
    }
    
    private static void check()
    /*: requires "theinvs & init"
        //modifies "foo..another"
        ensures "True"
     */
    {	
	Calls c = changeNew();
    }
}
