class Resolve {
    public static int i;
    public static void test() 
    /* 
       requires "i=0 & Foo.bar = 5"
       modifies i
       ensures "i = 10 & Foo.bar = 5"
    */
    {
        Foo.bar = Foo.bar + 1;
        while //: inv "i <= 10 & Foo.bar = 5"
            (i < 10) {
            i = i + 1;
        }
        Foo.bar = Foo.bar - 1;
    }

    //: private static ghost specvar badness :: int;
    //: inv good: "0 <= badness";
    
    private static void work()
    /*: requires "theinv good"
        ensures "badness >= 0"
    */
    {
    }

    private static void worknot()
    /*: requires "True"
        ensures "badness >= 0"
    */
    {
    }

    //: private ghost specvar boldness :: int;
    //: invariant igood: "0 <= boldness";

    private static void iwork()
    /*: requires "theinv igood"
      ensures "ALL r. r : Resolve & r : Object.alloc & r ~= null --> r..boldness >= 0"
    */
    {
    }

    private static void iworknot()
    /*: requires "True"
      ensures "ALL r. r : Resolve & r : Object.alloc & r ~= null --> r..boldness >= 0"
    */
    {
    }
}
