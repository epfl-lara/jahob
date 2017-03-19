class Client {
    public static void test() 
    /*: 
      modifies "List.content" 
      ensures "True";
    */
    {
        List l1 = new List();
        Object o1 = new Object();
        l1.add(o1);
        Object o2 = new Object();
        l1.add(o2);
        while (!l1.empty()) {
            Object oa = l1.getOne();
            l1.remove(oa);
        }
        //: assert "l1..List.content = {}";
    }

    public static void test0() 
    /*: 
      modifies "List.content"
      ensures "True"
    */
    {
        List l1 = new List();
        Object o1 = new Object();
        l1.add(o1);
        Object o2 = new Object();
        l1.add(o2);
        List l2 = new List();
	Object oa = l1.getOne();
	l1.remove(oa);
	//: assert stillDisjoint: "l1..List.content Int l2..List.content = {}";
    }

    public static void test1() 
    /*: 
      modifies "List.content"
      ensures "True"
    */
    {
        List l1 = new List();
        Object o1 = new Object();
        l1.add(o1);
        Object o2 = new Object();
        l1.add(o2);
        List l2 = new List();
	//: ghost specvar oldAlloc :: objset;
	//: oldAlloc := "Object.alloc";
        while //: inv "True"
         (!l1.empty()) {
	    //: noteThat still: "l1 : Object.alloc & l2 : Object.alloc";
        }
    }

    public static void test2() 
    /*: 
      modifies "List.content"
      ensures "True"
    */
    {
        List l1 = new List();
        Object o1 = new Object();
        l1.add(o1);
        Object o2 = new Object();
        l1.add(o2);
        // ghost specvar oldL1 :: objset = "l1..List.content";
        List l2 = new List();
        while // inv "l1..List.content Int l2..List.content = {} & l1..List.content Un l2..List.content = oldL1"
         (!l1.empty()) {
            Object oa = l1.getOne();
            l1.remove(oa);
            l2.add(oa);
        }
        // assert "l2..List.content = oldL1";
    }

   public static void test3(List l1, List l2) 
    /*: 
      requires "l1 ~= null & l2 ~= null & l1 ~= l2 & l1..List.content Int l2..List.content = {}"
      modifies "l1..List.content", "l2..List.content"
      ensures "l1..List.content = {} & l2..List.content = old (l1..List.content) Un old (l2..List.content)"
    */
    {
       while (!l1.empty()) {
	  Object oa = l1.getOne();
	  l1.remove(oa);
	  l2.add(oa);
       }
    }
}
