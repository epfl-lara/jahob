class Set {

    /*: public ghost specvar contents :: "objset"
     */

    
    public void add(Object o1) 
    /*: modifies contents
        ensures "contents = (old contents) Un {o1} &
	        (ALL x. x : Object.alloc & x : Set --> x : (old Object.alloc))"
    */
    {
	//: "contents" := "contents Un {o1}";
    }

    public static void orderA(Set A, Set B, Object o1, Object o2)
    {
	A.add(o1);
	B.add(o2);
    }

    public static void orderB(Set A, Set B, Object o1, Object o2)
    {
	B.add(o2);
	A.add(o1);
    }
}
