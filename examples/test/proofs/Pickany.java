class Pickany {
    /*:
      ghost specvar P :: "obj => bool";
      ghost specvar Q :: "obj => bool";
     */

    public static void test() 
    /*:
      requires "ALL x. P x --> Q x"
      ensures "ALL u v. P u & v=u --> Q v"
     */
    {
	{//: pickAny u, v suchThat cond: "P u & v=u";
	 //: noteThat p1: "P v" from cond;
	    {
	    //: pickAny x suchThat "A x";
	    //: noteThat "B x";
	    }
	 //: noteThat p2: "Q v" from Precondition forSuch u, v;
	}
    }

}