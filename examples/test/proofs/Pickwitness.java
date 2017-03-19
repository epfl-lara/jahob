class Pickwitness {

    /*:
      public static ghost specvar content :: "(obj * obj) set";
     */

    public static Object get1(Object k)
	/*:
	  requires "EX v. (k,v) : content"
	  ensures "True"
	 */
    {
	//: ghost specvar v0 :: obj;
	//: havoc v0 suchThat byPre: "(k,v0) : content";
	//: assert "(k,v0) : content";
    }

    public static Object get2(Object k)
	/*:
	  requires "EX v. (k,v) : content"
	  ensures "True"
	 */
    {
	//: pickWitness v0::obj suchThat byPre: "(k,v0) : content";
    }

    public static Object get3(Object k)
	/*:
	  requires "True"
	  ensures "True"
	 */
    {
	//: ghost specvar v0 :: obj;
	//: havoc v0 suchThat byPre: "(k,v0) : content";
	//: assert "(k,v0) : content";
    }

}
