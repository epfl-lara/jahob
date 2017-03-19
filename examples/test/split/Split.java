class Split {
    public boolean a, b;

    // supposed to succeed
    public static void test0() 
    /*:
      requires "a & b"
      ensures "a"
     */
    {
        //: noteOnly "a"
    }

    // supposed to fail
    public static void test1() 
    /*:
      requires "a & b"
      ensures "a"
     */
    {
        //: noteOnly "b"
    }

    // supposed to succeed
    public static void test2() 
    /*:
      requires "a & b"
      ensures "a & b"
     */
    {
    }
}
