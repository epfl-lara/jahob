class Partial {

    /* When checking partial corectness, a looping procedure
       can have arbitrarily strong postcondition. */

    public static Object x;
    public static void test()
    //: ensures "x ~= x";
    {
        test();
    }
}
