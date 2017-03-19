class CHTest {

    public static boolean CHOOSE()
    {
	return true;
    }

    public static void test0()
    {
	int x = 0;
	if (CHOOSE()) {
	    x = x + 1;
	} else {
	    x = x + 2;
	}
	//: assert ok: "x = 1 | x = 2";
    }

    public static void test1()
    {
	int x = 0;
	if (CHOOSE()) {
	    x = x + 1;
	} else {
	    x = x + 2;
	}
	//: assert wish1: "x = 1";
    }


    public static void test2()
    {
	int x = 0;
	if (CHOOSE()) {
	    x = x + 1;
	} else {
	    x = x + 2;
	}
	//: assert wish2: "x = 2";
    }
}
