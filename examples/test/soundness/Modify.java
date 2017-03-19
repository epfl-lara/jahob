class Modify {

    public static int foo;
    private int bar;
    

    public static void modify_foo()
	/* requires "True"
	   ensures "True"
	*/ 
    {
	foo = 3;
    }

    public void modify_bar()
	/* requires "True"
	   ensures "True"
	*/ 
    {
	bar = 3;
    }

}
