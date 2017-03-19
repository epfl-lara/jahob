class Test {
    boolean b;

    private int foo(int x) 
    //: ensures "result = x | result = x+1"
    {
	if (b) return x;
	else return x+1;
    }

    private int bar(int y)
    //: ensures "2 * y <= result"
    {
	return (foo(y) + foo(y));	
    }

}