/* Use this command-line to verify the class with Jahob:
     jahob.opt Test.java -class Test -nobackground -usedp isa
   (Make sure you have installed Isabelle and that isabelle is in your path.)
*/
class Test {
    private static int f(int x, int y)
    /*: requires "x >= 0 & y >= 0"
        ensures "result = x * y"
     */
    {
	if (y == 0) {
	    return 0;
	} else {
	    if (y % 2 == 0) {
		int z = f(x, y / 2);
		return (2 * z);
	    } else {
		return (x + f(x, y - 1));
	    }
	}
    }

    private static int fi(int x, int y)
    /*: requires "x >= 0 & y >= 0"
        ensures "result = x * y"
    */
    {	
	int r = 0;
	int i = 0;
	while //: inv "r = i * x  &  i <= y"
	    (i < y) {
	    i = i + 1;
	    r = r + x;
	}
	return r;
    }

    private static int fi1(int x, int y)
    /*: requires "x >= 0 & y >= 1"
        ensures "result = x * y"
    */
    {	
	int r = x;
	int i = 1;
	while //: inv "r = i * x  &  i <= y"
	    (i < y) {
	    i = i + 1;
	    r = r + x;
	}
	return r;
    }

    private static int fi2(int x, int y)
    /*: requires "x >= 0 & y >= 0"
        ensures "result = x * y"
    */
    {	
	if (y == 0) {
	    return 0;
	} else {
	    int r = x;
	    int i = 1;
	    while //: inv "r = i * x  &  i <= y"
		(i < y) {
		i = i + 1;
		r = r + x;
	    }
	    return r;
	}
    }
}