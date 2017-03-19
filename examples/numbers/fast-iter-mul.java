class Test {
    private static int fip(int x, int y)
    /*: requires "x >= 0 & y >= 0"
        ensures "result = x * y"
    */
    {	
	int y1 = y;
	int a = x;
	int r = 0;
	while /*: inv "comment ''A'' (x * y = r + a * y1)
                    &  comment ''B'' (y1 >= 0)" */
	    (y1 > 0) {
	    if (y1 % 2 != 0) {
		r = r + a;
		y1 = y1 - 1;
	    }
	    //: note stillInv: "x * y = r + a * y1 &  y1 >= 0"

	    //: note zeroMod: "y1 mod 2 = 0";
	    //: note divisible: "2 * (y1 div 2) = y1";
	    y1 = y1 / 2;
	    a = 2 * a;
	}
	return r;
    }
}
