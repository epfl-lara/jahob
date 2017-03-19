class Max {
    private static Object a[];
    private static void initializeFrom(int from)
    /*: requires "a ~= null & 0 <= from & from < a..Array.length"
        modifies "Array.arrayState"
        ensures "ALL (i::int). from <= i & i < a..Array.length --> a.[i] ~= null"
    */
    {
	if (from + 1 < a.length) {
	    initializeFrom(from+1);
	}
	a[from] = new Object();
    }

    private static Object a[];
    private static void initializeFromAssumeHack(int from)
    /*: requires "a ~= null & 0 <= from & from < a..Array.length"
        modifies "Array.arrayState"
        ensures "ALL (i::int). from <= i & i < a..Array.length --> a.[i] ~= null"
    */
    {
	if (from + 1 < a.length) {
	    initializeFrom(from+1);
	}
	Object n;
	//: havoc "n";
	//: assume "n ~= null";
	a[from] = n;
    }

    private static void failInitializeFrom(int from) 
	/* this should fail because modifies clause does not say that other array elements are preserved */
    /*: requires "a ~= null & 0 <= from & from < a..Array.length"
        modifies "Array.arrayState"
        ensures "ALL (i::int). from <= i & i < a..Array.length --> a.[i] ~= null"
    */
    {
	a[from] = new Object();
	if (from + 1 < a.length) {
	    initializeFrom(from+1);
	}
    }
}
