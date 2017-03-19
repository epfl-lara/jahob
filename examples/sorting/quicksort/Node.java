public class Node {
    int    key;
    Object data;

    private static void qsort(Node[] a, int start, int end) 
    /*:
        requires "a ~= null 
          & 0 <= start  & start <= end & end <= (Array.length a)
          & (ALL k. start <= k & k < end --> a.[k] ~= null)"
        modifies "Array.arrayState"
        ensures "a ~= null
	  & (ALL k. (start <= k & k < end) --> a.[k] ~= null)
          & (ALL arr k. a ~= arr --> arr.[k] = old (arr.[k]))
          & (ALL k. (0 <= k & k < start) --> a.[k] = old (a.[k]))
          & (ALL k. end <= k & k < (Array.length a) --> a.[k] = old (a.[k]))
          & {n. (EX k. start <= k & k < end & old (a.[k]) = n)} = 
             {n. (EX k. start <= k & k < end & a.[k] = n)}
          & (ALL k. start <= k & k < (end - 1) --> 
              a.[k]..Node.key <= a.[k+1]..Node.key)"
      */
    {
        if (start >= end - 1)
            return;
        int pivot = a[end-1].key;
        int l = start;
        int r = start;
        while
            /*:
                inv "start <= l & l <= r & r <= end
		  & Node.key = old (Node.key)
		  & Node.data = old (Node.data)
                  & (ALL arr k. a ~= arr --> arr.[k] = old (arr.[k]))
                  & (ALL k. 0 <= k & k < start --> a.[k] = old (a.[k]))
                  & (ALL k. r <= k & k < (Array.length a) 
                      --> a.[k] = old (a.[k]))
                  & {n. (EX k. start <= k & k < end & old (a.[k]) = n)} = 
                      {n. (EX k. start <= k & k < end & a.[k] = n)}
                  & (ALL k. start <= k & k < l --> a.[k]..Node.key <= pivot)
                  & (ALL k. l <= k & k < r --> a.[k]..Node.key > pivot)
		  & (ALL k. start <= k & k < end --> a.[k] ~= null)
		  & (r < end --> a.[end - 1]..Node.key = pivot)
		  & (r = end --> start < l & a.[l - 1]..Node.key = pivot)"
              */
            (r < end) {
            if (a[r].key <= pivot) {
		/*: noteThat before: "{n. (EX k. start <= k & k < end & old (a.[k]) = n)} = 
                      {n. (EX k. start <= k & k < end & a.[k] = n)}";
		    noteThat range: "start <= l & l < end & start <= r & r < end & 0 <= start & end <= (Array.length a)"
		*/
                Node tmp = a[r];
                a[r] = a[l];
                a[l] = tmp;
		/*: noteThat after: "{n. (EX k. start <= k & k < end & old (a.[k]) = n)} = 
                      {n. (EX k. start <= k & k < end & a.[k] = n)}" from before, range;
		*/
                l = l + 1;
            }
            r = r + 1;
        }

	/*: 
	  ghost specvar p1 :: "int => bool";
	  ghost specvar pl :: "int => bool";
	  ghost specvar p2 :: "int => bool";
	  ghost specvar p :: "int => bool";
	  assume "(ALL k. p1 k = (start <= k & k < l - 1))";
	  pl := "%k. (k = l - 1)";
	  assume "(ALL k. p2 k = (l <= k & k < end))";
	  assume "(ALL k. p  k = (start <= k & k < end))";
	  //p1 := "%k. (start <= k & k < l - 1)";
	  //p2 := "%k. (l <= k & k < end)";
	  //p := "%k. (start <= k & k < end)";

	  ghost specvar less_pivot :: "obj => bool";
	  less_pivot := "%n. n..Node.key <= pivot";
	  noteThat union: "(ALL k. (p1(k) | pl(k) | p2(k)) = p(k))";
	*/
	

	/*:
	  ghost specvar a1 :: "int => obj"
	  a1 := "%k. a.[k]";
	*/
        /*: noteThat perm1:
	  "{n. (EX k. p(k) & old (a.[k]) = n)} = 
	  {n. (EX k. p(k) & a.[k] = n)}";
	*/
	/*: noteThat pivot1: 
	  "(ALL k. p1(k) --> less_pivot(a.[k]))
	  &(ALL k. p2(k) --> ~less_pivot(a.[k]))"
	*/

        Node.qsort(a, start, l-1);
	
        /*: 
	  noteThat perm2a:
	  "{n. (EX k. p1(k) & a1 k = n)} = 
	  {n. (EX k. p1(k) & a.[k] = n)}";
	  noteThat perm2b:
	  "{n. (EX k. pl(k) &  a1 k = n)} = 
	  {n. (EX k. pl(k) &  a.[k] = n)}";
	  noteThat perm2c:
	  "{n. (EX k. p2(k) &  a1 k = n)} = 
	  {n. (EX k. p2(k) &  a.[k] = n)}";
	*/
        /*: noteThat perm2d:
	  "{n. (EX k. p(k) & a1 k = n)} = 
	  {n. (EX k. p(k) & a.[k] = n)}"
	  from union,perm2a,perm2b,perm2c,perm2d;
	*/
	/*: noteThat pivot2: 
	  "(ALL k. p1(k) --> less_pivot(a.[k]))
	  &(ALL k. p2(k) --> ~less_pivot(a.[k]))"
	  from pivot1, perm2a,perm2c,pivot2;
	 */
        /*: noteThat perm2:
	  "{n. (EX k. p(k) & old (a.[k]) = n)} = 
	  {n. (EX k. p(k) & a.[k] = n)}"
	  from union,perm1,perm2c,perm2;
	*/
	/*:
	  ghost specvar a2 :: "int => obj";
	  a2 := "%k. a.[k]";
	*/

        Node.qsort(a, l, end);
	
        /*: noteThat perm3a:
	  "{n. (EX k. p2(k) & a2 k = n)} = 
	  {n. (EX k. p2(k) & a.[k] = n)}";
	  noteThat perm3b:
	  "{n. (EX k. pl(k) & a2 k = n)} = 
	  {n. (EX k. pl(k) & a.[k] = n)}";
	  noteThat perm3c:
	  "{n. (EX k. p1(k) & a2 k = n)} = 
	  {n. (EX k. p1(k) & a.[k] = n)}";
	*/
        /*: noteThat perm3d:
	  "{n. (EX k. p(k) & a2 k = n)} = 
	  {n. (EX k. p(k) & a.[k] = n)}"
	  from union,perm3a,perm3b,perm3c,perm3d;
	*/

	/*: noteThat pivot3: 
	  "(ALL k. p1(k) --> less_pivot(a.[k]))
	  &(ALL k. p2(k) --> ~less_pivot(a.[k]))"
	  from pivot2, perm3a, perm3c,pivot3;
	 */
        /*: noteThat perm3:
	  "{n. (EX k. p(k) & old (a.[k]) = n)} = 
	  {n. (EX k. p(k) & a.[k] = n)}" from perm2,perm3c, perm3;
	*/
    }
}
