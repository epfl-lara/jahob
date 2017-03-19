/*
 * FuncTree.java
 *
 * Created on August 2, 2006
 * Functional Trees
 */

 class Pair {
	public int key;
	public Object data;
    }

public final class FuncTree
{
    private int key;
    private Object data;
    private FuncTree left;
    private FuncTree right;
    private int height;

   

   /*: 
    public ghost specvar content :: "(int * obj) set" = "({} :: (int * obj) set)";
    public ghost specvar init :: bool = "False";
    
    // If you're game enough....
 
    //invariant ("height invariant 1") "(init & this ~= null & left = null & right = null) --> height = 1"
    //invariant ("height invariant 2") "(init & this ~= null & left ~= null & right = null) --> height = left..height + 1"
    //invariant ("height invariant 3") "(init & this ~= null & left ~= null & right ~= null) --> 
    //                ((left..height > right..height --> height = left..height + 1) 
    //               & (left..height <= right..height --> height = right..height + 1))"
  
    // If you *REALLY* enjoy pain...

    //invariant ("balancing !") "(init & this ~= null & left ~= null & right ~= null) --> 
    //                "left..height = right.height | left..height = right.height + 1| right..height = left.height + 1" 

    // back to normal

    invariant ("content definition") "(this ~= null)--> ( content = {(key, data)} Un left..content Un right..content)"

    invariant ("null implies empty") "this = null --> content = {}"
    invariant ("no null data") "this ~= null --> data ~= null"

    // invariant ("init means left init")  "init --> left..init"
    // invariant ("init means right init") "init --> right..init"
    // invariant ("null is init")         "this = null --> init"

    // Changelog :
    //   a) Made the equality stricts (required for efficient membership test...). Or could we say k<key --> k is in the left subtree ?
    //   b) a parenthesis was misplaced, so the ALL was capturing more than I tought.



    invariant ("left children are smaller") "(ALL k. (ALL v. ( (k,v) : left..content --> k < key)))"
    invariant ("right children are bigger") "(ALL k. (ALL v. ( (k,v) : right..content --> k > key)))"

    //invariant ("key uniqueness") "(ALL k1. (ALL k2. (ALL v. (((k1,v) : content & (k2,v) : content) --> k1=k2))))"
    */

   public static FuncTree empty_set() 
   /*: requires "True"
       ensures "result..content = {}"
    */
   {
      return null;
   }
   
    public static int compute_height(FuncTree t)
    /* requires "t..left..init & t..right..init"
    //ensures "(height invariants 1, 2 & 3.....)"
    */
    {
	if (t == null) return 0;
	else if (t.left == null & t.right == null) return 1;
	else if (t.left == null) return (t.right.height + 1);
	else if (t.right == null) return (t.left.height + 1);
	else if (t.right.height > t.left.height) return (t.right.height + 1);
	else return (t.left.height + 1);
    }


    /* changelog :
       a) I forgot the case where t is null (shame)
       b) needed to add the init flag - because inv does not hold in recursive call
       c) removed invariant "empty implies nil"
       d) found a bug in jahob (boolean ghost specvar are not initialised !)
       e) made specification simpler (allowing duplicates keys)
       f) changed code (run-time complain in case of duplicates keys)
    */
    public static FuncTree add(int k, Object v, FuncTree t)
    /*: requires "v ~= null & (ALL y. (k,y) ~: t..content)"
        ensures "result..content = t..content Un {(k,v)}"
    */
    {
	if (t==null) {
	    FuncTree r = new FuncTree();
	    r.data = v;
	    r.key = k;
	    r.left = null;
	    r.right = null;
	    r.height = 1;
	    //: "r..content" := "{(k,v)}";
	    // "r..init" := "True";
	    return r;
	}
	else {
	    FuncTree left;
	    FuncTree right;

            if (k < t.key) {
                left = add(k, v, t.left);
                right = t.right;
	    }
            else {
                //: noteThat "t..key < k";
                left = t.left;
                right = add(k, v, t.right);
            }

	    FuncTree r = new FuncTree();
	    r.data = t.data;
	    r.key = t.key;
	    r.left = left;
	    r.right = right;
            // "r..init" := "True"
            //: "r..content" := "t..content Un {(k,v)}";
            return r;
	}
    }

    public static FuncTree update(int k, Object v, FuncTree t)
    /*: requires "v ~= null"
        ensures "result..content = (t..content \<setminus> {(x,y). x=k}) Un {(k,v)}"
    */
    {
	FuncTree r = new FuncTree();
	// "r..init" := "False";

	if (t==null) {
            //: assume "False";
	    r.data = v;
	    r.key = k;
	    r.left = null;
	    r.right = null;
	    r.height = 1;
	    //: "r..content" := "{(k,v)}";
	    // "r..init" := "True";
	    return r;
	}
	else 
            if (k < t.key) {
                //: assume "False";
                r.data = t.data;
                r.key = t.key;
                r.left = update(k, v, t.left);
                r.right = t.right;
	    }
            else if (t.key < k) {
                //: assume "False";
                r.data = t.data;
                r.key = t.key;
                r.left = t.left;
                r.right = update(k, v, t.right);
            } else {
                // assume "False";
                //: noteThat "t..key = k";
                r.data = v;
                r.key = k;
                r.left = t.left;
                r.right = r.right;
                //: noteThat "comment ''A3'' (t..content = {(k,y). y = t..data} Un t..left..content Un t..right..content)";
                //: noteThat "comment ''A4'' (r..content = {(k,v)} Un t..left..content Un t..right..content)";
                //: noteThat "comment ''A1'' (ALL x y. (x,y) : t..left..content --> x < k)";
                //: noteThat "comment ''A2'' (ALL x y. (x,y) : t..right..content --> k < x)";
            }
            // "r..init" := "True"
            //: "r..content" := "(t..content \<setminus> {(x,y). x=k}) Un {(k,v)}";
            return r;
    }

    public static boolean member(int k, FuncTree t)
	/*: requires "True"
	    ensures "result = (EX v. ((k,v) : t..content))"
	*/
    {
	if (t == null)
	    return false;
	else 
	    if (k == t.key)
		return true;
	    else if (k < t.key) 
		return member(k, t.left);
       	    else 
		return member(k, t.right);
    }

    public static Object lookup(int k, FuncTree t)
	/*: requires "True"
	    ensures "((k, result) : t..content) | (result = null & (ALL v. (k,v) ~: t..content))"
	*/
    {
	if (t == null)
	    return null;
	else 
	    if (k == t.key)
		return t.data;
	    else if (k < t.key) 
		return lookup(k, t.left);
       	    else 
		return lookup(k, t.right);
    }


    public static Pair max(FuncTree t)
	/*: requires "t..content ~= {}"
	    ensures "result ~= null
	    & result..Pair.data ~= null
	    & ((result..Pair.key, result..Pair.data) : t..content) 
	    & (ALL k. (k ~= result..Pair.key --> (ALL v. ((k,v) : t..content --> k < result..Pair.key))))"
	*/
    {
	Pair r = new Pair();
	
	if (t.right == null) {
	    r.key = t.key;
	    r.data = t.data;
	    return r;
	}
	else
	    return max(t.right);
    }


    static FuncTree remove_max(FuncTree t, int k, Object v)
	/*: requires "(k,v) : t..content & (ALL x.(x ~= k --> (ALL y. ((x,y) : t..content --> x < k))))"
	    ensures "result ~= t
	    & result..content = t..content - {(k,v)} 
	    & (ALL x. (ALL y. ((x,y) : result..content --> x < k)))"
	*/
    {
	if (t.right == null) 
	   {
	       return t.left;
	   }
	else
	    {
		FuncTree foo = remove_max(t.right, k, v);

		FuncTree r = new FuncTree();
		r.key = t.key;
		r.data = t.data;
		r.left = t.left;
		r.right = foo;
		//: noteThat "t..key ~= k"
		//: noteThat "(k, v) ~: t..left..content"
		//: noteThat "r..right..content = t..right..content - {(k,v)}"
		//: noteThat "r..left..content = t..left..content"
		//: "r..content" := "t..content - {(k,v)}"
		// "r..init" := "True"
		return r;
	    }
    }

    /* Change log :
       a) modified the specification of max and remove_max (probably in vain)
       b) I forgot the case where the max IS what we want to remove....
    */
       
    public static FuncTree remove(int k, FuncTree t)
	/*: requires "True"
	  ensures "result..content = t..content - {(x,y). x=k}"
	*/
    {
	if (t == null)
	    return null;
	else 
	    if (k == t.key)
		{
		    if ((t.right == null) && (t.left == null)) return null;
		    else if (t.left == null) { 
			return t.right; }
		    else if (t.right == null) {
			return t.left; 
		    }
		    else {
			Pair m = max(t.left);
		       
			FuncTree foo = remove_max(t.left, m.key, m.data);
			FuncTree r = new FuncTree();
			r.key = m.key;
			r.data = m.data;
			r.left = foo;
			r.right = t.right;
			//: "r..content" := "t..content - {(x,y). x=k}"
			return r;
		    }
		} 
	    else {
		FuncTree foo;
		FuncTree bar;
		if (k < t.key) {
		    if (t.left == null) { 
			return t;
		    }
		    else {
			foo = remove(k, t.left);
			bar = t.right;
		
		    }
		}
		else {
		    if (t.right == null) {
			return t;
		    }
		    else {
			foo = t.left;
			bar = remove(k, t.right);
		    }

		}
		FuncTree r = new FuncTree();
		r.key = t.key;
		r.data = t.data;
		r.left = foo;
		r.right = bar;
		//:noteThat "k ~= r..key"
		//:noteThat "(ALL y. ((k,y) ~: bar..content))"
		//:noteThat "(ALL y. ((k,y) ~: foo..content))"
		//: "r..content" := "t..content - {(x,y). x=k}"
		return r;
	    }
    }


  public static Pair min(FuncTree t)
	/*: requires "t..init & t..content ~= {}"
	    ensures "((result..Pair.key, result..Pair.data) : t..content) 
	           & (ALL k. (ALL v. ((k,v) : t..content --> k >= result..Pair.key)))"
	*/
    {
	Pair r = new Pair();
	
	if (t.left == null) {
	    r.key = t.key;
	    r.data = t.data;
	    return r;
	}
	else
	    return min(t.left);
    }

    public static boolean is_empty(FuncTree t)
    /*: requires "t..init"
        ensures "result = (t..content = {})";
    */
    {
        return (t==null);
    }


    public static void main(String args[])
    {
	FuncTree ft = empty_set();
	Object t = new Object();

	FuncTree ft2 = add(0, t, ft);
	FuncTree ft3 = remove(1, ft2);
    }



}
