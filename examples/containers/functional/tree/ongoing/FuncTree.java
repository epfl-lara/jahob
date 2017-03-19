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
class FuncTree
{
    private int key;
    private Object data;
    private FuncTree left;
    private FuncTree right;

   /*: 
    public ghost specvar content :: "(int * obj) set" = "({} :: (int * obj) set)";

    //invariant ("content definition") "(this ~= null)--> ( content = {(key, data)} Un left..content Un right..content)"
    invariant contentDefinition: "(this ~= null)--> ( content = {(key, data)} Un left..content Un right..content)"
    invariant ("null implies empty") "this = null --> content = {}"
    invariant ("no null data") "this ~= null --> data ~= null"

    invariant ("left children are smaller") "(ALL k. (ALL v. ( (k,v) : left..content --> k < key)))"
    invariant ("right children are bigger") "(ALL k. (ALL v. ( (k,v) : right..content --> k > key)))"
    */

   public static FuncTree empty_set() 
   /*: ensures "result..content = {}"
    */
   {
      return null;
   }
   
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
	    //: "r..content" := "{(k,v)}";
	    return r;
	} else {
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
            //: "r..content" := "t..content Un {(k,v)}";
            return r;
	}
    }

    public static FuncTree update(int k, Object v, FuncTree t)
    /*: requires "v ~= null"
        ensures "result..content = (t..content \<setminus> {(x,y). x=k}) Un {(k,v)}"
    */
    {
        FuncTree new_left, new_right;
        Object new_data;
        int new_key;
	if (t==null) {
	    new_data = v;
	    new_key = k;
	    new_left = null;
	    new_right = null;
	} else {
            if (k < t.key) {
                new_left = update(k, v, t.left);
                new_right = t.right;
                new_key = t.key;
                new_data = t.data;
	    } else if (t.key < k) {
                new_left = t.left;
                new_right = update(k, v, t.right);
                new_key = t.key;
                new_data = t.data;
            } else {
                new_data = v;
                new_key = k;
                new_left = t.left;
                new_right = t.right;
            }
        }
        FuncTree r = new FuncTree();
        r.left = new_left;
        r.right = new_right;
        r.data = new_data;
        r.key = new_key;
        //: "r..content" := "(t..content \<setminus> {(x,y). x=k}) Un {(k,v)}";
        return r;
    }

    public static boolean member(int k, FuncTree t)
    /*: ensures "result = (EX v. ((k,v) : t..content))" */
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
    /*: ensures "((k, result) : t..content) | (result = null & (ALL v. (k,v) ~: t..content))" */
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
		FuncTree new_right = remove_max(t.right, k, v);

		FuncTree r = new FuncTree();
		r.key = t.key;
		r.data = t.data;
		r.left = t.left;
		r.right = new_right;
		// noteThat "t..key ~= k"
		// noteThat "(k, v) ~: t..left..content"
		// noteThat "r..right..content = t..right..content - {(k,v)}"
		// noteThat "r..left..content = t..left..content"
		//: "r..content" := "t..content - {(k,v)}"
		return r;
	    }
    }

    public static FuncTree remove(int k, FuncTree t)
	/*: ensures "result..content = t..content - {(x,y). x=k}" */
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
		       
			FuncTree new_left = remove_max(t.left, m.key, m.data);
			FuncTree r = new FuncTree();
			r.key = m.key;
			r.data = m.data;
			r.left = new_left;
			r.right = t.right;
			//: "r..content" := "t..content - {(x,y). x=k}"
			return r;
		    }
		} 
	    else {
		FuncTree new_left, new_right;
		if (k < t.key) {
			new_left = remove(k, t.left);
			new_right = t.right;
		}
		else {
			new_left = t.left;
			new_right = remove(k, t.right);
		}
		FuncTree r = new FuncTree();
		r.key = t.key;
		r.data = t.data;
		r.left = new_left;
		r.right = new_right;
		//: "r..content" := "t..content - {(x,y). x=k}"
		return r;
	    }
    }

  public static Pair min(FuncTree t)
	/*: requires "t..content ~= {}"
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
    /*: ensures "result = (t..content = {})";
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
