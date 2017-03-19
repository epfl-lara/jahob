/*
 * FuncTree.java
 *
 * Created on August 2, 2006
 * 
 * Binary Search Tree Implementing a Map. 

PLUS 
 -instantiable
 -functional
 -sorted by keys
 -operations add, update, remove

MINUS
 -unbalanced
 -functional

 */

class Pair {
    public int key;
    public Object data;
}
class FuncTree
{
    private int key;
    private Object data;
    private FuncTree left, right;

   /*: 
    public ghost specvar content :: "(int * obj) set" = "({} :: (int * obj) set)";

    inv contentDefinition: "(ALL this. this : Object.alloc & this : FuncTree & this ~= null --> 
      ( this..content = {(this..key, this..data)} Un this..left..content Un this..right..content))"
    inv nullEmpty: "(ALL this. this : Object.alloc & this : FuncTree & this = null --> this..content = {})"
    inv dataNotNull: "(ALL this. this : Object.alloc & this : FuncTree & this ~= null --> this..data ~= null)"
    inv leftSmaller: "(ALL this. this : Object.alloc & this : FuncTree --> (ALL k. (ALL v. ( (k,v) : this..left..content --> k < this..key))))"
    inv rightBigger: "(ALL this. this : Object.alloc & this : FuncTree --> (ALL k. (ALL v. ( (k,v) : this..right..content --> k > this..key))))"    
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
        return add1(k,v,t);
    }
   
    private static FuncTree add1(int k, Object v, FuncTree t)
    /*: requires "v ~= null & (ALL y. (k,y) ~: t..content) & theinvs"
        ensures "result..content = t..content Un {(k,v)} & theinvs"
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
	    FuncTree new_left;
	    FuncTree new_right;

            if (k < t.key) {
                new_left = add1(k, v, t.left);
                new_right = t.right;
	    }
            else {
                //: assert "t..key < k";
                new_left = t.left;
                new_right = add1(k, v, t.right);
            }
	    FuncTree r = new FuncTree();
	    r.data = t.data;
	    r.key = t.key;
	    r.left = new_left;
	    r.right = new_right;
            //: "r..content" := "t..content Un {(k,v)}";
            return r;
	}
    }

    public static FuncTree update(int k, Object v, FuncTree t)
    /*: requires "v ~= null"
        ensures "result..content = (t..content \<setminus> {(x,y). x=k}) Un {(k,v)}"
    */
    {
        return update1(k,v,t);
    }

    private static FuncTree update1(int k, Object v, FuncTree t)
    /*: requires "v ~= null & theinvs"
        ensures "result..content = (t..content \<setminus> {(x,y). x=k}) Un {(k,v)} & theinvs"
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
                new_left = update1(k, v, t.left);
                new_right = t.right;
                new_key = t.key;
                new_data = t.data;
	    } else if (t.key < k) {
                new_left = t.left;
                new_right = update1(k, v, t.right);
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
    /*: ensures "(result ~= null & (k, result) : t..content) | 
                 (result = null & (ALL v. (k,v) ~: t..content))" */
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

    public static Object lookup1(int k, FuncTree t)
    /*: ensures "(result ~= null --> (k, result) : t..content) &
                 (result = null --> (ALL v. (k,v) ~: t..content))" */
    {
	if (t == null)
	    return null;
	else 
	    if (k == t.key)
		return t.data;
	    else if (k < t.key) 
		return lookup1(k, t.left);
       	    else 
		return lookup1(k, t.right);
    }

    public static Pair max(FuncTree t)
	/*: requires "t..content ~= {}"
	    ensures "result ~= null
	    & result..Pair.data ~= null
	    & ((result..Pair.key, result..Pair.data) : t..content) 
	    & (ALL k. (k ~= result..Pair.key --> (ALL v. ((k,v) : t..content --> k < result..Pair.key))))"
	*/
    {
        return max1(t);
    }

    private static Pair max1(FuncTree t)
	/*: requires "theinvs & t..content ~= {}"
	    ensures "theinvs & result ~= null
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
	    return max1(t.right);
    }

    public static FuncTree remove_max(FuncTree t, int k, Object v)
	/*: requires "(k,v) : t..content & (ALL x.(x ~= k --> (ALL y. ((x,y) : t..content --> x < k))))"
	    ensures "result ~= t
	    & result..content = t..content - {(k,v)} 
	    & (ALL x. (ALL y. ((x,y) : result..content --> x < k)))"
	*/
    {
        return remove_max1(t, k, v);
    }

    private static FuncTree remove_max1(FuncTree t, int k, Object v)
	/*: requires "(k,v) : t..content & 
                      (ALL x.(x ~= k --> (ALL y. ((x,y) : t..content --> x < k)))) &
                      theinvs"
	    ensures "result ~= t
	    & result..content = t..content - {(k,v)} 
	    & (ALL x. (ALL y. ((x,y) : result..content --> x < k)))
            & theinvs"
	*/
    {
	if (t.right == null) 
	   {
	       return t.left;
	   }
	else
	    {
		FuncTree new_right = remove_max1(t.right, k, v);

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
	return remove1(k, t);
    }

    private static FuncTree remove1(int k, FuncTree t)
	/*: 
	  requires "theinvs"
	  ensures "result..content = t..content - {(x,y). x=k} & theinvs" */
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
			Pair m = max1(t.left);
		       
			FuncTree new_left = remove_max1(t.left, m.key, m.data);
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
			new_left = remove1(k, t.left);
			new_right = t.right;
		}
		else {
			new_left = t.left;
			new_right = remove1(k, t.right);
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
	return min1(t);
    }

  private static Pair min1(FuncTree t)
	/*: requires "t..content ~= {} & theinvs"
	    ensures "((result..Pair.key, result..Pair.data) : t..content) 
	           & (ALL k. (ALL v. ((k,v) : t..content --> k >= result..Pair.key))) & theinvs"
	*/
    {
	Pair r = new Pair();
	
	if (t.left == null) {
	    r.key = t.key;
	    r.data = t.data;
	    return r;
	}
	else
	    return min1(t.left);
    }

    public static boolean is_empty(FuncTree t)
    /*: ensures "result = (t..content = {})";
    */
    {
        return (t==null);
    }

    /*    public static void main(String args[])
    {
	FuncTree ft = empty_set();
	Object t = new Object();

	FuncTree ft2 = add(0, t, ft);
	FuncTree ft3 = remove(1, ft2);
    }
    */
}
