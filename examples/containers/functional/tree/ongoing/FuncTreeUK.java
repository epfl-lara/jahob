/*
 * FuncTree.java, with unique keys
 *
 * Created on August 2, 2006
 * Functional Trees
 */
public final class FuncTree
{
    private int key;
    private Object data;
    private FuncTree left;
    private FuncTree right;


   /*: 
    public ghost specvar content :: "(int * obj) set" = "({} :: (int * obj) set)";
    public ghost specvar init :: bool = "False";

    invariant ("content definition") "(this ~= null & this..init)--> 
                    ( content = {(key, data)} Un left..content Un right..content)"

    invariant ("null implies empty") "this = null --> content = {}"
//  invariant ("empty implies null") "content = {} --> this = null"

    invariant ("no null data") "this ~= null --> data ~= null"

    invariant ("init means left init")  "init --> left..init"
    invariant ("init means right init") "init --> right..init"
    invariant ("null is init")         "this = null --> init"

    //invariant "{v. (EX k. (k,v) : content)} \<subseteq> Object.alloc"
    invariant ("left children are smaller") "init --> (ALL k. (EX v. ( (k,v) : left..content --> k <= key & k ~= key)))"
    invariant ("right children are bigger") "init --> (ALL k. (EX v. ( (k,v) : right..content --> k > key & k ~= key)))"
    */

   public static FuncTree empty_set() 
   /*: requires "True"
       ensures "result..content = {} & result..init"
    */
   {
      return null;
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
    /*: requires "v ~= null & t..init & (ALL v1. (k,v1) ~: content)"
        ensures "result..content = t..content Un {(k,v)} & result..init"
    */
    {
	FuncTree r = new FuncTree();
	//: "r..init" := "False";

	if (t==null) {
	    r.data = v;
	    r.key = k;
	    r.left = null;
	    r.right = null;
	    //: "r..content" := "{(k,v)}";
	    //: "r..init" := "True";
	    return r;
	}
	else {
            if (k < t.key) {
                r.data = t.data;
                r.key = t.key;
                r.left = add(k, v, t.left);
                r.right = t.right;
            }
            else if (k > t.key) {
                r.data = t.data;
                r.key = t.key;
                r.left = t.left;
                r.right = add(k, v, t.right);
            } else {
                //: noteThat "comment ''otherCase'' (k = t..key)";
                //: assume "False";
            }
            //: "r..init" := "True"
            //: "r..content" := "t..content Un {(k,v)}";
            return r;
        }
    }

    // update : this is going break, because now the invariant are with strict ordering. This makes membership test easier.
    public static FuncTree addNonStrict(int k, Object v, FuncTree t) // note that even this works, because we have <= for keys in the invariant
    /*: requires "v ~= null & t..init"
        ensures "result..content = t..content Un {(k,v)} & result..init"
    */
    {
        FuncTree r = new FuncTree();
        //: "r..init" := "False";

        if (t==null) {
            r.data = v;
            r.key = k;
            r.left = null;
            r.right = null;
            //: "r..content" := "{(k,v)}";
            //: "r..init" := "True";
            return r;
        }
        else {
            if (k < t.key) {
                r.data = t.data;
                r.key = t.key;
                r.left = add(k, v, t.left);
                r.right = t.right;
            }
            else {
                r.data = t.data;
                r.key = t.key;
                r.left = t.left;
                r.right = add(k, v, t.right);
            }
            //: "r..init" := "True"
            //: "r..content" := "t..content Un {(k,v)}";
            return r;
        }
    }



    public static boolean is_nil(FuncTree t)
    /*: ensures "result = (t..FuncTree.content = {})";
    */
    {
        return (t==null);
    }


  

}
