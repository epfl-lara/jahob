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
class Tree
{
    private int key;
    private Object data;
    private Tree left;
    private Tree right;

   /*: 
    public ghost specvar content :: "(int * obj) set" = "({} :: (int * obj) set)";

    invariant contentDefinition: "data ~= null --> content = {(key, data)} Un left..content Un right..content"
    invariant NullDataEmpty1: "data = null --> content = {}"
    invariant NullDataEmpty2: "data = null --> (left = null & right = null)"
   
    invariant ("left children are smaller") "(ALL k. (ALL v. ( (k,v) : left..content --> k < key)))"
    invariant ("right children are bigger") "(ALL k. (ALL v. ( (k,v) : right..content --> k > key)))"

    invariant Test1: "left ~= null --> left ~= this"
    invariant Test2: "right ~= null --> right ~= this"
 
    */

    public Tree()
    /*: modifies content
        ensures "content = {} & Object.alloc = (old Object.alloc)"
    */
    {
	//: assume "this ~: Object.alloc"
	//: content := "{}"
    }
 



    private void add1(int k, Object v)
    /*: requires "v ~= null & (ALL y. (k,y) ~: content) & theinvs"
        ensures "content = (old content) Un {(k,v)} & theinvs"
    */
    {
	if (data==null) {
	    left = new Tree();
	    right = new Tree();
	    data = v;
	    key = k;
	    //:noteThat "right..content = {}"
	    //: assume "False"
	    //: "content" := "{(k,v)}";
	} else {
	    //: assume "False"
	    if (k < key) {
                left.add1(k, v);
	    }
            else {
		right.add1(k, v);
            }
	    //: "content" := "(old content) Un {(k,v)}";
	}
    }
}