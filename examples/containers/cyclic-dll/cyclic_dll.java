/* Software Analysis and Verification project
 *
 * cyclic_dll.java
 * Created on June 29, 2007,
 *
 * Authors: Feride Cetin and Kremena Diatchka
 * 
 * Description:
 * A cyclic doubly linked list with a header node.
 * Each node has a next and a prev field pointing to the object following it
 * and the object preceding it in the cyclic list. New nodes are inserted at
 * the beginning of the list. 
 *
 */

class Node {
    public /*: claimedby List */ Node next;
    public /*: claimedby List */ Node prev;
}

// Cyclic list with a header node
class List
{
   public static Node first; 
  
   /*:
     private static ghost specvar next1 :: "obj => obj"; 
     public invariant next1field: "ALL n. n ~: Object.alloc --> isolated n";

     public static specvar content :: objset;
     vardefs "content == {x. x ~= null & (first..next1,x) : {(v,w). v..next1=w}^*}";

     public static specvar isolated :: "obj => bool";
     vardefs "isolated == (%n. n..next1 = null & (ALL x. x ~= null --> x..next1 ~= n))";

     private static specvar last :: "obj => bool";
     private vardefs "last == (% x. (first,x) : {(v,w). v..next1=w}^* & x ~=null & x..next1 = null)";

     invariant firstIsolated: "first ~= null --> (ALL n. n..next1 ~= first)";
     
     invariant isTree: "tree [next1]";

     invariant prevFC: "ALL x y. Node.prev x = y --> (x ~= null -->  ((x = first --> last y) & ( Node.next y = x)))";

     invariant fieldConstraint: "ALL x y. Node.next x = y --> 
         ((last x --> y = first) & (~ last x --> y = x..next1))";

     invariant contentCheck : "ALL x. x..Node.next = x..next1 --> x..Node.next : content";
   */

    // initialization of a list with a header node pointing to itself
    public static void init() 
    /*: requires "first = null"
        modifies content, isolated, first
        ensures "comment ''init_post'' content = {} & first ~= null"
     */
    {
        first = new Node();
        first.next = first;
        first.prev = first;
    }

    public static void add(Node n)
    /*: requires "comment ''add_pre'' (first ~= null & n ~: content & n ~= null & n ~= first & isolated n)"
        modifies content, isolated
        ensures "comment ''add_post'' (content = old content Un {n})"
    */
    {
  	n.next = first.next;
      //: "n..next1" := "first..next1";
        n.prev = first;
        first.next.prev = n;
        first.next = n;
        //: "first..next1" := "n";
	
    }

 public static boolean member(Node n)
    /*: requires "comment ''mem_pre'' first ~= null & n ~= null"
        ensures "comment ''mem_post'' result = (first ~= first..Node.next & n : content)"
     */
    {	
	Node tmp = first.next;
	
	if (tmp==first) { 
	    return false; 
	} else {
		
	    //: ghost specvar seen :: objset = "{}"
	    while /*:  inv "
		    comment ''A'' (tmp = first | tmp : content) &
		    comment ''B1'' (tmp : content --> seen = {} | seen = {x. x : content & (tmp,x) ~: {(u,v). u..next1 = v}^*}) &
		    comment ''B2'' (tmp = first --> seen = content) &
		    comment ''C'' (ALL x. x : seen --> x != n)" */
		(tmp != first) {
		if(tmp == n) {
		    return true;
		}
		//: seen := "seen Un {tmp}"
		
		tmp = tmp.next;
	    }
	    //: noteThat seenAll: "seen = content";
	    return false;
	}
    }


}
