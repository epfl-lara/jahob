/* Software Analysis and Verification project
 *
 * List.java
 * Created on June 29, 2007,
 *
 * Authors: Feride Cetin and Kremena Diatchka
 * 
 * Description:
 * Acyclic singly linked list with a header node.
 * Each node has a next field pointing to the object following it in 
 * the list. New nodes are inserted at the beginning of the list. 
 *
 */

class Node {
    public /*: claimedby List */ Node next;
}

// Acyclic list with header
class List
{
    public /*: readonly */ static Node first; 
  
   /*:
     public static specvar content :: objset;
     vardefs "content == {x. x ~= null & (first..Node.next,x) : {(v,w). v..Node.next=w}^*}";

     public static specvar pointed :: "obj => bool";
     public vardefs "pointed == (%n. EX x. x ~= null  & x..Node.next = n)";

     invariant firstUnaliased: "first ~= null --> ~ pointed first";
     
     invariant isTree: "tree [Node.next]";
   */

    // initialization of a list with a header node
    public static void init() 

    /*: requires "first = null"
        modifies first
        ensures "comment ''init_post''  first ~= null &  (content = {})"
     */
    {
    	first = new Node();
    }

    public static void add(Node n)
    /*: requires "comment ''add_pre'' first ~= null & n ~= first & n ~: content 
				      & n ~= null & n..Node.next = null & ~ pointed n"
        modifies content, pointed
        ensures "comment ''add_post'' (content = old content Un {n})"
    */
    {	
	n.next = first.next;
	first.next = n;
    }

    public static boolean member(Node n)
    /*: requires "comment ''mem_pre'' n ~= first & first ~= null"
        ensures "comment ''mem_post'' result = (n : content)"
     */
    {	
	Node tmp = first.next;
	
	//: ghost specvar seen :: objset = "{}"
        while /*:  inv " (tmp = null | tmp : content) & 
		         (seen = {x. x : content & (tmp,x) ~: {(u,v). u..Node.next = v }^*}) &
			  (ALL x. x : seen --> x != n)" */
			  
           (tmp != null) {
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
