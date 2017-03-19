/* A global queue with a header node, specified as a set.
 *
 * Created on June 29, 2007,
 * by Feride Cetin and Kremena Diatchka
 * in Software Analysis and Verification Class.
 * 

 Viktor Kuncak, November 2007: 
   -the authors assumed wrong priority of &,--> operators
    so postcondition was trivial.  Wrote correct postcondition, now verifies.
   -added getFresh method else there is no way for client to make sure ~pointed n
 */
class Node {
    public /*: claimedby List */ Node next;
}	
// Queue with header node
class List
{
    public /*: readonly */ static Node first; 
    private static Node last; 
   /*:
     public static specvar content :: objset;
     vardefs "content == {x. x ~= null & (first..Node.next,x) : {(v,w). v..Node.next=w}^*}";

     public static specvar pointed :: "obj => bool";
     public vardefs "pointed == (%n. EX x. x ~= null  & x..Node.next = n)";

     invariant firstUnaliased: "first ~= null --> ~ pointed first";
 
     invariant isTree: "tree [Node.next]";
   
     private static specvar isLast :: "obj => bool";
     private vardefs "isLast == (% x. (first,x) : {(v,w). v..Node.next=w}^* & x..Node.next=null)";

     private invariant emptyList: "(first = null) = (last = null)";
     private invariant lastIsLast: "last ~= null --> isLast last";
   */

    // initialization of a queue with a header node
    public static void init() 
    /*: requires "first = null"
        modifies first
        ensures "comment ''init_post''  first ~= null & (content = {})"
     */
    {
    	first = new Node();
	last = first;
    }

    public static Node getFresh()
    /*: ensures "~pointed result"
     */
    {
	return new Node();
    }

    /* insert node at the back */
    public static void enqueue(Node n)
    /*: requires "comment ''add_pre'' first ~= null & n ~= first & n ~: content 
				      & n ~= null & n..Node.next = null & ~ pointed n"
        modifies content, pointed
        ensures "comment ''add_post'' (content = old content Un {n})"
    */
    {
	if (first.next == null) {
		first.next = n;
	}
	else 
		last.next = n;

	last = n;
    }

   /* remove node after header node and return it */
    public static Node dequeue()
    /*: requires "comment ''del_pre'' first ~= null"
	modifies first, content, pointed
	ensures "(old content = {} --> result = null & content = old content) &
	         (old content ~= {} --> 
                   result ~= null & result : old content & 
		   ~pointed result & result..Node.next = null &
		   content = old content \<setminus> {result})"
    */ 
    {
	Node res;
	// list is empty
	if(first == last) {
		return null;
       }
 	// list contains one element
    	else if(first.next == last) {
		last = first;
		res = first.next;
		first.next = null;
 
 	} 
	// list contains more than one element
	else {
		Node tmp = first.next.next;
		first.next.next = null;
		res = first.next;
		first.next = tmp;
	}
	return res;
    }
}
