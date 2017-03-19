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
	ensures "comment ''del_post'' first = null --> (content = old content & result = null) & 
				      first ~= null --> 
				      (result : old content & (content = old content - {result}))"
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
