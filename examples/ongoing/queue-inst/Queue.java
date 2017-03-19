/* Software Analysis and Verification project
 *
 * Queue.java
 * Created on June 29, 2007,
 *
 * Authors: Feride Cetin and Kremena Diatchka
 * 
 * Description:
 * Instantiable queue with a header node.
 *
 */


class Node {
    public /*: claimedby List */ Node next;
}
	
// Queue with header
class Queue
{
    public /* readonly*/  Node first; 
    private Node last; 
 
   /*:
     public specvar content :: objset;
     vardefs "content == {x. x ~= null & (first..Node.next,x) : {(v,w). v..Node.next=w}^*}";

     public specvar pointed :: "obj => bool";
     public vardefs "pointed == (%n. EX x. x ~= null  & x..Node.next = n)";

     private invariant listEmpty: "(last = null) = (first = null)";

     private invariant firstUnaliased: "first ~= null --> ~ pointed first";

     public invariant contentAlloc: "content \<subseteq> Object.alloc";
	
     invariant isTree: "tree [Queue.first, Node.next]";
   
     private static specvar isLast :: "obj => bool";
     private vardefs "isLast == (% x. (first,x) : {(v,w). v..Node.next=w}^* & x..Node.next=null)";
     private invariant lastIsLast: "last ~= null --> isLast last";
   */

  public Queue() 
  /* requires "comment ''init_pre'' first = null"
     modifies first
     ensures "comment ''init_post''  first ~= null & content = {}"
   */
    {
        first = new Node();
        last = first;
    }


    /* insert node at the back */
    public void enqueue(Node n)
    /*: requires "comment ''add_pre'' n : Object.alloc & first ~= null & n ~: content 
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
    public Node dequeue()

    /*: requires "first ~= null" 
	modifies  content, pointed
	ensures "comment ''del_post'' ((first = null | first..Node.next = null) --> (content = old content & result = null)) & 
				      ((first ~= null & first..Node.next ~= null) --> 
				      (result : old content & (content = old content - {result})))"
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
