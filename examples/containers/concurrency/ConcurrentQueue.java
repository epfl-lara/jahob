/*
  Michael-Scott concurrent queue
 */

/*
  Assuming this class provide atomic compareAndSet for Node references
 */
public /*: claimedby ConcurrentQueue */ class AtomicNode {
	public Object item;
	public AtomicNode next;

    /*: 
      public ghost specvar con :: objset = "{} :: objset";

      public ensured invariant ConAlloc: "con \<subseteq> Object.alloc";

      public invariant ConNull: "this = null --> con = {}";
      public invariant ConDef: "this ~= null --> 
         con = {this..item} Un next..con & 
         item ~: next..con";
	*/

	/*
	  public ghost specvar snext :: objset = "{} :: objset";
	  public invariant SNextNull: "this..next = null --> snext = {}";
	  public invariant SNextDef: "this..next ~= null --> snext = {this..next}";

	  public ghost specvar snext1 :: obj;
	  public invariant SNext1 : "this..snext1 = this..next";
    */

    //	AtomicNode()
	/*
	  modifies con
	  ensures "con = {}";
	 */
    /*
	{
		item = null;
		next = null;
	}
    */
	
	static AtomicNode test(Object item)
	/*:
	  requires "item ~= null"
	  ensures "result..con = {item}";
	 */
	{
		AtomicNode tmp = new AtomicNode();
		tmp.item = item;
		tmp.next = null;
		//: "tmp..AtomicNode.con" := "{item}";
		return tmp;
	}


	static AtomicNode atomicNode2(Object item, AtomicNode ptr) 
	/*:
	  requires "item ~: ptr..con"
	  ensures "result..AtomicNode.con = {item} Un ptr..con";
	 */
	{
		AtomicNode tmp = new AtomicNode();
		tmp.item = item;
		tmp.next = ptr;
		return tmp;
	}

	static AtomicNode atomicNode1(AtomicNode ptr) 
	/*:
	  requires "item ~: ptr..con"
	  ensures "True";
	*/
	/*
	  ensures "result..con == {this..item} Un ptr..AtomicNode.con";
	*/
	{
		AtomicNode tmp = new AtomicNode();
		tmp.next = ptr;
		return tmp;
	}

	/* synchronized */ // Not really, compareAndSet is meant to be non-blocking.
	/* atomic */
	boolean compareAndSet(AtomicNode a, AtomicNode b) 
	/*:
	  requires "True"
	  modifies "this..AtomicNode.next"
	  ensures "(result = True & this..AtomicNode.next = b & old this..AtomicNode.next = a)
	         | (result = False & this..AtomicNode.next = old this..AtomicNode.next & old this..AtomicNode.next ~= a)";
	 */
	{
		// atomic {
		if (next == a) {
			next = b;
			return true;
		}
		else {
			return false;
		}
		// }
	}

	void test2(AtomicNode a)
	/*:
	  requires "a ~= null"
	  modifies "this..AtomicNode.next"
	  ensures "this..AtomicNode.next = a";
	 */
	{
		this.next = a;
	}

	AtomicNode get() { return next; }
}

public class ConcurrentQueue {
	AtomicNode dummy;
	AtomicNode head;
	AtomicNode tail;
	// note that tail itself doesn't change. tail.next is the real "tail" of the queue. Similarly for head

	/*:
	  public specvar content :: objset;
	  vardefs "content == head..AtomicNode.next..AtomicNode.con"; // head points to dummy node

	  // public ensured invariant ("ContentAlloc") "content \<subseteq> Object.alloc";
	  // invariant "head ~= null & tail ~= null & dummy ~= null";
	*/

	ConcurrentQueue() 
	/*:
	  ensures "content = {}";
	*/
	{
		dummy = AtomicNode.atomicNode2(null, null);
		head = AtomicNode.atomicNode1(dummy);
		tail = AtomicNode.atomicNode1(dummy); 
		// tail = dummy; this should cause a null pointer dereference check at cur_tail.next, but Jahob misses the error
	}
	
	void enq(Object item)
	/*: 
	  modifies content
	  ensures "item : content";
	*/
	// some items might have been removed. But upon returning,
	// can we really assert this? What if some process does
	// deq between the last compareAndSet and "return"?
	// anyway just do it the sequential way now.
	// At least we should be able to show that item in content.
	{
		AtomicNode new_node = AtomicNode.atomicNode2(item, null);

		AtomicNode cur_tail = tail.next;
		
		while /*: 
				inv "item = new_node..item
				& cur_tail ~= null & cur_tail..content \<subset> this..content"
			  */
			(true) {
			cur_tail = tail.next;
			AtomicNode tail_next = cur_tail.next;

			if (cur_tail == tail.next) { // no one has performed and insertion
				if (tail_next != null) { // someone is in the middle of enqueueing
					tail.compareAndSet(cur_tail, tail_next); // move the tail pointer for him
				}
				else {
					AtomicNode tmp = cur_tail.next;
					if (tmp.compareAndSet(null, new_node)) { // if cur_tail.next is used instead of tmp, Jahob complains
						if (tail.compareAndSet(cur_tail, new_node)) // set tail.next to new_node
							return;
					}
				}
			}
		}
	}
}
