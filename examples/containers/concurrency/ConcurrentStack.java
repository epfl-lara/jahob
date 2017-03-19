/*
  Concurrent stack using Treiber's algorithm.
  
  . Don't worry about ABA problem.
 */

public class Node {
	public Object item;
	public Node next;

	Node(Object i) {
		item = i;
		next = null;
	}
}

/*
  Assuming this class provide compareAndSet for Node references
 */
class AtomicNodeRef {
	Node ptr;
	
	AtomicNodeRef(Node node) {
		ptr = node;
	}

	/* synchronized */ // Not really, compareAndSet is meant to be non-blocking.
	boolean compareAndSet(Node a, Node b) {
		if (ptr == a) {
			ptr = b;
			return true;
		}
		return false;
	}

	Node get() { return ptr; }
}

public class ConcurrentStack {

	AtomicNodeRef top;

	ConcurrentStack() {
		top = new AtomicNodeRef(null);
	}

	public void push(Object item) {
		Node old_top;
		Node new_top;

		new_top = new Node(item);
		while /*: inv "True" */ (true) {
			old_top = top.get();
			new_top.next = old_top;
			if (!top.compareAndSet(old_top, new_top)) return;
		}
	}

	public Object pop() {
		Node old_top, new_top;

		while /*: inv "True" */ (true) {
			old_top = top.get();
			if (old_top == null) return null;
			new_top = old_top.next;
			if (!top.compareAndSet(old_top, new_top)) 
				return old_top.item;
		}
	}
}
