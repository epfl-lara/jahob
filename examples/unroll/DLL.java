/* Examples to be checked using bounded model checking. */

class Node {
    Node next, prev;
}

class List {  
    static Node root;

    boolean isDLL() {
	if (root==null) return true;
	if (root.prev!=null) return false;
	Node current = root;
	Node p;
	while (current != null) {
	    p = current;
	    current = current.next;
	    if (current.prev != p) return false;
	}
	return true;
    }

    void insert(Node n) {
	n.next = root;
	n.prev = null;
	root.prev = n;
	root = n;
    }

    void test() {
	if (!isDLL()) return;
	insert(new Node());
	boolean ok = isDLL();
	//: assert "ok"
    }

    private void brokenInsertion() 
    /*:
      requires "True"
      modifies root, prev, next
      ensures "True"
     */
    {
	boolean preOk = true;
	if (root!=null) {
	    if (root.prev!=null) {
		preOk = false;
	    } else {
		Node current = root;
		Node p = null;
		while (preOk && (current != null)) {
		    if (current.prev != p) {
			preOk = false;
		    } else {
			p = current;
			current = current.next;
		    }
		}
	    }
	}
	if (preOk) {
	    Node nn = new Node();
	    nn.next = root;
	    nn.prev = null;
	    if (root != null) {
		root.prev = nn;
		root = nn;
	    }

	    boolean postOk = true;
	    if (root!=null) {
		if (root.prev!=null) {
		    postOk = false;
		} else {
		    Node current = root;
		    Node p = null;
		    while (postOk && (current != null)) {
			if (current.prev != p) {
			    postOk = false;
			}
			p = current;
			current = current.next;
		    }
		}
	    }
	    //: assert "postOk"
	}
    }
}
