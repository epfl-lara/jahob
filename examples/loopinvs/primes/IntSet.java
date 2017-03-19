class ISNode {
    public /*: claimedby IntSet */ ISNode next;
    public /*: claimedby IntSet */ int val;

    /*: public ghost specvar ncon :: "int set";
     */
}

class IntSet {
    private ISNode root;

    /*: public specvar content :: "int set";
        private vardefs "content == root..ISNode.ncon";
	
	invariant NconNull: "null..ISNode.ncon = {}";
	
    */

    public void addAlt(int i) {
	if (root == null || i < root.val) {
	    ISNode n = new ISNode();
	    n.val = i;
	    n.next = root;
	    root = n;
	    return;
	} else if (i == root.val) {
	    return;
	}
	
	addRec(i, root);
    }

    private void addRec(int i, ISNode prev) {
	ISNode curr = prev.next;
	if (curr == null || i < curr.val) {
	    ISNode n = new ISNode();
	    n.val = i;
	    n.next = curr;
	    prev.next = n;
	    return;
	} else if (i == curr.val) {
	    return; // already in set
	}
	
	addRec(i, curr);
    }

    public void add(int i)
	/*: modifies content
	    ensures  "content = (old content) Un {i}"
	*/
    {
	ISNode prev = null;
	ISNode curr = root;

	while /*: inv "True";
	       */
	    (curr != null && curr.val < i) {

	    //: "prev..ISNode.ncon" := "prev..ISNode.ncon Un {i}";
	    prev = curr;
	    curr = curr.next;
	}

	if (curr != null && curr.val == i) {
	    //System.out.println(i + " already in set.");
	    return; // already in set
	}
	//: assume "False";

	ISNode n = new ISNode();
	n.val = i;

	n.next = curr;
	if (prev == null) {
	    root = n;
	} else {
	    prev.next = n;
	}
	//System.out.println("Added " + i + " to set.");
    }

    public boolean isEmpty() {
	return (root == null);
    }
    
    public int extractOne() {
	return removeMin();
    }

    public int removeMin()
    {
	ISNode n = root;
	root = root.next;
	n.next = null;
	return n.val;
    }

    public void remove(int i) {
	ISNode curr = root;
	ISNode prev = null;

	while(curr != null && curr.val != i) {
	    prev = curr;
	    curr = curr.next;
	}

	if (curr == null) {
	    return; // not found
	}

	// curr.val == i
	if (prev == null) {
	    root = curr.next;
	    curr.next = null;
	} else {
	    prev.next = curr.next;
	    curr.next = null;
	}
    }
}

