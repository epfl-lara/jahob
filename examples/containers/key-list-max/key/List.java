public class List {
    private Node head;

    public int max() {
	if ( head == null ) return 0;
	Node t = head;
	int max = t.val;
	while ( t.next != null ) {
	    t = t.next;
	    if ( t.val > max ) max = t.val;
	}
	return max;
    }
}

class Node {
    public Node next;
    public int val;    
}
