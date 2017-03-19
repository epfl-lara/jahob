class Node {
    public /*: claimedby DLLSet */ Object     data;
    public /*: claimedby DLLSet */ Node next;
    public /*: claimedby DLLSet */ Node prev;
}
class DLLSet {
    
    /*: private specvar nodes :: objset;
	public specvar content :: objset;

        private vardefs "nodes ==
	  {x. x ~= null & rtrancl_pt (% x y. x..Node.next = y) root x}";

	private vardefs "content ==
	  {z. EX x. x : nodes & Node.data x = z}"

	invariant TreeInv: "tree [Node.next]"

	invariant DataNonNullInv:
	  "ALL x. x : nodes --> x..Node.data ~= null"

	invariant PrevNextInv:
	  "ALL x1 x2. x1..Node.prev = x2 -->
	           ((x2 ~= null --> x2..Node.next = x1) &
                   (x2 = null --> x1 ~= null --> 
		   (ALL x3. x3..Node.next ~= x1)))"

	invariant InjInv:
	  "ALL x1 x2. x1 : nodes & x2 : nodes & 
	    x1..Node.data = x2..Node.data --> x1 = x2"
    */

    /*  
	Says that all nodes outside of this list have null
	fields. (Not true.)
      
      	invariant ExtNodeInv:
	  "this ~= null -->
	    (ALL x. ((x ~: nodes) --> 
	      (x..Node.next = null &
	       x..Node.prev = null &
	       x..Node.data = null)))"

     */
    private Node root = null;

    public static void main (String args[])
    /*: ensures "True"
     */
    {
	driver();
    }

    public void add (Object o1)
    /*: requires "o1 ~= null & o1 ~: content"
        modifies content
	ensures "content = old content Un {o1}"
    */
    {
	Node n = new Node();
	n.data = o1;

	if (root == null) {
	    root = n;
	} else {
	    //	    root.prev = n;
	    n.next = root;
	    root = n;
	}
	//: noteThat NewNodes: "nodes = old nodes Un {n}";
    }
    
    public boolean contains (Object o)
    /*: ensures "result = (o : content)"
     */
    {
	/*:
	  private specvar to_visit_nodes :: objset;
	  private specvar to_visit_content :: objset;

	  private vardefs "to_visit_nodes == 
	  {x. x ~= null & rtrancl_pt (% x y. x..Node.next = y) curr x}"

	  private vardefs "to_visit_content == 
	  {z. EX x. x : to_visit_nodes & Node.data x = z}"
	*/

	Node curr = root;
	
	while /*: inv "o ~: content - to_visit_content" */
	    (curr != null) {
	    if (curr.data == o)
		return true;
	    curr = curr.next;
	}
	return false;
    }

    public void remove (Object o)
    /*: modifies content
        ensures "content = old content - {o}"
     */
    {
	Node curr = root;

	while (curr != null) {
	    if (curr.data == o) {
		if (curr == root) {
		    root = curr.next;
		} else {
		    curr.prev.next = curr.next;
		}
		if (curr.next != null) {
		    curr.next.prev = curr.prev;
		}
		curr.next = null;
		curr.prev = null;
		curr.data = null;
		return;
	    }
	    curr = curr.next;
	}
    }

    public boolean isEmpty ()
    /*: ensures "result = (content = {})"
     */
    {
	//: noteThat "(root = null) = (nodes = {})";
	return root == null;
    }

    public static void driver0(Object x)
    /*: modifies content
        ensures "True"
     */
    {
	/* Not detected because treeness is not checked:
	Node n = new Node();
	n.next = n;
	n.prev = n;
	*/
    }

    public static void driver()
    /*: modifies content
        ensures "True"
     */
    {
	boolean b = false;
	Object o1 = new Object();
	Object o2 = new Object();
	Object o3 = new Object();
	Object o4 = new Object();

	DLLSet s = new DLLSet();
	b = !(s.contains(o1)) && !(s.contains(o2)) && 
	    !(s.contains(o3)) && !(s.contains(o4)) && s.isEmpty();
	//: assert "b";

	s.add(o1);
	b = s.contains(o1) && !(s.contains(o2)) && 
	    !(s.contains(o3)) && !(s.contains(o4)) && !(s.isEmpty());
	//: assert "b";

	s.add(o2);
	b = s.contains(o1) && s.contains(o2) && 
	    !(s.contains(o3)) && !(s.contains(o4)) && !(s.isEmpty());
	//: assert "b";

	s.add(o3);
	b = s.contains(o1) && s.contains(o2) && 
	    s.contains(o3) && !(s.contains(o4)) && !(s.isEmpty());
	//: assert "b";

	s.add(o4);
	b = s.contains(o1) && s.contains(o2) && 
	    s.contains(o3) && s.contains(o4) && !(s.isEmpty());
	//: assert "b";

	/* remove a middle node */
	s.remove(o2);
	b = s.contains(o1) && !(s.contains(o2)) && 
	    s.contains(o3) && s.contains(o4) && !(s.isEmpty());
	//: assert "b";
	
	/* remove the last node */
	s.remove(o1);
	b = !(s.contains(o1)) && !(s.contains(o2)) && 
	    s.contains(o3) && s.contains(o4) && !(s.isEmpty());
	//: assert "b";

	/* remove the first node */
	s.remove(o4);
	b = !(s.contains(o1)) && !(s.contains(o2)) && 
	    s.contains(o3) && !(s.contains(o4)) && !(s.isEmpty());
	//: assert "b";
	
	//	s.add(o3); /* this statement should fail */
    }
}
