/*
  Global doubly-linked list.

PLUS:
  getFirst, getLast, getLost, removeFirst, removeLast, addFirst, addLast,
  contains, size, add, remove, clear, get, set, addAt, removeAt,
  indexOf, isEmpty
  
MINUS:
  global
  no indirection (but that's still useful)
 */

class Node {
    public /*: claimedby DLL */ Node next;
    public /*: claimedby DLL */ Node prev;
    public Object data;
}
class DLL {
    private static Node root;
    private static int size;
   
    /*: public static specvar content :: objset;
        private vardefs "content == 
         {x. rtrancl_pt (% x y. Node.next x = y) root x & x ~= null}";

	public static specvar lsize :: int;
	private vardefs "lsize == size";
   
	invariant TreeInv: "tree [Node.next]";
   
	invariant "root = null | (ALL n. n..Node.next ~= root)";
	
	invariant "ALL x y. x ~= null & y ~= null & x..Node.next = y --> 
                   y : content";
		   
	invariant "ALL x y. Node.prev x = y --> 
	           (x ~= null & (EX z. Node.next z = x) --> 
		    Node.next y = x) &
		    (((ALL z. Node.next z ~= x) | x = null) --> 
		     y = null)";
   */   

    public static Node getFirst()
    /*: requires "content ~= {}"
        ensures  "result : content"
     */
    {
	return root;
    }

    public static Node getLast()
    /*: requires "content ~= {}"
        ensures "result : content"
     */
    {
	Node r = root;
	while /*: inv "r : content"
	       */
	    (r.next != null)
	{
	    r = r.next;
	}
	return r;
    }

    public static Node removeFirst()
    /*: requires "content ~= {}"
        modifies content, lsize
        ensures "content = old content - {result} & lsize = old lsize - 1"
    */
    {
	return removeFirst_int();
    }

    private static Node removeFirst_int()
    /*: requires "content ~= {} & theinvs"
        modifies content, lsize
        ensures "content = old content - {result} & lsize = old lsize - 1 &
	         theinvs"
    */
    {
	Node n = root;
	root = root.next;
	if (root != null)
	    root.prev = null;
	n.next = null;
	n.prev = null;
	size = size - 1;
	return n;
    }

    public static Node removeLast()
    /*: requires "content ~= {}"
        modifies content, lsize
	ensures "content = old content - {result} & lsize = old lsize - 1"
     */
    {
	Node r = root;
	while /*: inv "r : content"
	       */
	    (r.next != null)
	{
	    r = r.next;
	}
	if (r == root)
	    root = null;
	else
	    r.prev.next = null;
	r.prev = null;
	size = size - 1;
	return r;
    }

    public static void addFirst(Node n)
    /*: requires "n ~: content & n ~= null"
        modifies content, lsize
	ensures "content = old content Un {n} & lsize = old lsize + 1"
     */
    {
	n.next = root;
	if (root != null)
	    root.prev = n;
	root = n;
	size = size + 1;
    }

    public static void addLast(Node p)
    /*: requires "p ~: content & p ~= null"
        modifies content, lsize
	ensures "content = old content Un {p} & lsize = old lsize + 1";
    */
    {
	if (root == null)
	{
	    root = p;
	    p.next = null; 
	    p.prev = null;
	    size = size + 1;
	    return;
	}

	Node r = root;
	while /*: inv "r : content" */
	    (r.next != null)
        {
	    r = r.next;
	}
	r.next = p; 
	p.prev = r;
	p.next = null; 
	size = size + 1;

    }

    public boolean contains(Node n)
    /*: requires "n ~= null"
        ensures "result = (n : content)"
     */
    {
	/*: private static ghost specvar tocheck :: objset;
	 */
	Node r = root;

	//: tocheck := "content";
	while /*: inv "(r = null | r : content) & n ~: content - tocheck &
		       tocheck = 
		       {x. rtrancl_pt (% x y. Node.next x = y) r x & 
		       x ~= null}"
	       */
	    (r != null)
        {
	    if (r == n) return true;
	    //: tocheck := "tocheck - {r}";
	    r = r.next;
	}
	return false;
    }

    public static int size()
    /*: ensures "result = lsize"
     */
    {
	return size;
    }

    public static boolean add(Node n)
    /*: requires "n ~: content & n ~= null"
        modifies content, lsize
        ensures  "result & content = old content Un {n} & 
	          lsize = (old lsize) + 1"
     */
    {
	n.next = root;
	if (root != null)
	    root.prev = n;
	root = n;
	size = size + 1;
	return true;
    }

    public static void remove(Node n)
    /*: requires "n : content"
        modifies content, lsize
        ensures "comment ''elementRemoved'' ((content = old content - {n}) & 
	         (lsize = old lsize - 1))"
    */
    {
	remove_int(n);
    }

    private static void remove_int(Node n)
    /*: requires "n : content & theinvs"
        modifies content, lsize
        ensures "comment ''elementRemoved'' ((content = old content - {n}) & 
	         (lsize = old lsize - 1)) & theinvs"
    */
    {
	if (n==root) {
	    root = root.next;
	} else {
	    n.prev.next = n.next;
	}
	if (n.next != null) {
	    n.next.prev = n.prev;
	}
	n.next = null;
	n.prev = null;
	size = size - 1;
    }

    public static void clear()
     /*: modifies content, lsize
         ensures "content = {} & lsize = 0" */
    {
	while /*: inv "theinvs" */
	    (root != null)
        {
	    removeFirst_int();
	}
	size = 0;
    }
    
    public static Node get(int index)
    /*: requires "0 <= index & index < lsize & content ~= {}"
        ensures "result : content | result = null"
     */
    {
	Node r = root;
	int i = 0;
	
	while /*: inv "(r = null | r : content)"
	       */
	    (i < index && r != null)
	{
	    r = r.next;
	    i = i + 1;
	}
	return r;
    }
    
    /* This procedure takes a very long time in mona slicing.
     */
    public static Node set(int index, Node n) 
    /*: requires "0 <= index & index < lsize & 
                  content ~= {} & n ~: content & n ~= null"
	modifies content
	ensures "result = null | content = old content - {result} Un {n}"
     */
    {
	Node r = root;
	int i = 0;
	
	while /*: inv "r = null | r : content"
	       */
	    (i < index && r != null)
	{
	    r = r.next;
	    i = i + 1;
	}

	if (r == null) return null;
	n.next = r.next;
        if (r.next != null) {
            r.next.prev = n;
        }

        n.prev = r.prev;
        if (r == root) {
            root = n;
        } else {
            r.prev.next = n;
        }
        r.next = null;
	r.prev = null;
	return r;
    }

    public static void addAt(int index, Node n)
    /*: requires "0 <= index & index <= lsize & n ~: content & n ~= null"
        modifies content, lsize
	ensures "content = old content Un {n} & lsize = old lsize + 1"
     */
    {
	Node r = root;
	Node p = null;
	int i = 0;

	while /*: inv "(r = null | r : content) & 
		       (r ~= root --> p ~= null) &
		       (p ~= null --> (p : content & p..Node.next = r))"
	      */
	    (i < index && r != null) {
	    p = r;
	    r = r.next;
	    i = i + 1;
	}
	
	n.next = r;
	n.prev = p;
	if (r == root) {
	    root = n;
	} else {
	    p.next = n;
	}

	if (r != null) {
	    r.prev = n;
	}

	size = size + 1;
    }

    public static Node removeAt(int index)
    /*: requires "0 <= index & index < lsize & content ~= {}"
        modifies content, lsize
	ensures "(result = null --> 
	          (content = old content & lsize = old lsize)) &
		 (result ~= null -->
		  (content = old content - {result} & lsize = old lsize - 1))"
     */
    {
	Node r = root;
	int i = 0;
	
	while /*: inv "r = null | r : content"
	       */
	    (i < index && r != null)
	{
	    r = r.next;
	    i = i + 1;
	}

	if (r == null) return null;
	remove_int(r);
	return r;
    }

    public static int indexOf(Node n)
    /*: ensures "((result = -1) --> (n ~: content)) &
                 ((result ~= -1) --> (n : content))"
     */
    {
	/*: private static ghost specvar tocheck :: objset;
	 */
	Node r = root;
	int i = 0;
	//: tocheck := "content";
	while /*: inv "0 <= i &
		       (r = null | r : content) & n ~: content - tocheck &
		       tocheck =
		       {x. rtrancl_pt (% x y. Node.next x = y) r x &
		        x ~= null}"
	       */
	    (r != null)
	{
	    if (r == n) return i;
	    //: tocheck := "tocheck - {r}";
	    r = r.next;
	    i = i + 1;
	}
	return -1;
    }

    public static boolean isEmpty()
    /*: ensures "result = (content = {})"
     */
    {
	return root == null;
    }
	
    /* Soundness test case: Insufficient loop invariant. */
    public static void clearShouldNotVerify()
    /*: modifies content, lsize
        ensures "content = {} & lsize = 0"
     */
    {
	while /*: inv "True"
	       */
	    (root != null)
        {
	    removeFirst();
	}
	size = 0;
    }

    public static void driver()
    /*: requires "content = {}"
        ensures "True";
    */
    {
	int i = 0;
	int m = 11;
	Node[] saved = new Node[m];
	boolean b;

	while (i < m) {
	    Node n = new Node();
	    addLast(n);
	    b = isEmpty();
	    //: assert "~b";
	    saved[i] = n;
	    i = i + 1;
	}
        saved[1] = new Node();
        set(1, saved[1]);
	i = 0;
	while (i < m) {
	    remove(saved[i]);
	    i = i + 1;
	}
	b = isEmpty();
	//: assert "b";
    }
}
