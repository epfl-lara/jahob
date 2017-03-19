class Node {
    public /*: claimedby DLL */ Node next;
    public /*: claimedby DLL */ Node prev;
}
class DLL
{
   private static Node root;
   
   /*: public static specvar content :: objset;
       private vardefs "content == 
        {x. (root,x) : {(u,v). next u = v}^*  & x ~= null}";
   
       invariant tree: "tree [next]";
   
       invariant rootFirst: "root = null | (ALL n. n..next ~= root)";
   
       invariant noNextOutside: "ALL x y. x ~= null & y ~= null & x..next = y --> y : content";

       invariant prevDef: "ALL x y. prev x = y --> 
                      (x ~= null & (EX z. next z = x) --> next y = x) &
                      (((ALL z. next z ~= x) | x = null) --> y = null)";
//       invariant prevDef0: "ALL x y. prev x = y --> (x ~= null --> next y = x)";  // contradictory

   */   

   public static void addLast(Node n)
      /*: 
	requires "n ~: content & n ~= null"
	modifies content
	ensures "content = old content Un {n}";
      */
   {
      if (root == null) {
        root = n;
        n.next = null; 
        n.prev = null;
        return;
      }

      Node r = root;
      while (r.next != null) {
	 r = r.next;
      }
      r.next = n; 
      // PREVSET:
      n.prev = r;
   }

   public static boolean isEmpty()
   {
       return root == null;
   }
	

   public static void remove(Node n)
      /*: requires "n : content"
        modifies content
        ensures "comment ''elementRemoved'' (content = old content - {n})"
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
   }

   public static void removeBroken(Node n)
      /*: requires "n : content & n ~= null"
        modifies content
        ensures "True";
      */
   {
       /*: noteThat invsImply: "ALL y. y ~= null & y ~: content --> 
                                       Node.prev y = null"; */
       //: assume "n ~= root";
       //: assume "root ~= null";
       Node np = n.prev;
       Node nn = n.next;
       //: assert aha: "Node.next np = n";
       //: assert ofCourse: "Node.next n = nn";
       //: assume "np ~= null";
       //: assume "nn = null";
       //: assert list1: "np ~= n & nn ~= n";
       np.next = nn;
       //: assert shrinks: "content \<subseteq> old content";
       //: assert "tree[Node.next]";
       //: noteThat "ALL x. Node.next x ~= n";
       //: assert notin: "n ~: content"; // THIS FAILS
       //: assume "False";
   }

    private static void mystery(Node n) // this one works
      /*: 
        ensures "True";
      */
    {
        //: assume "tree [Node.next]";
        //: assume "ALL x. Node.next x ~= n";
        //: assume "n ~= root";
        //: assert "n ~: content";
        //: assume "False";
    }

    public static void testDriver()
	/*: requires "True"
	    modifies content
	    ensures "True"
	 */
    {
	// These lines detect: wrong prev invariant (prevDef0), prev field not set (PREVSET)
	Node n1 = new Node();
	addLast(n1);
	Node n2 = new Node();
	addLast(n2);
    }

    public static void biggerDriver(Object x)
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
	// n.next = n;
	i = m-1;
	while (i >= 0) {
	    remove(saved[i]);
	    i = i - 1;
	}
	b = isEmpty();
	//: assert "b";
    }
}
