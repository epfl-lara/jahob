/* Instantiable queue.
 */

class Node {
    public /*: claimedby Queue */ Object data;
    public /*: claimedby Queue */ Node next;
}
class Cell {
}
class Queue {
   private Node first;
   private Node last;
   /*: 
      private static ghost specvar nodes :: "obj => objset" = "(% this. {})";
      invariant NodesAlloc: "ALL n. n : Node & n : alloc & n ~= null -->
         n..nodes \<subseteq> alloc";

      invariant NodesNull: "null..nodes = {}";

      invariant NodesDef: "ALL n. n : Node & n : alloc & n ~= null -->
         n..nodes = {n} Un n..next..nodes & 
         n ~: n..next..nodes";

      invariant NodesNotNull: "ALL n. n : Node --> null ~: n..nodes";

      invariant ConTrans: 
        "ALL n x. n : Node & n : alloc & n ~= null & x : n..nodes 
           --> x..nodes \<subseteq> n..nodes";

     public specvar content :: objset;
     vardefs "content == {x. EX n. n : first..nodes & x=n..data}";

     public ensured invariant ContentAlloc: "content \<subseteq> alloc";

     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..next) | 
                              (x : Queue & y = x..Queue.first))";

     invariant Inj: "ALL x1 x2 y.  x1 ~= null & x2 ~= null & y ~= null & 
         edge x1 y & edge x2 y --> x1=x2";

//     invariant contentDisj: "ALL l1 l2. l1 ~= l2 &
//         l1 : Queue & l1 : alloc & l1 ~= null &
//         l2 : Queue & l2 : alloc & l2 ~= null  -->
//	   l1..first..nodes Int l2..first..nodes = {}";
   */

    public Queue()
    /*: modifies content
        ensures "content = {}" */
    {
        first = null;
	last = null;
        // "first..nodes" := "{}";
    }

    public Object popFirst()
    /*: requires "content ~= {}"
        modifies content
        ensures "old content = content Un {result}"
    */
    {
	Node res = first;
	first = res.next;
	if (first==null) {
	    last = null;
	}
	res.next = null;
	//: "res..nodes" := "{res}"
	return res.data;
    }

    public void addLast(Object x)
    /*: modifies content
        ensures "content = old content Un {x}"
     */
    {
	Node n = new Node();
	n.data = x;
	if (first==null) {
	    first = n;
	    last = n;
	} else {
	    //: assume "False";	    
	    last.next = n;
	    last = n;
	    /*: 
	      havoc nodes;
	      assume beforeChange: "ALL x. 
	         (x : old (first..nodes) --> x..nodes = old (x..nodes) Un {n}) &
		 (x ~= n & x ~: old (first..nodes) --> x..nodes = old (x..nodes))";
	     */
	}
	//: "n..nodes" := "{n}"
    }
}
