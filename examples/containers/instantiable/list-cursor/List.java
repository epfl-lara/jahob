/* Instantiable list with data fields.
Use this class to create Node's inside list and move within the list.
Put your useful data inside 'data' field, which is not touched by the List class.
    
    PLUS:
      -instantiable
      -object content cleanly exposed by claiming only 'next' field
      -iterator operations
      -member, add, removeCurrent operations
    MINUS:
      -manual setting of ghost fields
      -manual proofs (but solely in source code!)
      -had to do manually a sound havoc+assume since due to minor ite rewriting limitation
 */

class Node {
    public Object data;
    public /*: claimedby List */ Node next;
}
class Cell {
}
class List {
   private Node first;

   private Node iterPos;
   private Node iterPrev;

   /*: 
      invariant prevDef: "iterPos ~= first --> iterPrev : content & iterPrev..Node.next = iterPos";
      invariant prevElse: "iterPos = first --> iterPrev = null";

      public specvar currentIter :: obj;
      vardefs "currentIter == iterPos";

      public ensured invariant iterInv:
                 "(iter = {} --> currentIter = null) &
                  (iter ~= {} --> currentIter : iter)";

      private static ghost specvar nodes :: "obj => objset" = "(% this. {})";
      invariant NodesAlloc: "ALL n. n : Node & n : Object.alloc & n ~= null -->
         n..nodes \<subseteq> Object.alloc";

      invariant NodesNull: "null..nodes = {}";

      invariant NodesDef: "ALL n. n : Node & n : Object.alloc & n ~= null -->
         n..nodes = {n} Un n..Node.next..nodes & 
         n ~: n..Node.next..nodes";

      invariant NodesNotNull: "ALL n. n : Node --> null ~: n..nodes";

      invariant ConTrans: 
        "ALL n x. n : Node & n : Object.alloc & n ~= null & x : n..nodes 
           --> x..nodes \<subseteq> n..nodes";

     public specvar content :: objset;
     vardefs "content == first..nodes";

     invariant firstInside: "first ~= null --> first : content";

     public specvar iter :: objset;
     vardefs "iter == iterPos..nodes";

     public ensured invariant ContentAlloc: "content \<subseteq> Object.alloc";
     public ensured invariant ContentNode: "content \<subseteq> Node";
     public ensured invariant IterSubset: "iter \<subseteq> content";

     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..Node.next) | 
                              (x : List & y = x..List.first))";

     invariant Inj: "ALL x1 x2 y.  x1 ~= null & x2 ~= null & y ~= null & 
         edge x1 y & edge x2 y --> x1=x2";

     invariant contentDisj: "ALL l1 l2. l1 ~= l2 &
         l1 : List & l1 : Object.alloc & l1 ~= null &
         l2 : List & l2 : Object.alloc & l2 ~= null  -->
	l1..content Int l2..content = {}";

     private static specvar boundaryBody :: "obj => bool";
     vardefs "boundaryBody == (%that. (ALL x. x : that..content & x ~: that..iter & 
                                   x..Node.next : that..iter --> x = that..iterPrev))"
     invariant boundary: "boundaryBody this";

     invariant entry: "ALL x. x : Node & x ~= null &
                        x..Node.next : content --> x : content";
   */

    public List()
    /*: 
      modifies content, iter, currentIter 
      ensures "content = {} & Object.alloc = old Object.alloc"
    */
    {
        first = null;
	iterPos = null;
	iterPrev = null;
        // "first..nodes" := "{}";
    }

    public boolean member(Node o1)
    //: ensures "result = (o1 : content) & Object.alloc = old Object.alloc";
    {
        return member1(o1);
    }

    private boolean member1(Node n)
    /*: requires "theinvs"
        ensures "result = (n : content) & theinvs & Object.alloc = old Object.alloc"
    */
    {
        Node current = first;
        while /*: inv "current : Node & current : Object.alloc &
                       (n : content) = (n : current..nodes)" */
            (current != null) {
            if (current==n) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public Node addNew()
    /*: modifies content
        ensures "content = old content Un {result} & 
	         Object.alloc = (old Object.alloc) Un {result}";
    */
    {
	Node n = new Node();
	n.next = first;
	if (iterPos==first) {
	    iterPrev = n;
	}
	//: "n..nodes" := "{n} Un first..nodes";
	first = n;
	return n;
    }

    public void initIter()
    /*: modifies iter, currentIter
        ensures "iter = content" */
    {
	iterPos = first;
	iterPrev = null;
    }
 
    public Node nextIter()
    /*: requires "iter ~= {}" 
      modifies iter, currentIter
      ensures "iter = old iter - {result} & 
               result : old iter"
    */
    {
	iterPrev = iterPos;
	iterPos = iterPos.next;
	return iterPrev;
    }

    public Node getCurrent()
    //: ensures "result = currentIter" 
    {
	return iterPos;
    }

    public boolean lastIter()
    //: ensures "result = (iter = {})"
    {
	return iterPos == null;
    }

    public void removeCurrent()
    /*:
     requires "comment ''currentNotNull'' (currentIter ~= null)"
     modifies content, iter, currentIter
     ensures "content = old content \<setminus> {old currentIter} & 
              iter = old iter \<setminus> {old currentIter}" */
    {
	if (iterPos==first) {
	    //: note notNull: "first ~= null";
	    Node n = first;
	    first = first.next;
	    iterPos = first;
	    iterPrev = null;
	    n.next = null;
	    //: "n..nodes" := "{n}";
	} else {
	    //: note prevNext: "iterPrev..Node.next = iterPos";
	    //: note ok1: "iterPos ~= first";

	    Node pos = this.iterPos;
	    Node n = pos.next;
	    iterPrev.next = n;
	    pos.next = null;
	    iterPos = n;

            /* // It would be nice if we could write this, but our provers don't like yet conditional set expressions:
                "List.nodes" := "% (lst::obj). 
                 (if (lst = pos) then {pos}
                  else (if ((lst : this..content) & (lst ~: this..iter)) 
                   then (lst..nodes \<setminus> {pos})
                   else (lst..nodes)))";
            */

	    /*: // This havoc+assume combination is sound because it corresponds to an assignment to 'nodes'.
	      havoc "List.nodes";
	      assume newNodes1: "pos..nodes = {pos}";
	      assume newNodes2: "ALL lst. lst : old (this..content) & lst ~: old (this..iter)
                  --> lst..nodes = old (lst..nodes) \<setminus> {pos}";
	      assume newNodes3: "ALL lst.  (lst ~= pos & ~(lst : old (this..content) & lst ~: old (this..iter)))
                  --> lst..nodes = old (lst..nodes)";
	    */

	    /*:
	      note ok2: "iterPos ~= first";

	      note theFrame1: "ALL n. 
                  n : Node & n ~: old (this..content) & n ~= pos &
                  n ~= null & n : Object.alloc 
                --> n..nodes = fieldRead (old List.nodes) n &
		    n..Node.next = fieldRead (old Node.next) n";
	      note theFrame2: "ALL lst. lst ~= this -->
	           lst..first = old (lst..first) &
		   lst..iterPos = old (lst..iterPos) &
		   lst..iterPrev = old (lst..iterPrev)";

	     
	     note theFrame18: "ALL (lst::obj). lst : Object.alloc & lst : List & lst ~= null & lst ~= this & lst..first ~= null
                --> lst..first ~: old (this..content)";

             note totalFrame1: "(ALL framedObj. (((framedObj : old Object.alloc) & (framedObj : List) & (framedObj \<noteq> old this)) --> ((List.content framedObj) = ((old List.content) framedObj))))";

             note totalFrame3: "(ALL framedObj. (((framedObj : old Object.alloc) & (framedObj : List) & (framedObj \<noteq> old this)) --> 
  ((List.currentIter framedObj) = ((old List.currentIter) framedObj))))"

	     note totalFrame17: "(ALL framedObj. (((framedObj : old Object.alloc) & (framedObj : List) & 
                (framedObj ~= this)) --> framedObj..iterPos ~: old (this..content)))";

	     note totalFrame2: "(ALL framedObj. (((framedObj : old Object.alloc) & (framedObj : List) & 
(framedObj \<noteq> old this)) --> ((List.iter framedObj) = ((old List.iter) framedObj))))";

	      note backg1: "ALL x. x : List --> 
	                            old (x..iterPos) : Node";
	      note backg2: "ALL x. x : Node --> 
	                            old (x..Node.next) : Node";
	      note backg3: "((Node Int List) = {null})";
	      note "theinv Inj" by
	        backg1, backg2, backg3,
                Inj, edge_def, prevNext, currentNotNull, 
                currentIter_def, iter_def;

	      note "theinv entry";

	      note goneIter: "iter = (old iter) \<setminus> {pos}";
	      note goneContent: "content = (old content) \<setminus> {pos}";

	      note thisBoundary: "boundaryBody this";

              note well: "theinv iterInv";

	    */
	    // proving "theinv boundary":
	    { //: pickAny that::obj suchThat "that : Object.alloc & that : List";
		//: note forThis: "that = this --> boundaryBody that" by boundaryBody_def, thisBoundary, forThis, this;
		{ /*: assuming h0: "that ~= this";
		    note "that..iter = fieldRead (old List.iter) that";
		    note "that..content = fieldRead (old List.content) that";
		    note "that..iterPrev = fieldRead (old List.iterPrev) that";		      
		    note "boundaryBody that";
		  */
		}
		//: note forAny: "boundaryBody that" forSuch that;
	    }
	    //: note shownBoundary: "theinv boundary"

	    // proving "theinv NodesDef"
	    { /*: pickAny x::obj suchThat h3: "x : Node & x : Object.alloc & x ~= null";
		note p4: "x ~: x..Node.next..nodes";
		note p2: "x ~= pos & 
		x : old (this..content) &
		x ~: old (this..iter) &
		(old Node.next) x ~: (old List.content) this &
		(old Node.next) x ~: (old List.iter) this
		--> x..nodes = {x} Un x..Node.next..nodes";
		
		note p5: "x ~= pos & 
		(x ~: old (this..content) | x : old (this..iter))
		 --> x..nodes = {x} Un x..Node.next..nodes"; // needs 30sec	  
		    
		    note p6: "x = pos
		     --> x..nodes = {x} Un x..Node.next..nodes";
		    
		    note p7: "x ~= pos & 
		    x : old (this..content) &
		    x ~: old (this..iter) &
		    (old Node.next) x : (old List.content) this &
		    (old Node.next) x ~: (old List.iter) this
		    --> x..nodes = {x} Un x..Node.next..nodes";

		    note p8: "x = old iterPrev 
		    --> x..nodes = {x} Un x..Node.next..nodes";
			   
		    note p9: "x ~= pos & 
		    x : old (this..content) &
		    x ~: old (this..iter) &	
		    (old Node.next) x : (old List.iter) this
		    --> x = old iterPrev"; //works!

 		    note p10: "x..nodes = {x} Un x..Node.next..nodes &
                                   x ~: x..Node.next..nodes" by p5, p6, p7, p8, p9, p10, p2, p4 forSuch x;
	      */
	    }
	    //: note shownNodesDef: "theinv NodesDef";
    
	    // proving "theinv contentDisj";
	    { //: pickAny l1::obj, l2::obj 
		{/*: assuming ha: "l1 ~= l2 &
		   l1 : List & l1 : Object.alloc & l1 ~= null &
		   l2 : List & l2 : Object.alloc & l2 ~= null";
 
	     note a3: "(l1::obj) ~= this & (l2::obj) ~= this -->
                    l1..content Int l2..content = {}"
	        by ha, contentDisj, totalFrame1, a3;

             note a4: "this..content \<subseteq> old (this..content)";

	     note a5: "(l2::obj) ~= this -->
                    this..content Int l2..content = {}"
	        by ha, contentDisj, totalFrame1, a4, a5, this;
		
	      */
		}
		/*: note "l1 ~= l2 &
		     l1 : List & l1 : Object.alloc & l1 ~= null &
  		     l2 : List & l2 : Object.alloc & l2 ~= null -->
                       l1..content Int l2..content = {}" forSuch l1,l2;
		*/
	    }
            //: note "theinv contentDisj";

	    // now proving "theinv ConTrans";
	    { //: pickAny x::obj, y::obj
		{/*: assuming h9: "x : Node & x : Object.alloc & x ~= null & y : x..nodes";

			note h9a: "y : (old List.nodes) x";
			note h9b: "y..nodes \<subseteq> (old List.nodes) x"
			by h9a, ConTrans, h9, type, newNodes1, newNodes2, newNodes3;
		     
			note a9: "x ~: old (this..content)
			--> List.nodes x = (old List.nodes) x";
			
             note a10: "x ~: old (this..content) 
	     --> y..nodes \<subseteq> x..nodes";
	     
	     note a12: "x = pos 
	     --> y..nodes \<subseteq> x..nodes";
	     
             note a15: "x ~= pos & x : old (this..iter) 
	     --> y..nodes \<subseteq> List.nodes x";
		 */
		    // the last case
		    {/*: assuming xLast: "x ~= pos & x : old (this..content) &
		                        x ~: old (this..iter)";

                    note xLast1: "x : old Object.alloc & x ~= null & x : Node";
					
                    note xDom1: "x : old (this..first..nodes)";
 
      	            note joj1: "old (this..first) : old Object.alloc";
	            note joj2: "old (this..first) ~= null";
	            note joj3: "old (this..first) : Node";

                    note xDom2: "(old List.nodes) x \<subseteq> old (this..first..nodes)"
                      by xDom1, ConTrans, xLast, xLast1, joj1, joj2, joj3, h9;

                    note change1: "List.nodes x = (old List.nodes) x \<setminus> {pos}"
                      by xLast, xLast1, newNodes2;

     	            note yDom1: "y ~= pos";

    	            note yDom2: "y : (old List.nodes) x" by h9, change1;
    	            note yDom3: "y : old (this..first..nodes)" by yDom2, xDom2;
	            note yDom4: "y : old (this..content)";

	            note yGood2: "y ~: old (this..iter) --> y..nodes \<subseteq> x..nodes";
		     */            
			{/*: assuming hy: "y : old (this..iter)";
                             note n1: "List.nodes y = (old List.nodes) y";

			     note n2: "pos ~: (old List.nodes) ((old Node.next) pos)";

			     note n3: "(old List.nodes) y \<subseteq> 
			       (old List.nodes) ((old Node.next) pos)";

			       note n10: "pos ~: y..nodes" by n3, n2, n1;

			       note yGood6: "y..nodes \<subseteq> x..nodes";
			 */
			}
		     /*: note forLast: "y..nodes \<subseteq> x..nodes" 
			  by yGood6, yGood2;
		     */
		    }
		    //: note mostly: "y..nodes \<subseteq> x..nodes";
		}
		/*: note transBody:
                     "x : Node & x : Object.alloc & x ~= null & 
		     y : x..nodes --> y..nodes \<subseteq> x..nodes";
		*/
	    }
	    //: note shownConTrans: "theinv ConTrans";
	}
    }
}
