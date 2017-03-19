// use this class to create Node's inside list and move within the list.
// Put your useful data inside 'data' field, which is not touched by the List class.

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

    public void removeCurrent()
    /*:
     requires "comment ''currentNotNull'' (currentIter ~= null)"
     modifies content, iter, currentIter
     ensures "content = old content \<setminus> {old currentIter} & 
              iter = old iter \<setminus> {old currentIter}" */
    {
	if (iterPos==first) {
	    //: assume "False";
	    //: noteThat notNull: "first ~= null";
	    Node n = first;
	    first = first.next;
	    iterPos = first;
	    iterPrev = null;
	    n.next = null;
	    //: "n..nodes" := "{n}";
	} else {
	    //: noteThat prevNext: "iterPrev..Node.next = iterPos";
	    //: noteThat ok1: "iterPos ~= first";

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
	      noteThat ok2: "iterPos ~= first";

	      noteThat theFrame1: "ALL n. 
                  n : Node & n ~: old (this..content) & n ~= pos &
                  n ~= null & n : Object.alloc 
                --> n..nodes = fieldRead (old List.nodes) n &
		    n..Node.next = fieldRead (old Node.next) n";
	      noteThat theFrame2: "ALL lst. lst ~= this -->
	           lst..first = old (lst..first) &
		   lst..iterPos = old (lst..iterPos) &
		   lst..iterPrev = old (lst..iterPrev)";

	     
	     noteThat theFrame18: "ALL (lst::obj). lst : Object.alloc & lst : List & lst ~= null & lst ~= this & lst..first ~= null
                --> lst..first ~: old (this..content)";

             noteThat totalFrame1: "(ALL framedObj. (((framedObj : old Object.alloc) & (framedObj : List) & (framedObj \<noteq> old this)) --> ((List.content framedObj) = ((old List.content) framedObj))))";

             noteThat totalFrame3: "(ALL framedObj. (((framedObj : old Object.alloc) & (framedObj : List) & (framedObj \<noteq> old this)) --> 
  ((List.currentIter framedObj) = ((old List.currentIter) framedObj))))"

	     noteThat totalFrame17: "(ALL framedObj. (((framedObj : old Object.alloc) & (framedObj : List) & 
                (framedObj ~= this)) --> framedObj..iterPos ~: old (this..content)))";

	     noteThat totalFrame2: "(ALL framedObj. (((framedObj : old Object.alloc) & (framedObj : List) & 
(framedObj \<noteq> old this)) --> ((List.iter framedObj) = ((old List.iter) framedObj))))";

	      noteThat backg1: "ALL x. x : List --> 
	                            old (x..iterPos) : Node";
	      noteThat backg2: "ALL x. x : Node --> 
	                            old (x..Node.next) : Node";
	      noteThat backg3: "((Node Int List) = {null})";
	      noteThat "theinv Inj" from
	        backg1, backg2, backg3,
                Inj, edge_def, prevNext, currentNotNull, 
                currentIter_def, iter_def;

	      noteThat "theinv entry";

	      noteThat goneIter: "iter = (old iter) \<setminus> {pos}";
	      noteThat goneContent: "content = (old content) \<setminus> {pos}";

	      noteThat thisBoundary: "boundaryBody this";

              noteThat well: "theinv iterInv";

	    */
	    List that, l1, l2;
	    Node y, z;
	    // proving "theinv boundary":		
	    { //: pickAny that::obj suchThat "that : Object.alloc & that : List";
		//: noteThat forThis: "that = this --> boundaryBody that" from boundaryBody_def, thisBoundary, forThis, this;
		{ /*: assuming h0: "that ~= this";
		    noteThat "that..iter = fieldRead (old List.iter) that";
		    noteThat "that..content = fieldRead (old List.content) that";
		    noteThat "that..iterPrev = fieldRead (old List.iterPrev) that";		      
		    noteThat "boundaryBody that";
		  */
		}
		//: noteThat forAny: "boundaryBody that" forSuch that;
	    }
	    //: noteThat shownBoundary: "theinv boundary"
	    //: assume "False";
	}
    }
}
