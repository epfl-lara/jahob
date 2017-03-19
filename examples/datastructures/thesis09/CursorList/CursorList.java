public /*: claimedby CursorList */ class Node {
    public Object data;
    public Node next;
}

class CursorList {
   private Node first;

   private Node iterPos;
   private Node iterPrev;

   /*: 
     public specvar content :: objset;
     vardefs "content == first..con";

     public specvar iter :: objset;
     vardefs "iter == iterPos..con";

     public specvar currentIter :: obj;
     vardefs "currentIter == iterPos..data";

     public specvar visiting :: bool;
     vardefs "visiting == (iterPos \<noteq> null)";

     public ghost specvar toVisit :: objset;

     public ghost specvar visited :: objset;

     static ghost specvar nodes :: "obj \<Rightarrow> objset" = "(\<lambda> n. {})";

     static specvar con :: "obj \<Rightarrow> objset";
     vardefs "con == (\<lambda> n. {x. \<exists> y. y \<in> n..nodes \<and> x = y..data})";

     invariant VisitedInv: "visiting \<longrightarrow> (toVisit = visited \<union> iter \<and> visited \<inter> iter = \<emptyset>)";

     invariant ConInjInv:
     "\<forall> x. x \<in> Node \<and> x \<in> alloc \<longrightarrow>
      (\<forall> m n. m \<in> x..nodes \<and> n \<in> x..nodes \<and> 
      m..data = n..data \<and> m..data \<noteq> null \<longrightarrow> m = n)";

     invariant ConNonNull: 
     "\<forall> x. x \<in> Node \<and> x \<in> alloc \<longrightarrow> 
      null \<notin> x..con";

     invariant NodesAlloc:
     "\<forall> x. x \<in> Node \<and> x \<in> alloc \<longrightarrow>
      x..nodes \<subseteq> alloc";

     invariant NodesDef:
     "\<forall> x. x \<in> Node \<and> x \<in> alloc \<and> 
      x \<noteq> null \<longrightarrow> 
      x..nodes = {x} \<union> x..next..nodes \<and> x \<notin> x..next..nodes";

     invariant NodesNotNull:
     "\<forall> x. x \<in> Node \<and> x \<in> alloc \<longrightarrow>
      null \<notin> x..nodes";

     invariant ConTrans:
     "\<forall> y. y \<in> Node \<and> y \<in> alloc \<longrightarrow>
      (\<forall> x. x \<in> y..nodes \<longrightarrow> 
      x..nodes \<subseteq> y..nodes)";

     invariant NodesNull: "null..nodes = \<emptyset>";

     invariant prevDef: 
     "iterPos \<noteq> first \<longrightarrow> 
      iterPrev \<in> first..nodes \<and> iterPrev..next = iterPos";

     invariant prevElse: "iterPos = first \<longrightarrow> iterPrev = null";

     invariant iterInv:
     "(iterPos..nodes = {} \<longrightarrow> iterPos = null)  \<and>  
      (iterPos..nodes \<noteq> {} \<longrightarrow> 
       iterPos \<in> iterPos..nodes)";

     invariant ContentAlloc: "first..nodes \<subseteq> alloc";
     invariant ContentNode: "first..nodes \<subseteq> Node";
     invariant IterSubset: "iterPos..nodes \<subseteq> first..nodes";

     private static specvar edge :: "obj \<Rightarrow> obj \<Rightarrow> bool";
     vardefs "edge == (\<lambda> x y. (x \<in> Node \<and> y = x..next) \<or> 
     (x \<in> CursorList \<and> y = x..first))";

     invariant Inj: 
     "\<forall> x1 x2 y. x1 \<noteq> null \<and> x2 \<noteq> null \<and> 
      y \<noteq> null \<and> edge x1 y \<and> edge x2 y \<longrightarrow> 
      x1=x2";

     invariant NodesDisj:
     "\<forall> l1 l2. l1 \<noteq> l2 \<and> l1 \<in> CursorList \<and> 
      l1 \<in> Object.alloc \<and> l1 \<noteq> null \<and> 
      l2 \<in> CursorList \<and> l2 \<in> Object.alloc \<and> 
      l2 \<noteq> null \<longrightarrow> 
      l1..first..nodes \<inter> l2..first..nodes = {}";

     invariant EntryInv: 
     "\<forall> x. x \<in> Node \<and> x \<noteq> null \<and> 
      x..next \<in> first..nodes \<longrightarrow> x \<in> first..nodes";

     invariant BoundaryInv: 
     "\<forall> x. x \<in> first..nodes \<and> x \<notin> iterPos..nodes \<and> 
      x..next \<in> iterPos..nodes \<longrightarrow> x = iterPrev";
   */

    public CursorList()
    /*: 
      modifies content, iter, currentIter, toVisit, visited, visiting
      ensures "content = \<emptyset> \<and> iter = \<emptyset> \<and> currentIter = null \<and> toVisit = \<emptyset> \<and> visited = \<emptyset> \<and> \<not> visiting \<and> alloc = old alloc"
    */
    {
        first = null;
	iterPos = null;
	iterPrev = null;
	//: toVisit := "\<emptyset>";
	//: visited := "\<emptyset>";
    }

    public boolean member(Object o1)
    //: ensures "result = (o1 : content) & Object.alloc = old Object.alloc";
    {
        Node current = first;
        while /*: inv "current : Node & current : Object.alloc &
                       (o1 : content) = (o1 : current..con)" */
            (current != null) {
            if (current.data == o1) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public Object addNew(Object o1)
    /*: requires "o1 \<noteq> null \<and> o1 \<notin> content"
        modifies content
        ensures  "content = old content Un {o1}" */
    {
	Node n = new Node();
	n.data = o1;
	n.next = first;
	if (iterPos==first) {
	    iterPrev = n;
	}
	//: "n..nodes" := "{n} Un first..nodes";
	first = n;
	return n;
    }

    public void initIter()
    /*: modifies iter, currentIter, toVisit, visited, visiting
        ensures "iter = content \<and> toVisit = content \<and> visited = \<emptyset> \<and> (visiting \<or> (iter = \<emptyset> \<and> visited = toVisit))" */
    {
	iterPos = first;
	iterPrev = null;
	//: toVisit := "content";
	//: visited := "\<emptyset>";
    }
 
    public Object nextIter()
    /*: requires "iter \<noteq> \<emptyset>" 
        modifies iter, currentIter, visited, visiting
	ensures "result = old currentIter \<and> iter = old iter \<setminus> {result} \<and> result \<in> old iter \<and> visited = old visited \<union> {result} \<and> result \<notin> old visited \<and> (visiting \<or> (iter = \<emptyset> \<and> visited = toVisit))" */
    {
	iterPrev = iterPos;
	iterPos = iterPos.next;
	//: visited := "visited \<union> {iterPrev..data}";
	return iterPrev.data;
    }

    public Object getCurrent()
    /*: requires "iter \<noteq> \<emptyset>"
        ensures  "result = currentIter" */
    {
	return iterPos.data;
    }

    public boolean lastIter()
    //: ensures "result = (iter = \<emptyset>)"
    {
	return iterPos == null;
    }

    public void removeCurrent()
    /*: requires "iter \<noteq> \<emptyset>"
        modifies content, iter, currentIter, toVisit, visiting
	ensures "content = old content \<setminus> {old currentIter} \<and> 
                 iter = old iter \<setminus> {old currentIter} \<and>
		 (toVisit = old toVisit \<setminus> {old currentIter}) \<and>
		 (visiting \<or> (iter = \<emptyset> \<and> visited = toVisit))" */
    {
	//: note IterPosNotNull: "iterPos \<noteq> null";
	if (iterPos==first) {
	    //: note notNull: "first ~= null";
	    Node n = first;
	    first = first.next;
	    iterPos = first;
	    iterPrev = null;
	    n.next = null;
	    //: toVisit := "toVisit \<setminus> {n..data}";
	    //: "n..nodes" := "{n}";
	} else {
	    //: note prevNext: "iterPrev..Node.next = iterPos";

	    Node pos = iterPos;
	    Node n = pos.next;
	    iterPrev.next = n;
	    pos.next = null;
	    iterPos = n;

	    //: toVisit := "toVisit \<setminus> {pos..data}";
	    /*: "nodes" := 
		"\<lambda> n. if n = pos then {pos} else
		   (if (n \<in> old (first..nodes) \<and> 
		        n \<notin> old (iterPos..nodes))
		     then (old (n..nodes) \<setminus> {pos})
		     else old (n..nodes))"; */

	    {//: localize;
	     //: note NextNull: "null..next = null";
	     //: note iterPrevNull: "null..iterPrev = null";
	     /*: note BoundaryPost: "theinv BoundaryInv"
	       from edge_def, currentIter_def, field_pointsto, IterPosNotNull,
               prevElse, iterInv, NodesDisj, EntryInv, BoundaryInv, 
               ContentAlloc, ContentNode, IterSubset, NodesDef, NodesNotNull, 
               thisType, prevNext, NextNull, iterPrevNull; */
	    }
	}
    }
}
