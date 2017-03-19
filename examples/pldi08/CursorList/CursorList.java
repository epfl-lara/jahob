class Node {
    public Object data;
    public /*: claimedby CursorList */ Node next;
}

class CursorList {
   private Node first;

   private Node iterPos;
   private Node iterPrev;

   /*: 
      invariant prevDef: "iterPos \<noteq> first \<longrightarrow> iterPrev \<in> content \<and> iterPrev..next = iterPos";
      invariant prevElse: "iterPos = first \<longrightarrow> iterPrev = null";

      public specvar currentIter :: obj;
      vardefs "currentIter == iterPos";

      public ensured invariant iterInv:
         "(iter = {} \<longrightarrow> currentIter = null)  \<and>  (iter \<noteq> {} \<longrightarrow> currentIter \<in> iter)";

      private static ghost specvar nodes :: "obj \<Rightarrow> objset" = "\<lambda> this. {}";
      invariant NodesAlloc: "\<forall> n. n \<in> Node \<and> n \<in> alloc & n \<noteq> null \<longrightarrow> n..nodes \<subseteq> alloc";

      invariant NodesNull: "null..nodes = {}";

      invariant NodesDef: "\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<longrightarrow>
                                n..nodes = {n} \<union> n..next..nodes \<and> n \<notin> n..next..nodes";

      invariant NodesNotNull: "\<forall> n. n \<in> Node \<longrightarrow> null \<notin> n..nodes";

      invariant ConTrans: 
        "\<forall> n x. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> x \<in> n..nodes \<longrightarrow> x..nodes \<subseteq> n..nodes";

     public specvar content :: objset;
     vardefs "content == first..nodes";

     invariant firstInside: "first \<noteq> null \<longrightarrow> first \<in> content";

     public specvar iter :: objset;
     vardefs "iter == iterPos..nodes";

     public ensured invariant ContentAlloc: "content \<subseteq> alloc";
     public ensured invariant ContentNode: "content \<subseteq> Node";
     public ensured invariant IterSubset: "iter \<subseteq> content";

     private static specvar edge :: "obj \<Rightarrow> obj \<Rightarrow> bool";
     vardefs "edge == (\<lambda> x y. (x \<in> Node \<and> y = x..next) \<or> (x \<in> CursorList \<and> y = x..first))";

     invariant Inj: 
       "\<forall> x1 x2 y. x1 \<noteq> null \<and> x2 \<noteq> null \<and> y \<noteq> null \<and> edge x1 y \<and> edge x2 y \<longrightarrow> x1=x2";

     invariant contentDisj: "\<forall> l1 l2. l1 \<noteq> l2 \<and>
         l1 \<in> CursorList \<and> l1 \<in> Object.alloc \<and> l1 \<noteq> null \<and>
         l2 \<in> CursorList \<and> l2 \<in> Object.alloc \<and> l2 \<noteq> null 
      \<longrightarrow> l1..content \<inter> l2..content = {}";

     private static specvar boundaryBody :: "obj => bool";
     vardefs "boundaryBody == (\<lambda> that. (\<forall> x. x \<in> that..content \<and> x \<notin> that..iter \<and>
                                             x..next : that..iter \<longrightarrow> x = that..iterPrev))"
     invariant boundary: "boundaryBody this";

     invariant entry: "\<forall> x. x \<in> Node \<and> x \<noteq> null \<and> x..next \<in> content \<longrightarrow> x \<in> content";
   */

    public CursorList()
    /*: 
      modifies content, iter, currentIter 
      ensures "content = {} & Object.alloc = old Object.alloc"
    */
    {
        first = null;
	iterPos = null;
	iterPrev = null;
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
	    // note ok1: "iterPos ~= first";

	    Node pos = this.iterPos;
	    Node n = pos.next;
	    iterPrev.next = n;
	    pos.next = null;
	    iterPos = n;

	    /*: "CursorList.nodes" := 
		"\<lambda> n. if n = pos then {pos} else
		    (if (n \<in> old (this..content) \<and> n \<notin> old (this..iter))
		     then (old (n..nodes) \<setminus> {pos})
		     else old (n..nodes))"; */
	    
	}
    }
}
