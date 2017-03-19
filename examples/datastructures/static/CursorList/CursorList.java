public /*: claimedby CursorList */ class Node {
    public Object data;
    public Node next;
}

class CursorList {
   private static Node first;

   private static Node iterPos;
   private static Node iterPrev;

   /*: 
     public static specvar content :: objset;
     vardefs "content == first..con";

     public static specvar iter :: objset;
     vardefs "iter == iterPos..con";

     public static specvar currentIter :: obj;
     vardefs "currentIter == iterPos..data";

     static ghost specvar nodes :: "obj \<Rightarrow> objset" = "(\<lambda> n. {})";

     static specvar con :: "obj \<Rightarrow> objset";
     vardefs "con == (\<lambda> n. {x. \<exists> y. y \<in> n..nodes \<and> x = y..data})";

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

     invariant Inj: 
     "\<forall> x y. x \<in> Node \<and> y \<in> Node \<and> x..next = y \<and>
      y \<noteq> null \<longrightarrow> first \<noteq> y \<and>
      (ALL z. z \<in> Node \<and> z..next = y \<longrightarrow> x = z)";

     invariant EntryInv: 
     "\<forall> x. x \<in> Node \<and> x \<noteq> null \<and> 
      x..next \<in> first..nodes \<longrightarrow> x \<in> first..nodes";

     invariant BoundaryInv: 
     "\<forall> x. x \<in> first..nodes \<and> x \<notin> iterPos..nodes \<and> 
      x..next \<in> iterPos..nodes \<longrightarrow> x = iterPrev";
   */

    public static void init()
    /*: 
      modifies content, iter, currentIter 
      ensures "content = {} & Object.alloc = old Object.alloc"
    */
    {
        first = null;
	iterPos = null;
	iterPrev = null;
    }

    public static boolean member(Object o1)
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

    public static Object addNew(Object o1)
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

    public static void initIter()
    /*: modifies iter, currentIter
        ensures "iter = content" */
    {
	iterPos = first;
	iterPrev = null;
    }
 
    public static Object nextIter()
    /*: requires "iter ~= {}" 
        modifies iter, currentIter
	ensures "iter = old iter - {result} & result : old iter"
    */
    {
	iterPrev = iterPos;
	iterPos = iterPos.next;
	return iterPrev.data;
    }

    public static Object getCurrent()
    /*: requires "iter ~= {}"
        ensures  "result = currentIter" */
    {
	return iterPos.data;
    }

    public static boolean lastIter()
    //: ensures "result = (iter = {})"
    {
	return iterPos == null;
    }

    public static void removeCurrent()
    /*: requires "iter \<noteq> \<emptyset>"
        modifies content, iter, currentIter
	ensures "content = old content \<setminus> {old currentIter} & 
                 iter = old iter \<setminus> {old currentIter}" */
    {
	//: note IterPosNotNull: "iterPos \<noteq> null";
	if (iterPos == first) {
	    //: note notNull: "first ~= null";
	    Node n = first;
	    first = first.next;
	    iterPos = first;
	    iterPrev = null;
	    n.next = null;
	    //: "n..nodes" := "{n}";
	} else {
	    //: note prevNext: "iterPrev..Node.next = iterPos";

	    Node pos = iterPos;
	    Node n = pos.next;
	    iterPrev.next = n;
	    pos.next = null;
	    iterPos = n;

	    /*: "nodes" := 
		"\<lambda> n. if n = pos then {pos} else
		   (if (n \<in> old (first..nodes) \<and> 
		        n \<notin> old (iterPos..nodes))
		     then (old (n..nodes) \<setminus> {pos})
		     else old (n..nodes))"; */

	    {//: pickAny x::obj;
		{//: assuming lhsHyp: "x \<in> Node \<and> x \<in> alloc \<and> x \<noteq> null";
		    {//: assuming PosHyp: "x = pos";
		     //: note PosConc: "x..nodes = {x} \<union> x..next..nodes";
		    }
		    {//: assuming TrueHyp: "x \<noteq> pos \<and> x \<in> old (first..nodes) \<and> x \<notin> old (iterPos..nodes)";
		     //: note TrueConc: "x..nodes = {x} \<union> x..next..nodes";
		    }
		    {//: assuming FalseHyp: "x \<noteq> pos \<and> \<not> (x \<in> old (first..nodes) \<and> x \<notin> old (iterPos..nodes))";
		     //: note FalseConc: "x..nodes = {x} \<union> x..next..nodes";
		    }
		 //: note conj1: "x..nodes = {x} \<union> x..next..nodes" from PosConc, TrueConc, FalseConc;
		 //: note conj2: "x \<notin> x..next..nodes";
		 //: note rhsConc: "x..nodes = {x} \<union> x..next..nodes \<and> x \<notin> x..next..nodes" from conj1, conj2;
		}
	     //: note NodesDefConc: "x \<in> Node \<and> x \<in> alloc \<and> x \<noteq> null \<longrightarrow> x..nodes = {x} \<union> x..next..nodes \<and> x \<notin> x..next..nodes" forSuch x;
	    }
	}
    }
}
