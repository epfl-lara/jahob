class Node {
    private static int nnid = 0;

    private Node[] edges = null;
    private int numEdges = 0;
    private int nid;
    Node parent;
    private boolean visited = false;

    /*: public static ghost specvar root :: obj;
        public static ghost specvar processed :: objset = "{}";

	public ghost specvar ancestors :: objset = "{}";

	public ghost specvar init :: bool = "False";

	public specvar neighbors :: objset;
	private vardefs "neighbors == 
	 {x. x \<noteq> null \<and> (\<exists> i. 0 \<le> i \<and> i < numEdges \<and> x = edges.[i])}";

	private invariant EdgesInv: "init \<longrightarrow> edges \<noteq> null \<and> edges \<in> hidden"

	private invariant NumEdgesLBInv: "0 \<le> numEdges"
	private invariant NumEdgesUBInv: "init \<longrightarrow> numEdges \<le> edges..length"

	private invariant NeighborsInv:
	"init \<longrightarrow> (\<forall> i. (0 \<le> i \<and> i < numEdges) \<longrightarrow> (edges.[i] \<noteq> null \<and> edges.[i]..init))"

	private invariant AncestorsInv: "visited \<and> this \<noteq> root \<longrightarrow> root \<in> ancestors"
	private invariant ProcessedInv: "visited = (this \<in> processed)"

	private invariant NVAncestorsInv: "\<not> visited \<longrightarrow> ancestors = {}"
	
	private invariant NVParentInv: 
	"\<not> visited \<and> this \<noteq> null \<longrightarrow> (\<forall> x. x..parent \<noteq> this)"

	private invariant AncestorsBCInv:
	"visited \<and> parent = null \<longrightarrow> ancestors = {}"

	private invariant AncestorsICInv:
	"visited \<and> parent \<noteq> null \<longrightarrow> ancestors = parent..ancestors \<union> {parent}"

	private invariant NotInitInv: "\<not> init \<longrightarrow> ancestors = {}";

	private invariant RootInv: "visited \<and> parent = null \<longrightarrow> root = this"

	private invariant InjInv: "\<forall> x y. x \<noteq> y \<and> x..edges \<noteq> null \<longrightarrow> x..edges \<noteq> y..edges";

	private invariant ProcessedNodesInv: "\<forall> x. x \<in> processed \<longrightarrow> x \<in> Node \<and> x \<in> alloc"

        private invariant RootAncestorsInv: "root..ancestors = {}"
    */

    public Node(int maxEdges)
    /*: requires "0 < maxEdges \<and> \<not> init"
        modifies ancestors, neighbors, init
        ensures  "neighbors = \<emptyset> \<and> ancestors = \<emptyset> \<and> init"
    */
    {
	edges = new /*: hidden */ Node[maxEdges];
	numEdges = 0;
	nid = nnid;
	nnid = nnid + 1;
	//: "init" := "True";
	//: "ancestors" := "\<emptyset>";
    }

    public boolean addEdge(Node n)
    /*: requires "init \<and> n \<noteq> null \<and> n..init"
        modifies neighbors
        ensures  "(result \<longrightarrow> neighbors = old neighbors \<union> { n }) \<and> 
	          (\<not> result \<longrightarrow> neighbors = old neighbors)"
     */
    {
	if (numEdges < edges.length) {

	    edges[numEdges] = n;
	    numEdges = numEdges + 1;

	    {
	      //: assuming "True";
	      //: noteThat NNonNull: "n \<noteq> null";
	      //: noteThat ZeroLEOldNumEdges: "0 \<le> old numEdges";
	      /*: noteThat OldNeighborsDef: "old neighbors = {x. x \<noteq> null \<and> 
	          (\<exists> i. 0 \<le> i \<and> i < old numEdges \<and> x = old (edges.[i]))}"; */
	      /*: noteThat NewNeighborsDef: "neighbors = {x. x \<noteq> null \<and>
	          (\<exists> i. 0 \<le> i \<and> i < numEdges \<and> x = edges.[i])}"; */
	      /*: noteThat NeighborsPostCond: 
	          "neighbors = (old neighbors) \<union> { n }"
	          from NeighborsPostCond, OldNeighborsDef, NewNeighborsDef,
		    NNonNull, ZeroLEOldNumEdges; */
            }
	    return true;
	}
	return false;
    }

    public void compute()
    /*: requires "init \<and> ancestors = {} \<and> root = null \<and> processed = {}"
        modifies "Node.ancestors", "Node.root", "Node.parent", "Node.processed"
	ensures "root = this \<and> this \<in> processed \<and> 
                 (\<forall> x y. x \<in> processed \<and> y \<in> x..neighbors \<longrightarrow> y \<in> processed) \<and>
		 (\<forall> x. x \<in> processed \<and> x \<noteq> root \<longrightarrow> root \<in> x..ancestors)"
    */
    {
	makeRoot();

	int i = 0;
 
	while /*: inv "0 \<le> i \<and> theinvs \<and> this \<in> processed \<and>
		       (\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> edges.[j] \<in> processed) \<and>
		       (\<forall> x y. x \<noteq> this \<and> x \<notin> ancestors \<and> x \<in> processed \<and> 
		       y \<in> x..neighbors \<longrightarrow> y \<in> processed)"
	       */
	    (i < numEdges()) {
	    edge(i).span(this);
	    i = i + 1;
	}
    }

    private void makeRoot()
    /*: requires "init \<and> root = null \<and> ancestors = {} \<and> processed = {} \<and> 
                  theinvs"
        modifies ancestors, root, processed, visited
        ensures  "visited \<and> parent = null \<and> root = this \<and> 
	          ancestors = {} \<and> processed = { this } \<and> theinvs"
    */
    {
	visited = true;
	//: "Node.root" := "this";
	//: "ancestors" := "{}";
	//: "processed" := "processed \<union> { this }";
    }

    private boolean visit(Node p)
    /*: requires "init \<and> p \<noteq> null \<and> p..visited \<and> root..visited \<and> 
	          (p \<noteq> root \<longrightarrow> root \<in> p..ancestors) \<and>
	          (\<forall> x y. x \<noteq> p \<and> x \<notin> p..ancestors \<and> x \<in> processed \<and>
		  y \<in> x..neighbors \<longrightarrow> y \<in> processed) \<and> theinvs"
        modifies ancestors, processed, visited, parent
        ensures  "visited \<and> (this \<noteq> root \<longrightarrow> root \<in> ancestors) \<and>
	          (result \<longrightarrow> ancestors = p..ancestors \<union> { p }) \<and> 
	          (\<forall> x. old (x..ancestors) \<noteq> {} \<longrightarrow> 
	          x..ancestors = old (x..ancestors)) \<and>
		  (\<forall> x. x \<noteq> this \<longrightarrow> x..visited = old (x..visited)) \<and>
		  processed = (old processed) \<union> { this } \<and>
		  (result \<longrightarrow> (\<forall> x y. x \<noteq> this \<and> x \<notin> ancestors \<and> x \<in> processed \<and>
		  y \<in> x..neighbors \<longrightarrow> y \<in> processed)) \<and>
		  (\<not> result \<longrightarrow> (\<forall> x y. x \<noteq> p \<and> x \<notin> p..ancestors \<and> 
	          x \<in> processed \<and> y \<in> x..neighbors \<longrightarrow> y \<in> processed)) \<and>
		  root = old root \<and> alloc = old alloc \<and> theinvs"
    */
    {
	if (!visited) {
	    visited = true;
	    parent = p;
	    //: "ancestors" := "p..ancestors \<union> { p }";
	    //: "processed" := "processed \<union> { this }";

	    return true;
	}
	return false;
    }

    private void span(Node p)
    /*: requires "init \<and> p \<noteq> null \<and> p..visited \<and> root..visited \<and>
	          (p \<noteq> root \<longrightarrow> root \<in> p..ancestors) \<and>
                  (\<forall> x y. x \<noteq> p \<and> x \<notin> p..ancestors \<and> x \<in> processed \<and> 
	          y \<in> x..neighbors \<longrightarrow> y \<in> processed) \<and> theinvs"
        modifies "Node.ancestors", "Node.processed",
	         "Node.visited", "Node.parent"
        ensures  "visited \<and> (this \<noteq> root \<longrightarrow> root \<in> ancestors) \<and>
	          this \<in> processed \<and>
	          (\<forall> x. old (x..ancestors) \<noteq> {} \<longrightarrow> 
	          x..ancestors = old (x..ancestors)) \<and> 
		  (\<forall> x. old (x..visited) \<longrightarrow> x..visited) \<and>
		  (\<forall> x. x \<in> (old processed) \<longrightarrow> x \<in> Node.processed) \<and>
	          (\<forall> x y. x \<noteq> p \<and> x \<notin> p..ancestors \<and> x \<in> processed \<and>
	          y \<in> x..neighbors \<longrightarrow> y \<in> processed) \<and> theinvs"
    */
    {
	if (!visit(p)) {
            return;
	}

	int i = 0;
 
	while /*: inv "0 \<le> i \<and> i \<le> numEdges \<and> root \<in> ancestors \<and> visited \<and>
	               this \<in> processed \<and>
		       (\<forall> x. old (x..ancestors) \<noteq> {} \<longrightarrow> 
	               x..ancestors = old (x..ancestors)) \<and> 
		       (\<forall> x. old (x..visited) \<longrightarrow> x..visited) \<and>
		       (\<forall> x. x \<in> old processed \<longrightarrow> x \<in> processed) \<and>  
		       comment ''ProcessedSoFar'' 
	               (\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> edges.[j] \<in> processed) \<and>
		       (\<forall> x y. x \<noteq> this \<and> x \<notin> ancestors \<and> x \<in> processed \<and>
		       y \<in> x..neighbors \<longrightarrow> y \<in> processed) \<and>
		       (ancestors = p..ancestors \<union> { p }) \<and> theinvs"
	       */
	    (i < numEdges()) {
	    edge(i).span(this);
	    i = i + 1;
	}
    }

    private int numEdges()
    /*: requires "init \<and> theinvs"
        ensures  "result = numEdges \<and> theinvs"
    */
    {
	return numEdges;
    }

    private Node edge(int i)
    /*: requires "init \<and> 0 \<le> i \<and> i < numEdges \<and> theinvs"
        ensures "result = edges.[i] \<and> theinvs"
    */
    {
	return edges[i];
    }
}