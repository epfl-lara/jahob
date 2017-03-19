class Node {    
    private boolean isBody = true;
    private Node next = null;
    private Node subp[] = null;
    private static Node nodes;
    private static Node root;
    private static int si;
    private static int sj;

    /*: private ghost specvar llcontents :: objset = "\<emptyset>";
        private ghost specvar init :: bool = "False";
	private ghost specvar children :: objset = "\<emptyset>";
	private ghost specvar subtree :: objset = "\<emptyset>";

        public static ghost specvar treeinit :: bool = "False";

	public static specvar bodies :: objset;
        private vardefs "bodies == nodes..llcontents";

	public static specvar treecontents :: objset;
	vardefs "treecontents == root..subtree";

        invariant LLContentsDefBCInv: 
	"init \<and> this \<noteq> null \<and> next = null \<longrightarrow> llcontents = {this}";

	invariant LLContentsDefRCInv:
	"init \<and> this \<noteq> null \<and> next \<noteq> null \<longrightarrow>
          (llcontents = next..llcontents \<union> {this} \<and> this \<notin> next..llcontents)";

	invariant LLContentsDefNullInv:	"null..llcontents = \<emptyset>";

	invariant NodesPropInv: 
	"nodes \<noteq> null \<longrightarrow> nodes \<in> alloc \<and> nodes \<in> Node \<and> nodes..init \<and> nodes..isBody";

	invariant LLContentsPropInv: 
	"\<forall> x. x \<in> bodies \<longrightarrow> x \<in> Node \<and> x \<in> alloc \<and> x..init \<and> x..isBody";

	invariant LLContentsBodiesRecInv:
	"\<forall> x. this \<in> bodies \<and> x \<in> llcontents \<longrightarrow> x \<in> bodies";

	invariant ChildrenDefBCInv: "isBody \<longrightarrow> children = \<emptyset>";

	invariant ChildrenDefRCInv:
	"\<not> isBody \<longrightarrow> children = {c. \<exists> i. 0 \<le> i \<and> i < 8 \<and> c = subp.[i] \<and> c \<noteq> null}";

	invariant SubtreeDefBCInv: "isBody \<and> init \<longrightarrow> subtree = {this}";

	invariant SubtreeDefRCInv:
	"\<not> isBody \<and> init \<longrightarrow> subtree = {s. \<exists> c. c \<in> children \<and> s \<in> c..subtree}";

	invariant SubtreeDefNullInv: "null..subtree = {}";

	invariant CellBodyInv: "isBody = (subp = null)";
      
	invariant SubpBoundsInv: "subp \<noteq> null \<longrightarrow> subp..Array.length = 8";

	invariant SubpInjInv: 
	"\<forall> m n. m..subp = n..subp \<and> m..subp \<noteq> null \<longrightarrow> m = n";

	invariant LLContentsBCInv:
	"init \<and> next = null \<longrightarrow> llcontents = {this}";

	invariant LLContentsRCInv:
	"init \<and> next \<noteq> null \<longrightarrow>
         llcontents = {this} \<union> next..llcontents \<and> this \<notin> next..llcontents";

	invariant NextInitInv:
	"\<forall> x y. x = y..next \<and> x \<noteq> null \<longrightarrow> x..init \<and> x \<in> alloc";

	invariant IndexInBounds: "0 \<le> si \<and> si < 8 \<and> 0 \<le> sj \<and> sj < 8";

	invariant SubpElemInjInv:
	"\<forall> x y i j. x \<in> alloc \<and> x \<in> Node \<and> y \<in> alloc \<and> y \<in> Node \<and> 
         x..subp.[i] = y..subp.[j] \<and> x..subp.[i] \<noteq> null \<longrightarrow> x = y \<and> i = j";

        invariant SubpElemsInv: 
        "\<forall> x y i. x = y..subp.[i] \<and> x \<noteq> null \<longrightarrow> 
         x \<in> Node \<and> x \<noteq> y \<and> x..init \<and> x \<noteq> root";

	invariant RootInitInv: "root \<noteq> null \<longrightarrow> root..init";

        invariant HiddenInv: "subp \<noteq> null \<longrightarrow> subp : hidden";

        invariant TreeInitInv: 
        "\<not> treeinit \<longrightarrow> (\<forall> x y i. x \<in> bodies \<longrightarrow> y..subp.[i] \<noteq> x)";
    */

    private static Node makeCell()
    /*: modifies "new..children", "new..subtree", "new..llcontents", "new..init", 
                 "new..subp", "new..isBody"
        ensures  "\<not> result..isBody \<and> result..init \<and> result..subp \<noteq> null \<and>
                 result..llcontents = { result } \<and> result..children = \<emptyset> \<and> 
                 result..subtree = \<emptyset> \<and> result : hidden \<and>
                 result \<notin> old alloc \<and> result..subp \<notin> old alloc \<and> 
                 alloc = old alloc \<union> {result, result..subp} \<and> 
                 (\<forall> i. result..subp.[i] = null) \<and> root = old root \<and>
                 (\<forall> x. x \<noteq> result \<longrightarrow> x..subtree = old (x..subtree) \<and> 
                 x..children = old (x..children) \<and> 
                 x..llcontents = old (x..llcontents) \<and> x..init = old (x..init) \<and>
                 x..subp = old (x..subp) \<and> x..isBody = old (x..isBody))" */
    {
	Node n = new /*: hidden */ Node();
	n.isBody = false;
	n.subp = new /*: hidden */ Node[8];
        n.next = null;

	//: "n..Node.init" := "True";
	//: "n..Node.llcontents" := "{ n }";
        //: "n..Node.children" := "\<emptyset>";
	//: "n..Node.subtree" := "\<emptyset>";

	return n;
    }
    
    private Node getNext()
    /*: ensures "result = next \<and> nodes = old nodes \<and> arrayState = old arrayState \<and> 
	         Node.subp = old Node.subp \<and> alloc = old alloc" */
    {
	return next;
    }

    public static void makeTree()
    /*: requires "treecontents = \<emptyset> \<and> \<not> treeinit"
        modifies treeinit, treecontents
        ensures "treecontents = bodies \<and> treeinit"
    */
    {
	//: ghost specvar p :: obj = "null";
	Node n = nodes;

        //: treeinit := "True";
	while 
	    /*: inv "(comment ''StartLoop'' (p = null \<longrightarrow> treecontents = \<emptyset>)) \<and>
		     (comment ''PNRel'' (p = null) = (n = nodes)) &
	             (n \<noteq> null \<longrightarrow> n \<in> bodies) \<and>
	             (comment ''NProps'' 
                     (n \<noteq> null \<longrightarrow> n \<in> Node \<and> n \<in> alloc \<and> n..init \<and> n..isBody)) \<and>
                     (\<forall> x y i. x \<in> n..llcontents \<longrightarrow> y..subp.[i] \<noteq> x) \<and>
	             (comment ''ElemProps'' 
		     (\<forall> x. x \<in> n..llcontents \<longrightarrow> (x \<in> Node \<and> x \<in> alloc \<and> x..isBody \<and> 
		     x..init \<and> x \<notin> treecontents))) \<and>
		     (p \<noteq> null \<longrightarrow> n \<noteq> p \<and> n = p..next \<and> 
                     treecontents = bodies \<setminus> n..llcontents) \<and> 
		     (bodies = old bodies) \<and> (nodes = old nodes) \<and> 
                     (\<forall> x i. x \<notin> hidden \<longrightarrow> x.[i] = old (x.[i])) \<and> theinvs" */
	    (n != null) {
	    
	    n.addToTree();

	    //: p := "n";
	    n = n.getNext();
	}
    }

    private void setRoot()
    /*: modifies root, treecontents
        ensures "root = this \<and> treecontents = subtree \<and> alloc = old alloc" */
    {
	root = this;
    }

    private void addToTree()
    /*: requires "init \<and> treeinit \<and> isBody \<and> (this \<notin> treecontents) \<and> 
	          (\<forall> x i. x..subp.[i] \<noteq> this) \<and> theinvs"
        modifies "treecontents", "root", "Node.subtree", "Node.children",
	         arrayState, "Node.llcontents", "Node.init",
		 "Node.isBody", "Node.subp"
        ensures  "treecontents = old treecontents \<union> { this } \<and> 
		  (comment ''NotPointedToPost''
		  (\<forall> x. (x \<in> old alloc \<and> x \<noteq> null \<and> x \<noteq> this \<and> x \<noteq> old root \<and>
		  (\<forall> y i. old (y..subp.[i]) \<noteq> x)) \<longrightarrow> (\<forall> z j. z..subp.[j] \<noteq> x))) \<and>
		  (\<forall> x. x \<in> old alloc \<longrightarrow> x..llcontents = old (x..llcontents) \<and> 
	          x..init = old (x..init) \<and> x..isBody = old (x..isBody)) \<and> 
                  (\<forall> x i. x \<notin> hidden \<longrightarrow> x.[i] = old (x.[i])) \<and> theinvs"
    */
    {
	if (root == null) {
            setRoot();
	    return;
	}

	if (root.isBody) {
	    Node m = root;
	    root = makeCell();

	    root.subp[si] = m;
	    //: "root..children" := "root..children \<union> { m }";
	    //: "root..subtree" := "m..subtree \<union> { this }";
	} else {
	    //: "root..subtree" := "root..subtree \<union> { this }";
	}
	root.loadTree(this);
    }	


    private void loadTree(Node toLoad)
    /*: requires "init \<and> treeinit \<and> \<not> isBody \<and> (toLoad \<noteq> null) \<and> (toLoad \<noteq> root) \<and>
	          (\<forall> x i. x..Node.subp.[i] \<noteq> toLoad) \<and> toLoad..isBody \<and> toLoad..init \<and>
                  (theinv LLContentsDefBCInv) \<and> (theinv LLContentsDefRCInv) \<and>
		  (theinv LLContentsDefNullInv) \<and> (theinv NodesPropInv) \<and>
		  (theinv LLContentsPropInv) \<and> (theinv LLContentsBodiesRecInv) \<and>
		  (theinv ChildrenDefBCInv) \<and> (theinv ChildrenDefRCInv) \<and>
		  (theinv SubtreeDefBCInv) \<and> 
		  (comment ''SubtreeDefRCOther''
		  (\<forall> x. x \<in> alloc \<and> x \<in> Node \<and> x \<noteq> this \<and> \<not> x..isBody \<and> x..init \<longrightarrow>  
		   x..subtree = 
		  { s. (\<exists> c. (c \<in> x..children \<and> s \<in> c..subtree))})) \<and>
		  (comment ''SubtreeDefRCThis''
		  (subtree = 
		  { s. (\<exists> c. (c \<in> children \<and> s \<in> c..subtree))} \<union> { toLoad })) \<and> 
		  (theinv SubtreeDefNullInv) \<and> (theinv CellBodyInv) \<and> 
		  (theinv SubpBoundsInv) \<and> (theinv SubpInjInv) \<and>
		  (theinv LLContentsBCInv) \<and> (theinv LLContentsRCInv) \<and> 
		  (theinv NextInitInv) \<and> (theinv IndexInBounds) \<and> 
		  (theinv SubpElemInjInv) \<and> (theinv SubpElemsInv) \<and>
	          (theinv RootInitInv) \<and> (theinv HiddenInv) \<and> (theinv TreeInitInv)"
	 modifies "Node.children", arrayState, "Node.subtree",
	          "Node.subp", "Node.isBody", "Node.llcontents", "Node.init"
	 ensures  "theinvs \<and> nodes = old nodes \<and> bodies = old bodies \<and> 
		  (treecontents = old treecontents) \<and>
		  (comment ''NotPointedToPost''
		  (\<forall> x. (x \<in> old alloc \<and> x \<noteq> null \<and> x \<noteq> toLoad \<and> 
		  (\<forall> y i. old (y..subp.[i]) \<noteq> x)) \<longrightarrow> (\<forall> z j. z..subp.[j] \<noteq> x))) \<and>
		  (\<forall> x. x \<in> old alloc \<longrightarrow> x..llcontents = old (x..llcontents) \<and> 
	          x..init = old (x..init) \<and> x..isBody = old (x..isBody) \<and>
	          x..subp = old (x..subp)) \<and> 
	          (\<forall> x i. x \<notin> hidden \<longrightarrow> x.[i] = old (x.[i]))" */
    {
	Node n = subp[si];

	if (n == null) {
	    subp[si] = toLoad;
	    //: "children" := "children \<union> { toLoad }";

	    return;
	}

	if (n.isBody) {
	    Node m = makeCell();

	    //: noteThat SubpNotNode: "m..subp \<notin> Node";
	    //: noteThat MNotChild: "\<forall> x. x \<in> alloc \<and> x \<in> Node \<longrightarrow> m \<notin> x..children";

	    m.subp[sj] = n;
	    //: "m..children" := "m..children \<union> { n }";
	    //: "m..subtree" := "n..subtree \<union> { toLoad }";

	    subp[si] = m;
	    //: "children" := "(children \<setminus> { n }) \<union> { m }";


	    /*: noteThat NewThisChildren: "children = 
	        { c. (\<exists> i. 0 \<le> i \<and> i < 8 \<and> c = subp.[i] \<and> c \<noteq> null) }"; */
	    /*: noteThat MChildren: "m..children = 
	        { c. (\<exists> i. 0 \<le> i \<and> i < 8 \<and> c = m..subp.[i] \<and> c \<noteq> null) }"; */
	    /*: noteThat OtherChildren: "\<forall> x. x \<noteq> this \<and> x \<noteq> m \<and> x \<in> alloc \<and> 
	        x \<in> Node \<and> \<not> x..isBody \<longrightarrow> x..children =
	        { c. (\<exists> i. 0 \<le> i \<and> i < 8 \<and> c = x..subp.[i] \<and> c \<noteq> null) }"; */
	    /*: noteThat ChildrenLemma: "theinv ChildrenDefRCInv"
	        from NewThisChildren, OtherChildren, MChildren, ChildrenLemma; */

	    m.loadTree(toLoad);
	} else {
	    //: "n..subtree" := "n..subtree \<union>  { toLoad }";
	    n.loadTree(toLoad);
	}	    
    }
}
