class Node {
    
    boolean isBody = true;

    int xPos;
    int yPos;
    int zPos;

    int mass;

    Node next;

    Node subp[] = null;

    // Tree properties

    static int lowerX;
    static int lowerY;
    static int lowerZ;
    
    static int rsize = 2;

    public static Node nodes;
    static Node root;

    static final int IMAX = 1073741824;


    /*: public ghost specvar llcontents :: objset = "{}";
        public ghost specvar init :: bool = "False";
	public ghost specvar children :: objset = "{}";
	public ghost specvar subtree :: objset = "{}";

        invariant LLContentsDefBCInv: 
	"init & this ~= null & next = null --> llcontents = { this }";

	invariant LLContentsDefRCInv:
	"init & this ~= null & next ~= null --> 
	llcontents = next..Node.llcontents Un { this }";
	
	invariant ChildrenDefBCInv:
	"isBody --> children = {}";

	invariant ChildrenDefRCInv:
	"~isBody --> children = 
	{ c. (EX i. 0 <= i & i < 8 & c = subp.[i] & c ~= null) }";

	invariant SubtreeDefBCInv:
	"isBody & init --> subtree = { this }";

	invariant SubtreeDefRCInv:
	"~isBody & init --> 
	subtree = { s. (EX c. c : children & s : c..Node.subtree) }";

	invariant SubtreeDefNullInv:
	"ALL x. x = null --> x..Node.subtree = {}";

	invariant CellBodyInv: "isBody = (subp = null)";
      
	invariant SubpBoundsInv: "subp ~= null --> subp..Array.length = 8";

	invariant SubpInjInv: 
	"ALL m n. m..Node.subp = n..Node.subp & m..Node.subp ~= null --> m = n";

	invariant ConstsInv: "NSUB = 8 & IMAX = 1073741824";

	invariant RSizeInvs: "rsize > 0 & (EX x. rsize = 2 * x)";

	invariant LLContentsBCInv:
	"init & next = null --> llcontents = { this }";

	invariant LLContentsRCInv:
	"(init & next ~= null) --> 
	((llcontents = { this } Un next..Node.llcontents) & 
	(this ~: next..Node.llcontents))";

	invariant NextInitInv:
	"ALL x y. x = y..Node.next & x ~= null --> 
	x..Node.init & x : Object.alloc";
	
    */

    /*: public static specvar bodies :: objset;
        private vardefs "bodies == nodes..Node.llcontents";

	public static specvar treecontents :: objset;
	vardefs "treecontents == root..Node.subtree";

    */

    /*  public specvar children :: objset = "{}";
	vardefs "children == 
	{ c. EX i. 0 <= i & i < 8 & subp ~= null & c = subp.[i] }";


	invariant SubpUniqueInv: "ALL i j. subp.[i] = subp.[j] --> i = j";

	invariant SubpAllocInv: "subp : Object.alloc";

	invariant SubtreeDefBCInv:
	"init & isBody --> subtree = { this }";
	
	invariant SubtreeDefRCInv:
	"init & ~isBody --> 
	subtree = { c. (EX i. 0 <= i & i < 8 & subp.[i] ~= null & 
	c : subp.[i]..Node.subtree) }";

	invariant SubpTreeAcyclicInv: 
	"ALL i. 0 <= i & i < 8 --> this ~: subp.[i]..Node.subtree";

	invariant SubpTreeDisjointInv:
	"ALL i j x. 0 <= i & i < 8 & 0 <= j & j < 8 & 
	x : subp.[i]..Node.subtree & x : subp.[j]..Node.subtree --> i = j";

    */
    
    public static Node makeCell()
    /*: modifies "Array.arrayState"
        ensures "~result..Node.isBody & result..Node.init &
	         (ALL i. 0 <= i & i < 8 --> result..Node.subp.[i] = null) &
		 root = (old root)"
    */
    {
	Node n = new Node();
	n.isBody = false;
	n.subp = new Node[8];
	n.next = null;

	//: "n..Node.init" := "True";
	//: "n..Node.llcontents" := "{ n }";
	//: "n..Node.children" := "{}";
	//: "n..Node.subtree" := "{}";

	return n;
    }
    
    Node setSubp(int i, Node m)
    /* requires "0 <= i & i < 8 & ~isBody & m ~: children"
        modifies "Node.subp", "Array.arrayState", "Node.children"
        ensures "children = ((old children) - {result}) Un {m}"
     */
    /*: requires "0 <= i & i < 8 & ~isBody & 
                 (ALL j. 0 <= j & j < 8 & j ~= i --> subp.[j] ~= m)"
        modifies "Node.subp", "Array.arrayState", "Node.subtree", 
	         "Node.children"
        ensures "subp.[i] = m & 
	         result = (arrayRead (old Array.arrayState) subp i)"
	         
     */
    {
	Node n = subp[i];
	subp[i] = m;

	//: "children" := "(children - {n}) Un {m}";
	//: "subtree" := "(subtree - n..Node.subtree) Un (m..Node.subtree) ";

	//: noteThat ChildrenLHS: "children = ((old children) - {n}) Un {m}";
	/*: noteThat ThisChildren:
	  "children = 
	  { c. (EX i. 0 <= i & i < 8 & c = subp.[i] & c ~= null) }"
	  from ThisChildren, ChildrenLHS;
	*/
	//: assume "False";
	return n;
    }

    private int getMass()
    /*: requires "theinvs"
        ensures "result = mass & theinvs & 
	         (bodies = old bodies) & (nodes = old nodes)"
    */
    {
	return mass;
    }

    private Node getNext()
    /*: requires "theinvs"
        ensures "result = next & theinvs & (bodies = old bodies)";
     */
    {
	return next;
    }

    private Node getSubp(int i)
    /*: requires "0 <= i & i < 8 & ~isBody & theinvs"
        ensures "result = subp.[i] & theinvs"
    */
    {
	return subp[i];
    }

    int getXPos()
    /*: ensures "result = xPos"
     */
    {
	return xPos;
    }

    int getYPos()
    /*: ensures "result = yPos"
     */ 
    {
	return yPos;
    }

    int getZPos()
    /*: ensures "result = zPos"
     */
    {
	return zPos;
    }

    private void setMass(int m)
    /*: requires "theinvs"
        modifies "Node.mass"
        ensures "mass = m & theinvs"
     */
    {
	mass = m;
    }

    void setPos(int a, int b, int c)
    /*: modifies "Node.xPos", "Node.yPos", "Node.zPos"
        ensures "xPos = a & yPos = b & zPos = c"
     */
    {
	this.xPos = a;
	this.yPos = b;
	this.zPos = c;
    }

    public static void makeTree()
    /*: requires "treecontents = {}"
        ensures "treecontents = bodies"
    */
    {
	//: ghost specvar p :: obj;
	Node n = nodes;

	//: p := "null";

	while 
	    /*: inv "(p = null --> treecontents = {}) &
	             (comment ''ProcessedLoop'' (p ~= null --> 
		      treecontents = (bodies \<setminus> n..Node.llcontents))) &
		     (bodies = old bodies) & (nodes = old nodes) &
		     theinvs" */
	    (n != null) {

	    if (n.mass != 0) {
		n.expandBox();
		n.addToTree();
	    }

	    //: p := "n";
	    n = n.next;
	}
	
	if (root != null) root.computeCofM();
    }

    public int computeCofM()
    {
	if (isBody) return mass;
	
	int mq = 0;
	int i = 0;
	int xt = 0;
	int yt = 0;
	int zt = 0;

	while (i < 8) {
	    Node r = getSubp(i);
	    int mr = r.computeCofM();
	    mq = mq + mr;
	    xt = xt + mr * r.getXPos();
	    yt = yt + mr * r.getYPos();
	    zt = zt + mr * r.getZPos();

	    i = i + 1;
	}

	xt = xt / mq;
	yt = yt / mq;
	zt = zt / mq;

	setMass(mq);
	setPos(xt, yt, zt);
	return mq;
    }

    public void expandBox()
    /*: modifies "Node.children", "Node.root"
        ensures "lowerX <= xPos & lowerY <= yPos & lowerZ <= zPos &
                 xPos < (lowerX + rsize) & yPos < (lowerY + rsize) &
		 zPos < (lowerZ + rsize) & (bodies = old bodies) &
		 (nodes = old nodes)"
    */
    {
	// In the original olden implementation, the loop exit
	// condition is only updated if there is an existing tree
	// (even if the tree is resized), which can potentially cause
	// an infinite loop if the first node to be inserted into the
	// tree is outside of the original box.

	while
	    /*: inv "theinvs & (bodies = old bodies)";
	     */
	    (!inBox()) {
	    resizeBox();
	}	
    }

    private void addToTree()
    /*: requires "init & isBody & (this ~: treecontents) & theinvs"
        modifies "treecontents", "root"
        ensures  "treecontents = (old treecontents) Un { this } & 
	          theinvs &
		  (nodes = old nodes) & (bodies = old bodies)"
     */
    {
	int f = 1073741824/rsize;
	int xsc = (xPos - lowerX) * f;
	int ysc = (yPos - lowerY) * f;
	int zsc = (zPos - lowerZ) * f;

	if (root == null) {
	    root = this;
	    return;
	}

	if (root.isBody) {

	    Node m = root;
	    root = Node.makeCell();
	    int si = m.subindex(1073741824/2);
	    root.setSubp(si, m);
	}

	root.loadTree(this, xsc, ysc, zsc, 1073741824/2);
    }

    private void loadTree(Node toLoad, int xsc, int ysc, int zsc, int l)
    /*: requires "init & ~isBody & (toLoad ~: children) &
                  (theinv LLContentsDefBCInv) &
		  (theinv LLContentsDefRCInv) &
		  (theinv ChildrenDefBCInv) &
		  (theinv ChildrenDefRCInv) &
		  (theinv SubtreeDefBCInv) &
		  (ALL x. x : Object.alloc & x : Node & x ~= this & 
		   ~x..Node.isBody & x..Node.init --> 
		   x..Node.subtree = 
		   { s. (EX c. c : x..Node.children & s : c..Node.subtree) }) &
		  (subtree = 
		   { s. (EX c. c : children & s : subtree) } Un { toLoad }) &
		  (theinv SubtreeDefRCInv) &
		  (theinv SubtreeDefNullInv) &
		  (theinv CellBodyInv) &
		  (theinv SubpBoundsInv) &
		  (theinv SubpInjInv) &
		  (theinv ConstsInv) &
		  (theinv RSizeInvs) &
		  (theinv LLContentsBCInv) &
		  (theinv LLContentsRCInv) &
		  (theinv NextInitInv)"
	 ensures  "theinvs &
		  (nodes = old nodes) & (bodies = old bodies)"
    */
    {
	// don't run out of bits
	// assert "l ~= 0";

	int si = oldSubindex(xsc, ysc, zsc, l);
	Node n = getSubp(si);

	if (n == null) {
	    subp[si] = toLoad;
	    //: "children" := "children Un { toLoad }";

	    /*: noteThat ThisChildren:
	      "children = 
	      { c. (EX i. 0 <= i & i < 8 & c = subp.[i] & c ~= null) }";
	    */
	    //: assume "False";
	    return;
	}

	//: assume "False";

	if (n.isBody) {
	    Node m = Node.makeCell();
	    int sj = n.subindex(l/2);
	    m.subp[sj] = n;
	    subp[si] = m;
	    n = m;
	}

	n.loadTree(toLoad, xsc, ysc, zsc, l/2);
    }

    public int subindex(int l)
    /*: requires "lowerX <= xPos & xPos < rsize + lowerY <= yPos & lowerZ <= zPos"
        ensures "0 <= result & result < 8"
     */
    {
	int f = 1073741824/rsize;
	int xsc = (xPos - lowerX) * f;
	int ysc = (yPos - lowerY) * f;
	int zsc = (zPos - lowerZ) * f;

	// assert "0 <= xsc & xsc < 1073741824";
	// assert "0 <= ysc & ysc < 1073741824";
	// assert "0 <= zsc & zsc < 1073741824";
	
	return oldSubindex(xsc, ysc, zsc, l);
    }

    private void resizeBox()
    /*: requires "theinvs"
        modifies "Node.root", "Node.children"
        ensures "theinvs"
     */ 
    {
	int midX = lowerX + rsize/2;
	int midY = lowerY + rsize/2;
	int midZ = lowerZ + rsize/2;

	// is p left of mid?
	if (xPos < midX)
	    lowerX = lowerX - rsize;

	if (yPos < midY)
	    lowerY = lowerY - rsize;

	if (zPos < midZ)
	    lowerZ = lowerZ - rsize;

	rsize = 2 * rsize; // double length of box

	if (root != null) { // repot existing tree?
	
	    //: assert "lowerX <= midX & midX < lowerX + rsize";
	    //: assert "lowerY <= midY & midY < lowerY + rsize";
	    //: assert "lowerZ <= midZ & midZ < lowerZ + rsize";
	    
	    // locate old root cell
	    int f = 1073741824/rsize;
	    int xsc = (midX - lowerX) * f;
	    int ysc = (midY - lowerY) * f;
	    int zsc = (midZ - lowerZ) * f;
	    
	    //: assert "0 <= xsc & xsc < 1073741824";
	    //: assert "0 <= ysc & ysc < 1073741824";
	    //: assert "0 <= zsc & zsc < 1073741824";

	    int i = oldSubindex(xsc, ysc, zsc, 1073741824/2); // find old tree index
	    Node m = Node.makeCell();
	    m.setSubp(i, root);                 // graft old on new
	    root = m;                           // plant new tree
	}
    }

    /* Generates an index in the interval [0,8). If we consider that
     * the space is a cube divided into 8 subcubes, then the index of
     * each subcube is a triple (x0, y0, z0) where each component can
     * be either 0 or 1. The index returned is 4 * x0 + 2 * y0 + z0
     * where (x0, y0, z0) indicates the subcube in which (x, y, z) is
     * located.
     */
    public static int oldSubindex(int xp, int yp, int zp, int l)
    /*: ensures  "0 <= result & result < 8 & root = (old root)"
     */
    {
	int i = 0;

	if (xp > l) i = i + 4;
	if (yp > l) i = i + 2;
	if (zp > l) i = i + 1;

	return i;
    }

    public boolean inBox()
    /*: ensures "result = 
      (lowerX <= xPos & xPos < (lowerX + rsize) &
       lowerY <= yPos & yPos < (lowerY + rsize) &
       lowerZ <= zPos & zPos < (lowerZ + rsize)) & (bodies = old bodies)"
    */
    {
	if (!(lowerX <= xPos && xPos < (lowerX + rsize)))
	    return false;

	if (!(lowerY <= yPos && yPos < (lowerY + rsize)))
	    return false;

	if (!(lowerZ <= zPos && zPos < (lowerZ + rsize)))
	    return false;

	return true;
    }

    /* Previous, Java Olden-esque versions of addToTree and loadTree
 
    private void addToTree(Node n)
    {
	int f = 1073741824/rsize;
	int xsc = (n.xPos - lowerX) * f;
	int ysc = (n.yPos - lowerY) * f;
	int zsc = (n.zPos - lowerZ) * f;

	root = loadTree(root, n, xsc, ysc, zsc, 1073741824/2);
    }

    private Node loadTree
	(Node toLoad, Node loadAt, int xsc, int ysc, int zsc, int l)
    {
	if (loadAt == null) return toLoad;

	int si;

	// don't run out of bits
	//: assert "l ~= 0";

	Node m = loadAt;

	if (m.isBody) { // reached a leaf?

	    Node n = makeCell();
	    si = subindex(m.xPos, m.yPos, m.zPos, l);
	    n.setSubp(si, m); // put body in cell
	    m = n; // link cell in tree
	}
	
	si = oldSubindex(xsc, ysc, zsc, l); // move down one level
	Node rt = m.getSubp(si);
	Node n = loadTree(toLoad, rt, xsc, ysc, zsc, l/2);
	m.setSubp(si, n);
	return m;
    }
    */

}