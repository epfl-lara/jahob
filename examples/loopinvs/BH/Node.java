/**
 * A class that represents the common fields of a cell or body
 * data structure.
 **/
class Node
{
    // subcells per cell
    public static final int NSUB = 8;  // 1 << NDIM
    
    // highest bit of int coord
    static final int IMAX =  1073741824;

    static final boolean CELL = true;
    static final boolean BODY = false;

    // potential softening parameter
    //static final int double EPS = 0.05;

    /**
     * Mass of the node.
     **/
    int mass;

    /**
     * Position of the node
     **/
    MathVector pos;

    public final boolean isCell; // is this a body or cell node?

    /* Cell fields */

    /**
     * The children of this cell node.  Each entry may contain either 
     * another cell or a body.
     **/
    Node[] subp;

    /* Body fields */

    MathVector vel;
    MathVector acc;
    MathVector newAcc;
    int        phi;

    private Node next;
    private Node procNext;

    /**
     * Construct an empty node
     **/
    Node(boolean isCell)
    {
	this.mass = 0;
	this.pos = new MathVector();

	this.isCell = isCell;
	this.subp = new Node[NSUB];

	this.vel      = new MathVector();
	this.acc      = new MathVector();
	this.newAcc   = new MathVector();
	this.phi      = 0;
	this.next     = null;
	this.procNext = null;
    }

    /**
     * Construct an empty node
     **/
    Node()
    {
	this(BODY);
    }

    /**
     * Set the next body in the list.
     * @param n the body
     **/
    final void setNext(Node n)
    /*: requires "n ~= null & ~n..Node.isCell"
        ensures  "True"
    */
    {
	next = n;
    }

    /**
     * Get the next body in the list.
     * @return the next body
     **/
    Node getNext()
    /*: ensures "~result..Node.isCell"
     */
    {
	return next;
    }
    
    /**
     * Set the next body in the list.
     * @param n the body
     **/
    final void setProcNext(Node n)
    /*: requires "~n..Node.isCell"
        ensures  "True"
     */
    {
	procNext = n;
    }

    /**
     * Get the next body in the list.
     * @return the next body
     **/
    Node getProcNext()
    /*: ensures "~result..Node.isCell"
     */
    {
	return procNext;
    }

    final boolean isCell()
    /*: ensures "result = isCell"
     */
    {
	return isCell;
    }

    final int getMass()
    {
	return mass;
    }

    final MathVector getPos()
    {
	return pos;
    }

    /**
     * Enlarge cubical "box", salvaging existing tree structure.
     * @param tree the root of the tree.
     **/
    void expandBox(Tree tr)
    /*: requires "tr..Tree.rsize >= 2"
        ensures  "True"
    */
    {
	boolean inbox = icTest(tr);
	while (!inbox) {
	    int rsize = tr.rsize;
	    
	    MathVector rmid = new MathVector();
	    rmid.addScalar(tr.rmin, rsize/2);
	    
	    if (pos.getX() < rmid.getX()) {
		int rmin = tr.getRMinX();
		tr.setRMinX(rmin - rsize);
	    }
	    
	    if (pos.getY() < rmid.getY()) {
		int rmin = tr.getRMinY();
		tr.setRMinY(rmin - rsize);
	    }
	    
	    if (pos.getZ() < rmid.getZ()) {
		int rmin = tr.getRMinZ();
		tr.setRMinZ(rmin - rsize);
	    }
	    
	    tr.rsize = 2 * rsize;
	  
	    if (tr.root != null) {
		MathVector ic = tr.intcoord(rmid);
		
		//: assert "ic != null";

		int j = oldSubindex(ic, IMAX/2);
		Node newt = new Node(CELL);
		newt.subp[j] = tr.root;
		tr.root = newt;
		inbox = icTest(tr);
	    }
	}
    }

    /**
     * Check the bounds of the body and return true if it isn't in the
     * correct bounds.
     **/
    boolean icTest(Tree tr)
    /*: requires "~this..Node.isCell"
        ensures  "True"
     */
    {
	int pos0 = pos.getX();
	int pos1 = pos.getY();
	int pos2 = pos.getZ();
    
	int txmin = tr.getRMinX();
	int txmax = txmin + tr.rsize;
	if (!(txmin <= pos0 && pos0 < txmax))
	    return false;
	
	int tymin = tr.getRMinY();
	int tymax = tymin + tr.rsize;
	if (!(tymin <= pos1 && pos1 < tymax))
	    return false;
	
	int tzmin = tr.getRMinZ();
	int tzmax = tzmin + tr.rsize;
	if (!(tzmin <= pos2 && pos2 < tzmax))
	    return false;

	return true;
    }

    final void setNodeAt(Node n, int i)
    {
	subp[i] = n;
    }

    /**
     * Descend Tree and insert particle.  If we're at a body,
     * create a cell and attach this body to the cell.
     * @param p the body to insert
     * @param xpic
     * @param l 
     * @param tree the root of the data structure
     * @return the subtree with the new body inserted
     **/
    final Node loadTree(Node p, MathVector xpic, int l, Tree tr)
    /*: requires "~p..Node.isCell"
        ensures  "True"
     */
    {
	if (isCell())
	    return loadTreeAtCell(p, xpic, l, tr);

	// create a Cell
	Node retval = new Node(CELL);
	int si = subindex(tr, l);
	// attach this Body node to the cell
	retval.setNodeAt(this, si);
	
	return retval.loadTreeAtCell(p, xpic, l, tr);
    }

    /**
     * Descend Tree and insert particle.  We're at a cell so 
     * we need to move down the tree.
     * @param p the body to insert into the tree
     * @param xpic
     * @param l
     * @param tree the root of the tree
     * @return the subtree with the new body inserted
     **/
    final Node loadTreeAtCell(Node p, MathVector xpic, int l, Tree tr)
    /*: requires "this..Node.isCell & ~p..Node.isCell"
        ensures  "True"
     */
    {
	// move down one level
	int si = oldSubindex(xpic, l);
	Node rt = subp[si];
	if (rt != null) 
	    subp[si] = rt.loadTree(p, xpic, l/2, tr);
	else 
	    subp[si] = p;
	return this;
    }

    /**
     * Descend tree finding center of mass coordinates
     * @return the mass of this node
     **/
    int hackcofm()
    {
	// if this is a body, then return its mass
	if (!isCell) return mass;

	// this is a cell

	int mq = 0;
	MathVector tmpPos = new MathVector();
	MathVector tmpv   = new MathVector();

	int i = 0;
	
	while (i < NSUB) { // for each subtree
	    Node r = subp[i];
	    if (r != null) {
		int mr = r.hackcofm(); // compute cofm for subtree
		mq = mr + mq;
		tmpv.multArgScalar(r.pos, mr);
		tmpPos.addition(tmpv);
	    }
	    i = i + 1;
	}
	mass = mq;
	pos = tmpPos;
	pos.divScalar(mass);  // result of center of mass calculation
	
	return mq; // return mass of subtree rooted at this node
    }

    /**
     * Evaluate gravitational field on the body.
     * The original olden version calls a routine named "walkscan",
     * but we use the same name that is in the Barnes code.
     **/
    final void hackGravity(int rsize, Node root)
    {
	MathVector pos0 = (MathVector)pos.clone();
	
	HG hg = new HG(this, pos);
	root.walkSubTree(rsize * rsize, hg);
	phi = hg.phi0;
	newAcc = hg.acc0;
    }
    
     /**
     * Recursively walk the tree to do hackwalk calculation
     **/
    void walkSubTree(int dsq, HG hg)
    {
	if (isCell) {
	    
	    if (subdivp(dsq, hg)) {
		int k = 0;
		while (k < NSUB) {
		    Node r = subp[k];
		    if (r != null)
			r.walkSubTree(dsq / 4, hg);
		    k = k + 1;
		}
	    } else {
		gravSub(hg);
	    }
	} else {
	    if (this != hg.pskip)
		gravSub(hg);
	}
    }

    /**
     * Decide if the cell is too close to accept as a single term.
     * @return true if the cell is too close.
     **/
    final boolean subdivp(int dsq, HG hg)
    {
	MathVector dr = new MathVector();
	dr.subtract(pos, hg.pos0);
	int drsq = dr.dotProduct();
	
	// in the original olden version drsp is multiplied by 1.0
	return (drsq < dsq);
    }

    /**
     * Compute a single body-body or body-cell interaction
     **/
    final void gravSub(HG hg)
    {
	MathVector dr = new MathVector();
	dr.subtract(pos, hg.pos0);
	
	//int drsq = dr.dotProduct() + (EPS * EPS);
	int drsq = dr.dotProduct();
	int drabs = Util.sqrt(drsq);
	
	int phii = mass / drabs;
	hg.phi0  = hg.phi0 - phii;
	int mor3 = phii / drsq;
	dr.multScalar(mor3);
	hg.accAdd(dr);
    }

    /**
     * Determine which subcell to select.
     * Combination of intcoord and oldSubindex.
     * @param t the root of the tree
     **/
    final int subindex(Tree tr, int l)
    {
	MathVector xp = new MathVector();
	int f = IMAX / tr.rsize;

	int xsc = pos.getX() - tr.getRMinX();
	xp.setX(xsc * f);
	
	int ysc = pos.getY() - tr.getRMinY();
	xp.setY(ysc * f);
	
	int zsc = pos.getZ() - tr.getRMinZ();
	xp.setZ(zsc * f);

	int i = 0;
	if (xp.getX() > l)
	    i = i + 4;
	
	if (xp.getY() > l)
	    i = i + 2;
	
	if (xp.getZ() > l)
	    i = i + 1;

	return i;
    }

    /* Generates an integer in the interval [0,8)
     */
    static final int oldSubindex(MathVector ic, int l)
    /*: ensures "0 <= result & result < NSUB"
     */
    {
	int i = 0;

	if (ic.getX() > l)
	    i = i + 4;

	if (ic.getY() > l)
	    i = i + 2;

	if (ic.getZ() > l)
	    i = i + 1;

	return i;
    }
    
    /**
     * Return a string representation of a node.
     * @return a string representation of a node.
     **/
    /*
      public String toString()
      {
      return mass + " : " + pos;
      }
    */
}
