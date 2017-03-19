
import java.util.Enumeration;

/**
 * A class that represents the root of the data structure used
 * to represent the N-bodies in the Barnes-Hut algorithm.
 **/
class Tree
{
  MathVector rmin;
  int        rsize;
  /**
   * A reference to the root node.
   **/
  Node       root;
  /**
   * The complete list of bodies that have been created.
   **/
  private Node       bodyTab;
  /**
   * The complete list of bodies that have been created - in reverse.
   **/
  private Node       bodyTabRev;
  
  /**
   * Construct the root of the data structure that represents the N-bodies.
   **/
  Tree()
  {
    rmin       = new MathVector();
    rsize      = -2 * -2;
    root       = null;
    bodyTab    = null;
    bodyTabRev = null;

    rmin.setX(-2);
    rmin.setY(-2);
    rmin.setZ(-2);
  }
  
  final int getRMinX()
  {
      return rmin.getX();
  }

  final int getRMinY()
  {
      return rmin.getY();
  }

  final int getRMinZ()
  {
      return rmin.getZ();
  }

  final void setRMinX(int i)
  {
      rmin.setX(i);
  }

  final void setRMinY(int i)
  {
      rmin.setY(i);
  }

  final void setRMinZ(int i)
  {
      rmin.setZ(i);
  }

  /**
   * Return an enumeration of the bodies.
   * @return an enumeration of the bodies.
   **/
  final Node getFirst()
  {
    return bodyTab;
  }

  /**
   * Return an enumeration of the bodies - in reverse.
   * @return an enumeration of the bodies - in reverse.
   **/
  final Node getLast()
  {
    return bodyTabRev;
  }

  /**
   * Create the testdata used in the benchmark.
   * @param nbody the number of bodies to create
   **/
  final void createTestData(int nbody)
  {
    MathVector cmr = new MathVector();
    MathVector cmv = new MathVector();

    Node head = new Node();
    Node prev = head;

    //double rsc  = 3.0 * MATH.PI / 16.0;
    //double vsc  = Math.sqrt(1.0 / rsc);
    int vsc = Util.sqrt(16/(3 * 3));
    int seed = 123;

    int i = 0;

    while (i < nbody) {
      Node p = new Node();

      prev.setNext(p);
      prev = p;
      p.mass = 1 / nbody;
      
      seed      = BH.myRand(seed);
      
      /* DEAD CODE: r is not used until after it is recomputed within
       * the loop.  Since NDIM is a constant, the loop body is always
       * exercised first.

	 double t1 = BH.xRand(0.0, 0.999, seed);
	 t1        = Math.pow(t1, (-2.0/3.0)) - 1.0;
	 double r  = 1.0 / Math.sqrt(t1);
      */
      
      int r = BH.myRand(seed);

      int coeff = 4;

      seed = BH.myRand(seed);
      //r = BH.xRand(0.0, 0.999, seed);
      r = BH.xRand(0, 100, seed);
      p.pos.setX(coeff * r);

      seed = BH.myRand(seed);
      //r = BH.xRand(0.0, 0.999, seed);
      r = BH.xRand(0, 100, seed);
      p.pos.setY(coeff * r);

      seed = BH.myRand(seed);
      //r = BH.xRand(0.0, 0.999, seed);
      r = BH.xRand(0, 100, seed);
      p.pos.setZ(coeff * r);
      
      cmr.addition(p.pos);

      int x, y;
      do {
	seed = BH.myRand(seed);
	//x    = BH.xRand(0.0, 1.0, seed);
	x    = BH.xRand(0, 100, seed);
	seed = BH.myRand(seed);
	//y    = BH.xRand(0, 0.1, seed);
	y    = BH.xRand(0, 10, seed);
      //} while (y > x*x * Math.pow(1.0 - x*x, 3.5));
      } while (y > x*x*(10000 - x*x)*(1000 - x*x)*(1000 - x*x)*(1000 - x * x));
      
      //double v = Math.sqrt(2.0) * x / Math.pow(1 + r*r, 0.25);
      int v = Util.sqrt(2) * x / Util.sqrt(Util.sqrt(1 + r * r));

      int rad = vsc * v;
      int rsq;
      do {
	  
	  seed = BH.myRand(seed);
	  //p.vel.setValue(k, BH.xRand(-1.0, 1.0, seed));	  
	  p.vel.setX(BH.xRand(-100, 100, seed));

	  seed = BH.myRand(seed);
	  //p.vel.setValue(k, BH.xRand(-1.0, 1.0, seed));	  
	  p.vel.setY(BH.xRand(-100, 100, seed));

	  seed = BH.myRand(seed);
	  //p.vel.setValue(k, BH.xRand(-1.0, 1.0, seed));	  
	  p.vel.setZ(BH.xRand(-100, 100, seed));
	  
	  rsq = p.vel.dotProduct();

      } while (rsq > 1);

      int rsc1 = rad / Util.sqrt(rsq);
      p.vel.multScalar(rsc1);
      cmv.addition(p.vel);

      i = i + 1;
    }

    // mark end of list
    prev.setNext(null);
    // toss the dummy node at the beginning and set a reference to the first element
    bodyTab = head.getNext();

    cmr.divScalar(nbody);
    cmv.divScalar(nbody);

    prev = null;
    
    Node b = bodyTab;

    while (b != null) {
      b.pos.subtraction(cmr);
      b.vel.subtraction(cmv);
      b.setProcNext(prev);
      prev = b;
      b = b.getNext();
    }
    
    // set the reference to the last element
    bodyTabRev = prev;
  }


  /**
   * Advance the N-body system one time-step.
   * @param nstep the current time step
   **/
  void stepSystem(int nstep)
  {
    // free the tree
    root = null;

    makeTree(nstep);

    Node b = bodyTabRev;

    // compute the gravity for all the particles
    while (b != null) {
      b.hackGravity(rsize, root);
      b = b.getProcNext();
    }

    vp(bodyTabRev, nstep);

  }
    
  private void setRoot(Node r)
  {
      root = r;
  }

  private void addToTree(Node q)
  /*: requires "q ~= null"
      ensures  "True"
   */
  /*  ensures "treeContents = (old treeContents) Un { q }"
  */
  {
      if (root == null) {
	  setRoot(q);
      } else {
	  MathVector xqic = intcoord(q.getPos());
	  Node r = root.loadTree(q, xqic, Node.IMAX/2, this);
	  setRoot(r);
      }
  }

  /**
   * Initialize the tree structure for hack force calculation.
   * @param nsteps the current time step
   **/
  private void makeTree(int nstep)
  {
      Node q = getLast();
      
      while (q != null) {
	  if (q.getMass() != 0) {
	      q.expandBox(this);
      	      addToTree(q);
	  }
	  q = q.getProcNext();
      }
      root.hackcofm(); // compute cofm for all nodes recursively
  }

  /**
   * Compute integerized coordinates.
   * @return the coordinates or null if rp is out of bounds
   **/
  final MathVector intcoord(MathVector vp)
  {
      MathVector xp = new MathVector();
      int f = Node.IMAX/rsize;
    
      int xsc = vp.getX() - rmin.getX();
      if (0 <= xsc && xsc < rsize) {
	  xp.setX(xsc * f);
      } else {
	  return null;
      }

      int ysc = vp.getY() - rmin.getY();
      if (0 <= ysc && ysc < rsize) {
	  xp.setY(ysc * f);
      } else {
	  return null;
      }

      int zsc = vp.getZ() - rmin.getZ();
      if (0 <= zsc && zsc < rsize) {
	  xp.setZ(zsc * f);
      } else {
	  return null;
      }
      return xp;
  }

  static final private void vp(Node b, int nstep)
  {
      MathVector dacc = new MathVector();
      MathVector dvel = new MathVector();
      int dthf = BH.DTIME / 2;
      
      Node p = b;
      while (p != null) {
	  MathVector acc1 = (MathVector)b.newAcc.clone();
	  if (nstep > 0) {
	      dacc.subtract(acc1, b.acc);
	      dvel.multArgScalar(dacc, dthf);
	      dvel.addition(b.vel);
	      b.vel = (MathVector)dvel.clone();
	  }
	  b.acc = (MathVector)acc1.clone();
	  dvel.multArgScalar(b.acc, dthf);
	  
	  MathVector vel1 = (MathVector)b.vel.clone();
	  vel1.addition(dvel);
	  MathVector dpos = (MathVector)vel1.clone();
	  dpos.multScalar(BH.DTIME);
	  dpos.addition(b.pos);
	  b.pos = (MathVector)dpos.clone();
	  vel1.addition(dvel);
	  b.vel = (MathVector)vel1.clone();
	  
	  p = p.getProcNext();
      }
  }
}
