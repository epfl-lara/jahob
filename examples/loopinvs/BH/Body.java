
import java.lang.Math;
import java.util.Enumeration;

/**
 * A class used to representing particles in the N-body simulation.
 **/
final class Body extends Node
{
  MathVector vel;
  MathVector acc;
  MathVector newAcc;
  int        phi;

  private Body next;
  private Body procNext;
  
  /**
   * Create an empty body.
   **/
  Body()
  {
    vel      = new MathVector();
    acc      = new MathVector();
    newAcc   = new MathVector();
    phi      = 0;
    next     = null;
    procNext = null;
  }

  /**
   * Set the next body in the list.
   * @param n the body
   **/
  final void setNext(Body n)
  {
    next = n;
  }

  /**
   * Get the next body in the list.
   * @return the next body
   **/
  final Body getNext()
  {
    return next;
  }

  /**
   * Set the next body in the list.
   * @param n the body
   **/
  final void setProcNext(Body n)
  {
    procNext = n;
  }

  /**
   * Get the next body in the list.
   * @return the next body
   **/
  final Body getProcNext()
  {
    return procNext;
  }

  /**
   * Check the bounds of the body and return true if it isn't in the
   * correct bounds.
   **/
  final boolean icTest(Tree tree)
  {
      int pos0 = pos.getX();
      int pos1 = pos.getY();
      int pos2 = pos.getZ();
    
      int txmin = tree.rmin.getX();
      int txmax = txmin + tree.rsize;
      if (!(txmin <= pos0 && pos0 < txmax))
	  return false;

      int tymin = tree.rmin.getY();
      int tymax = tymin + tree.rsize;
      if (!(tymin <= pos1 && pos1 < tymax))
	  return false;

      int tzmin = tree.rmin.getZ();
      int tzmax = tzmin + tree.rsize;
      if (!(tzmin <= pos2 && pos2 < tzmax))
	  return false;

      return true;
  }

  /**
   * Descend Tree and insert particle.  We're at a body so we need to
   * create a cell and attach this body to the cell.
   * @param p the body to insert
   * @param xpic
   * @param l 
   * @param tree the root of the data structure
   * @return the subtree with the new body inserted
   **/
  final Node loadTree(Body p, MathVector xpic, int l, Tree tree)
  {
    // create a Cell
    Cell retval = new Cell();
    int si = subindex(tree, l);
    // attach this Body node to the cell
    retval.subp[si] = this;

    // move down one level
    si = oldSubindex(xpic, l);
    Node rt = retval.subp[si];
    if (rt != null) 
      retval.subp[si] = rt.loadTree(p, xpic, l/2, tree);
    else 
      retval.subp[si] = p;
    return retval;
  }

  /**
   * Descend tree finding center of mass coordinates
   * @return the mass of this node
   **/
  final int hackcofm()
  {
    return mass;
  }

  /**
   * Return an enumeration of the bodies
   * @return an enumeration of the bodies
   **/
  final Enumeration elements()
  {
    // a local class that implements the enumerator
    class Enumerate implements Enumeration {
      private Body current;
      public Enumerate() { this.current = Body.this; }
      public boolean hasMoreElements() { return (current != null);  }
      public Object nextElement() {
	if (current == null) throw new java.util.NoSuchElementException("Body - forward");
	Object retval = current;
	current = current.next;
	return retval;
      }
    }
    return new Enumerate();
  }

  final Enumeration elementsRev()
  {
    // a local class that implements the enumerator
    class Enumerate implements Enumeration {
      private Body current;
      public Enumerate() { this.current = Body.this; }
      public boolean hasMoreElements() {  return (current != null);  }
      public Object nextElement() {
	if (current == null) throw new java.util.NoSuchElementException("Body - backward");
	Object retval = current;
	current = current.procNext;
	return retval;
      }
    }

    return new Enumerate();
  }

  /**
   * Recursively walk the tree to do hackwalk calculation
   **/
  final void walkSubTree(int dsq, HG hg)
  {
    if (this != hg.pskip)
      gravSub(hg);
  }

  /**
   * Return a string represenation of a body.
   * @return a string represenation of a body.
   **/
  public String toString()
  {
    return "Body " + super.toString();
  }

}

