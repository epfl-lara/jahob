class Node {
  public /*: claimedby Tree */ Node l, r, p;
}
class Tree {
    private static Node root;
    /*:
    invariant "ptree p [l,r]";
    invariant "p root = null";
    private static specvar content :: objset;
    vardefs "content=={x. root ~= null & x ~= null & (x,root) : {(x,y). p x = y}^*}";
    */

    private void insertLeftOf(Node pos, Node e) 
    /*:
      requires "ptree p [l,r] & p root = null & root ~= null & (ALL x. l x ~= root & r x ~= root) &
                pos : content & pos ~= null & l pos = null &
                e ~: content & e ~= root & e ~= null & p e = null & l e = null & r e = null"
      modifies content,l,p
      ensures "pos : content" // "(e,root) : {(x,y). p x = y}^*" // content = old content Un {e}" 
    */
    {	
	e.p = pos;
	pos.l = e;
	//: assert "ptree p [l,r]";
    }
}
