public final class Node {
   public /*: claimedby Justvc */ Node right;
   public /*: claimedby Justvc */ Node left;
   public /*: claimedby Justvc */ Object data;
}
public class Justvc
{
    private static Node root;
    private static int size;
    /*:
      private static specvar inlist :: objset;
      private static specvar content :: objset;

      vardefs "inlist == 
      {x. rtrancl_pt (% x y. x..left = y | x..right = y) root x}";

      vardefs "content ==
      {x. EX n. n ~= null & n : inlist & n..data = x}";      
    */

    private void vc(Node p, Object e) 
    /*:
      requires "tree [left, right] &
                inlist <= Object.alloc &
	        size = card content &
                e ~: content & e ~= null &
	        p : inlist & p ~= null & p..left = null"
      modifies inlist, content, left, right, data, size
      ensures "size = card content"
     */
    {	
	Node n = new Node();
	n.data = e;
	p.left = n;
	size = size + 1;
	/*:
	  noteThat "inlist = old inlist Un {n}";
	  noteThat isIn: "content = old content Un {e}";
	 */
    }

    private void vc1(Node p, Object e) 
    /*:
      requires "tree [left, right] &
                inlist <= Object.alloc &
	        size = card content &
                e ~: content & e ~= null &
	        p : inlist & p ~= null & p..left = null"
      modifies inlist, content, left, right, data, size
      ensures "content = old content Un {e}"
     */
    {	
	Node n = new Node();
	n.data = e;
	p.left = n;
	size = size + 1;
	/*
	  noteThat "inlist = old inlist Un {n}";
	 */
    }

    private void vcAllInvs(Node p, Object e)
    /*:
      requires "True"
      modifies inlist, content, left, right, data, size
      ensures "True"
     */
    {	
	/*:
	  assume "tree [left, right]";
	  assume "inlist <= Object.alloc";
	  assume "size = card content";
	  assume "root = null | (ALL n. n..left ~= root & n..right ~= root)";
	  assume "ALL x y. x ~= null & y ~= null & (x..right = y | x..left = y) --> y : inlist";

	  assume "e ~: content & e ~= null";
	  assume "p : inlist & p ~= null";
	  assume "p..left = null";
	 */
	Node n = new Node();
	n.data = e;
	p.left = n;
	size = size + 1;
	/*:
	  noteThat "inlist = old inlist Un {n}";
	  noteThat isIn: "content = old content Un {e}";
	  noteThat sizeOk: "size = card content";
	 */
    }


}
