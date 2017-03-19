public final class Node {
   public /*: claimedby Tree */ Node right;
   public /*: claimedby Tree */ Node left;
   public /*: claimedby Tree */ Node next;
   public /*: claimedby Tree */ int v;
}

public class Tree
{
   private static Node root;
   private static int size;
   
   /*: public static specvar content :: objset;
       private vardefs "content == 
        {x. rtrancl_pt (% x y. x..left = y | x..right = y) root x}";
   
       invariant "tree [left, right]";
   
       invariant "root = null | (ALL n. n..left ~= root & n..right ~= root)";
   
       invariant "ALL x y. x ~= null & y ~= null & (x..right = y | x..left = y) --> y : content";

       invariant "ALL x y. x..next = y <->
          (x ~= null -->
	    (x..right = null --> 
               ((EX z. z..left = x) --> y..left = x) &
	       ((ALL z. z..left ~= x) --> 
	           (((ALL z. (left z, x) ~: {(x1,x2). x1..right = x2}^*)) & (y = null) | 
		   (left y, x) : {(x1,x2). x1..right = x2}^*))) &
	    (x..right ~= null -->
	       y..left = null & y ~= null & (right x, y) : {(x1, x2). x1..left = x2}^*)) &
	  (x = null --> y = null)";

       invariant sizeInv: "size = card content";
   */
    
   public static void add_annotated(Node e) 
      /*: 
	requires "e ~: content"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      Node pred = null;
      Node succ = null;
      boolean wentLeft = false;

      while 
	 /*: inv "((p = null & n = null) --> root = null) &
                   p : content &
                   n : content &
                   (p ~= null & wentLeft --> p..Node.left = n) &
                   (p ~= null & ~wentLeft --> p..Node.right = n) &
		   e ~= null &
		   succ : content &
		   pred : content &
		   ((wentLeft | p = null) <-> succ = p) &
		   (~wentLeft <-> pred = p) &
		   (pred = null --> (root, p) : {(x1,x2). x1..left = x2}^*) &
		   (pred = null --> (root, n) : {(x1,x2). x1..left = x2}^*) &
		   ((root, p) : {(x1,x2). x1..left = x2}^* & wentLeft --> pred = null) &
		   (n ~= null & (root, n) : {(x1,x2). x1..left = x2}^* --> pred = null) &
		   (pred ~= null --> (pred..right,n) : {(x1,x2). x1..left = x2}^*) &
		   (pred ~= null & p ~= pred --> (pred..right,p) : {(x1,x2). x1..left = x2}^*) &
		   (succ = null --> (root, p) : {(x1,x2). x1..right = x2}^*) &
		   (succ = null --> (root, n) : {(x1,x2). x1..right = x2}^*) &
		   ((root, p) : {(x1,x2). x1..right = x2}^* & ~wentLeft --> succ = null) &
		   (n ~= null & (root, n) : {(x1,x2). x1..right = x2}^* --> succ = null) &
		   (succ ~= null --> (succ..left,n) : {(x1,x2). x1..right = x2}^*) &
		   (succ ~= null & p ~= succ --> (succ..left,p) : {(x1,x2). x1..right = x2}^*)"
             */
      (n != null) {
	 p = n;
	 if (e.v < n.v) {
	    wentLeft = true;
	    succ = n;
            n = n.left;
	 } else {
	    wentLeft = false;
	    pred = n;
	    n = n.right;
	 }
      }
      if (p == null) {
	 root = e;
      } else {
	 if (wentLeft) {
            p.left = e;
	 } else {
            p.right = e;
	 }
      }
      e.next = succ;
      if (pred != null) pred.next = e;
   }


    public static void add_annotated2(Node e) 
      /*: 
	requires "comment ''eFresh'' (e ~: content)"
	modifies content
	ensures "content = old content Un {e}";
      */
   {

      Node n = root, p = null;
      Node pred = null;
      boolean wentLeft = false;

      while 
	 /*: inv "((p = null & n = null) --> root = null) &
                   p : content &
                   n : content &
                   (p ~= null & wentLeft --> p..Node.left = n) &
                   (p ~= null & ~wentLeft --> p..Node.right = n) &
		   e ~= null &
		   pred : content &
		   (~wentLeft <-> pred = p) &
		   (pred = null --> (root, p) : {(x1,x2). x1..left = x2}^*) &
		   (pred = null --> (root, n) : {(x1,x2). x1..left = x2}^*) &
		   ((root, p) : {(x1,x2). x1..left = x2}^* & wentLeft --> pred = null) &
		   (n ~= null & (root, n) : {(x1,x2). x1..left = x2}^* --> pred = null) &
		   (pred ~= null --> (pred..right,n) : {(x1,x2). x1..left = x2}^*) &
		   (pred ~= null & p ~= pred --> (pred..right,p) : {(x1,x2). x1..left = x2}^*)"
             */
      (n != null) {
	 p = n;
	 if (e.v < n.v) {
	    wentLeft = true;
            n = n.left;
	 } else {
	    wentLeft = false;
	    pred = n;
	    n = n.right;
	 }
      }
      if (p == null) {
	 root = e;
      } else {
	 if (wentLeft) {
            p.left = e;
	 } else {
            p.right = e;
	 }
      }
      
      if (pred != null) {
	 e.next = pred.next;
	 pred.next = e;
      } else {
	 e.next = p;
      }
      //: noteThat cn: "content = old content Un {e}"
      size = size + 1;
      //: noteThat sizeOk: "theinv sizeInv" from cn, eFresh, sizeInv
   }

}
 
