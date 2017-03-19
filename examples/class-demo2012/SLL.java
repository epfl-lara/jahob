class Node { public /*: claimedby SLL */ Node next; }
class SLL
{
   private static Node root;
   /*: 
       private static specvar reachable :: "obj => obj => bool";
       private vardefs "reachable == (% x y.
                        (x,y) : {(u,v). u..next = v}^*)";

       public static specvar content :: objset;
       private vardefs "content ==  {x. x ~= null &  reachable root x}";
   
       invariant tree: "tree [next]";
   
       invariant rootFirst: "root = null | 
                             (ALL n. n..next ~= root)";
   */
   public static void addLast(Node n)
      /*: 
	requires "n ~: content & n ~= null & n..next = null &
                  (ALL m. m..next ~= n)"
	modifies content
	ensures "content = old content Un {n}";
      */
   {
      if (root == null) {
        root = n;
        n.next = null; 
        return;
      }

      Node r = root;
      while //: inv "r : content"
       (r.next != null) {
	 r = r.next;
      }
      r.next = n; 
   }

   public static void remove(Node n)
  /*: requires "n : content"
      modifies content
      ensures "content = old content - {n}"
   */
   {
       if (root == n) {
	   root = root.next;
	   n.next = null;
       } else {
	   Node r = root;
	   while //: inv "r ~= n & r : content & reachable r n"
	       (r.next != n) {
	       r = r.next;
	   }
	   r.next = n.next;
	   n.next = null;    
       }
   }

   public static void removeMaybe(Node n)
  /*: requires "(n : content)"
      modifies content
      ensures "content = old content 
             | content = old content - {n}"
   */
   {
      if (root == n) {
	  root = root.next;
	  n.next = null;
      } else {
	  Node r = root;
	  while //: inv "r : content"
	      (r.next != null && r.next != n) {
	      r = r.next;
	  }
	  if (r.next == n) {
	      r.next = n.next;
	      n.next = null;    
	  }
      }
   }
}
