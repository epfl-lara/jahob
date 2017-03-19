class Node {
   public /*: claimedby SizeList */ Node next;
}

class SizeList {
   private static Node root;
   private static int size;
   /*: 
     public static specvar content :: objset;
     vardefs "content == {n. n ~= null & (root,n) : {(u,v). u..next=v}^*}";
     invariant sizeInv: "size = cardinality content";
     invariant treeInv: "tree [next]";
     invariant rootInv: "root ~= null --> (ALL n. n..next ~= root)";
     invariant noNextInv: "ALL x. x ~= null & x ~: content --> x..next = null";

   */
   
   public static void add(Node x)
   /*: requires "x ~= null & x ~: content"
     modifies content
     ensures "content = old content Un {x}" */
   {
      x.next = root;
      root = x; 
      size = size + 1;
   }

   public static void remove(Node x)
   /*: requires "x : content"
     modifies content
     ensures "content = old content - {x}" 
   */
   {
      Node e = root;
      Node prev = null;
      while (e != x) {
	 prev = e;
	 e = e.next;
      }
      if (prev == null) {
	 root = e.next;
      } else {
	 prev.next = e.next;
      }
      e.next = null;
      size = size - 1;
   }
}
