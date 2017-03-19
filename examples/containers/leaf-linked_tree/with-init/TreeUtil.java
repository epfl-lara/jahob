
public class TreeUtil {
	 // The code below is just for debugging
	   private static void openP() { System.out.print("("); }
	   private static void closeP() { System.out.print(")"); }
	   private static void println() { System.out.println(); }  
	   public static void printFrom(Node n)
	   {
	     //inorder traversal
	     if (n != null) {
	       printFrom(n.left);
	       System.out.print(n.v + " ");
	       printFrom(n.right);
	     }
	   }  
	   public static void printTree()
	   {
	     printFrom(Tree.getRoot());
	     println();
	   }

	   public static void printNode(Node n, String label) {

	        if (n == null) 
	                System.out.println(label + ": null");
	        else
	                System.out.println(label + ": " + n.v);

	   }

	   public static void printNodeFields(Node n) {
	 
		printNode(n, "n.value");
		printNode(n.left, "n.left");
		printNode(n.right, "n.right");
		printNode(n.next, "n.next");
		printNode(n.prev, "n.prev");
		printNode(n.parent, "n.parent");
	   }
	   
	   public static void printList() {
		   Node cur = Tree.findSmallestLeaf();
		   while(cur != null) {
			   printNodeFields(cur);
			   System.out.println();
			   cur = cur.next;
		   }
	   }

	   public static Node findNeighbor(Node l) {

		// l is the only node in the tree
		Node p = l.parent;
		if (p == null)
			return null;

		if (p.left.v == l.v)
			return p.right;
		
		Node nextRight = null;

		while (p.parent != null) {
			if (p.parent.right != null && p.parent.right.v != p.v)
				nextRight = p.right;
			p = p.parent;
		}
		
		return nextRight;
	  }

}
