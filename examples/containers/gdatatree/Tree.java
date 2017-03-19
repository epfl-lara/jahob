public class Tree
{
   private static Node root;
   private static int size;
   /*: private static specvar inlist :: objset;
       public static specvar content :: objset;
       private vardefs "inlist == 
        {x. rtrancl_pt (% x y. x..Node.left = y | x..Node.right = y) root x}";
   
       private vardefs "content ==
        {x. EX n. n ~= null & n : inlist & n..data = x}"

       invariant "tree [Node.left, Node.right]";
   
       invariant "inlist <= Object.alloc";

       invariant "root = null | (ALL n. n..Node.left ~= root & n..Node.right ~= root)";
   
       invariant "ALL x y. x ~= null & y ~= null & (x..Node.right = y | x..Node.left = y) --> y : inlist";

       invariant "size = card content";
   */
    
   public static void add(Object e) 
      /*: 
	requires "e ~: content & e ~= null"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      boolean wentLeft = false;
      while (n != null) {
	 //: havoc "wentLeft"; 
	 p = n;
	 if (wentLeft) {
            n = n.left;
	 } else {
	    n = n.right;
	 }
      }
      Node n = new Node();
      n.data = e;
      if (p == null) {
	 root = n;
      } else {
	 if (wentLeft) {
            p.left = n;
	 } else {
            p.right = n;
	 }
      }
      size = size + 1;
   }

   public static void add_annotated(Object e) 
      /*: 
	requires "e ~: content & e ~= null"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      boolean wentLeft = false;
      while 
	 /*: inv "((p = null & n = null) --> root = null) &
                   p : inlist &
                   n : inlist &
                   (p ~= null & wentLeft --> p..Node.left = n) &
                   (p ~= null & ~wentLeft --> p..Node.right = n)"
             */
	 (n != null) {
	 p = n;
	 //: havoc "wentLeft"; 
	 if (wentLeft) {
            n = n.left;
	 } else {
	    n = n.right;
	 }
      }
      Node n = new Node();
      n.data = e;
      if (p == null) {
	 root = n;
      } else {
	 if (wentLeft) {
            p.left = n;
	 } else {
            p.right = n;
	 }
      }
      //: noteThat "inlist = old inlist Un {n}";
   }
   
   // The code below is just for debugging
   
   private static void openP() { System.out.print("("); }
   private static void closeP() { System.out.print(")"); }
   private static void println() { System.out.println(); }  
   public static void printFrom(Node n)
   {
     //openP();
     if (n != null) {
       printFrom(n.left);
       System.out.print(n.v + " ");
       printFrom(n.right);
     }
     //closeP();
   }  
   public static void print()
   {
     printFrom(root);
     println();
   }
}
 
