public final class Node {
    public /*: claimedby List */ Node next;
    public /*: claimedby List */ boolean data;
}

public class List 
{
   /*:
     // public static specvar content :: objset;
     // vardefs "content == {x. (first,x) : {(x,y). x..next = y}^*}";

     private static specvar is_root :: "obj => bool";
     private vardefs "is_root == 
       (% first. first ~= null --> (ALL x. x..next ~= first))";

     invariant "tree [next]";
   */
    
   public static void reverse(Node root)
   {
      Node first = root;
      //: assume "is_root first";
           
      Node t, e;
      e = first;
      first = null;
      while (e != null) {
	 t = first;
	 first = e;
	 e = e.next;
	 first.next = t;
      }
      //: assert "is_root first";
   }

   public static void reverse2(Node root)
   {
      Node first = root;
      //: assume "ALL v1 v2. v1..next ~= null & v1 ~= v2 --> v1..next ~= v2..next";
      //: assume "is_root first";
           
      Node t, e;
      e = first;
      first = null;
      while (e != null) {
	 t = first;
	 first = e;
	 e = e.next;
	 first.next = t;
      } 
      //: assert "is_root first";
   }

   public static void filter(Node root)
   {
      Node first = root;
      //: assume "is_root first";

      Node e = first;
      Node prev = null;

      boolean nondet;
      while (e != null) {
	 // havoc "nondet";
	 if (e.data) {
	    if (prev == null) {
	       prev = e;
	       e = e.next;
	       first = e;
	       prev.next = null;
	       prev = null;
	    } else {
	       e = e.next;
	       Node tmp = prev.next;
	       tmp.next = null;
	       prev.next = e;
	    }
	 } else {
	    prev = e;
	    e = e.next;
	 }
      }
      
      // assert "ALL v. (first,v) : {(x,y). x..next = y}^* & null ~= v --> ~v..data"; 
      //: assert "is_root first";
   }

   public static void partition(Node root)
   {
      //: assume "is_root root";
      Node p_true = null;
      Node p_false = null;
      Node e = root;
      while (e != null) {
	 if (e.data) {
	    Node tmp = p_true;
	    p_true = e;
	    e = e.next;
	    p_true.next = tmp;
	    tmp = null;
	 } else {
	    Node tmp = p_false; 
	    p_false = e;
	    e = e.next;
	    p_false.next = tmp;
	    tmp = null;
	 }
      }
      
      //: assert "ALL v. (p_true,v) : {(x,y). x..next = y}^* & null ~= v --> v..data"; 
      //: assert "is_root p_true";
      //: assert "is_root p_false";

   }

   /*
   public static void splice(Node root)
   {
      Node e = root;
      Node l1 = null;
      Node l2 = null;
      boolean flag = false;

      while (e != null) {
	 if (flag) {
	    if (l1 == null) {
	       l1 = e;
	       else 
	    }
	 }
      }
      }*/


   public static void append(Node l1, Node l2)
   {
      //: assume "is_root l1";
      //: assume "is_root l2";
      //: assume "l1 ~= l2";
      // assume "(l1,l2) : {(x,y). x..next = y}^* --> l2 = null";
      // assume "(l2,l1) : {(x,y). x..next = y}^* --> l1 = null";
      // assume "tree [next]";

      Node l = l1;
      Node e = l1;
      Node last = null;

      while (e != null) {
	 last = e;
	 e = e.next;
      }
      
      if (last == null) l = l2;
      else last.next = l2;

      // assert "is_root l";
      // assert "(tree
   }


   public static void insertBefore(Node root, Node pos, Node n)
   {
      //: assume "is_root root";
      //: assume "is_root n";
      //: assume "(root,pos) : {(x,y). x..next = y}^*";
      //: assume "(root,n) ~: {(x,y). x..next = y}^*";
      Node e = root;
      Node prev = null;

      while (e != pos) {
	 prev = e;
	 e = e.next;
      }
      
      if (prev == null) {
	 n.next = root;
      } else { 
	 prev.next = n;
	 n.next = e;
      }
      
   }

   public static void findPrev(Node x, Node y)
   {
      //: assume "(x,y) : {(x,y). x..next = y}^*";
      //: assume "tree [next]";
      Node e = x;
      Node prev = null;

      while (e != y) {
	 prev = e;
	 e = e.next;
      }
   }

   public static void split(Node root, Node pos)
   {
      //: assume "ALL v1 v2. v1..next ~= null & v1 ~= v2 --> v1..next ~= v2..next";
      //: assume "root ~= pos";
      Node e = root;
      Node prev = null;

      while (e != pos && e != null) {
	 prev = e;
	 e = e.next;
      }
      
      if (prev != null) 
	 prev.next = null;
   
      //: assert "e = pos --> is_root pos";
   }

   public static void contains(Node root, Node n)
   {
      Node e = root;
      boolean result;
      
      while (e != null && e != n) {
	 e = e.next;
      }
	 
      result = e != null;
      
      //: assert "result == (root,n) : {(x,y). x..next = y}^* & n ~= null";
      // congruence closure required
   }

   public static void create()
   {
      Node root = null;
      
      boolean nondet;
      while (nondet) {
	 //: havoc nondet;
	 Node e = new Node();
	 e.next = root;
	 root = e;
      }
      //: assert "is_root root";
   }

   public static void getLast(Node root)
   {
      Node e = root;
      Node p = null;

      while (e != null) {
	 p = e;
	 e = e.next;
      }

      //: assert "ALL v. (root,v) ~: {(x,y). x..next = y}^* --> p ~= v";
      //: assert " p..next = null";
   }

   public static void removeLast(Node root)
   {
      Node e = root;
      Node l = null;
      Node prev = null;

      while (e != null) {
	 prev = l;
	 l = e;
	 e = e.next;
      }

      if (root != l) {
	 prev.next = null;
      }

      // assert "ALL v. (root,v) ~: {(x,y). x..next = y}^* --> l ~= v";
      //: assert " l..next = null";
      // no progress required
   }

   public static void remove(Node root, Node n)
   /* 
     requires "tree [next]"
     ensures "True";
    */
   {
      //: assume "n ~= null";
      Node result = root;
      Node e = root;
      Node prev = null;

      while (e != null && e != n) {
	 prev = e;
	 e = e.next;
      }

      if (e != null) {
	 if (prev != null) {
	    prev.next = e.next;
	 } else {
	    result = root.next;
	 }
	 e.next = null;
      }
      
      //: assert "ALL v. (result,v) : {(x,y). x..next = y}^*  --> v ~= n"
      // congruence closure required
   }



   public static void traverse(Node root)
   {
      Node e = root;
      
      while (e != null) {
	 e = e.next;
      }
   }


   
}
 
