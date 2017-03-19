/*
  Shows how fast things are when vc is given on the folklore example.
  Also, Bohne can infer the invariants.
 */

public final class Node {
    public /*: claimedby List */ Node next;
    public /*: claimedby List */ int data;
}

public class List 
{
   private static Node first;
   
   /*:
     private static specvar next_star :: "obj => obj => bool";
     private vardefs "next_star == 
     (% a b. (a,b) : {(x, y). x..Node.next = y}^*)";

     public static specvar content :: objset;
     private vardefs "content == {x. (first,x) : {(x, y). x..Node.next = y}^*}";
   
     invariant "first ~= null --> (ALL x. x..Node.next ~= first)";

     invariant "tree [Node.next]";
   */
    
   public static void reverse ()
   {
      Node t, e;
      e = first;
      first = null;
      while (e != null) {
	 t = first;
	 first = e;
	 e = e.next;
	 first.next = t;
      } 
   }

   public static void reverse_annot ()
   //:	ensures "content = old content";
   {
      Node t, e;
      e = first;
      first = null;
      while /*:inv "tree [Node.next] &
                    old content = {x. next_star e x} Un {x. next_star first x} &
	            (next_star e first --> first = null) &
		    (first ~= null --> ~ (next_star e first) & (ALL n. n..Node.next ~= first)) &
		    (e ~= null --> (ALL n. n..Node.next ~= e))";
	     */
	 (e != null) {
	 t = first;
	 first = e;
	 e = e.next;
	 first.next = t;
      }
   }

   public static void test ()
    /*: modifies content
      ensures "True";
     */
   {
       int i = 0;
       int n = 10;
       boolean b;
       Node x;
       while (i < n)
       {
	   x = new Node ();
	   x.data = i;
	   x.next = first;
	   first = x;
	   i = i + 1;
       }
       i = n - 1;
       x = first;
       // linked list should have 9 .. 0
       while (i >= 0)
       {
	   b = (x.data == i);
	   //: assert "b"
	   i = i - 1;
	   x = x.next;
       }
       reverse ();
       i = 0;
       x = first;
       // linked list should have 0 .. 9
       while (i < n)
       {
	   b = (x.data == i);
	   //: assert "b"
	   i = i + 1;
	   x = x.next;
       }
   }
}
 
