public final class Node {
    public /*: claimedby List */ Node next;
}

public class List 
{
   private static Node a;
   private static Node b;
   
   /*:
     private static specvar reach_a :: "obj => bool";
     private vardefs "reach_a == (% x. (a,x) : {(x, y). x..next = y}^*)";

     private static specvar reach_b :: "obj => bool";
     private vardefs "reach_b == (% x. (b,x) : {(x, y). x..next = y}^*)";

     invariant "reach_a null";
     invariant "reach_b null";
   
     invariant "ALL x. reach_a x & reach_b x --> x = null";
     //invariant "tree [next]";
   */
    
   public static void delete_a (Node p)
   {
      //: assume "p ~= null & next p ~= null & reach_a p";
      Node q = p.next;
      p.next = q.next;
      q.next = null;
   }

}
 
