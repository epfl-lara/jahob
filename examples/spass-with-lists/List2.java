public final class Node {
    public /*: claimedby List */ Node next;
    public /*: claimedby List */ Node prev;
}

public class List 
{
   private static Node a;
   private static Node b;
   
   /*:
     private static specvar reach :: "obj => obj => bool";
     private vardefs "reach == (% x y. (x,y) : {(x, y). x..next = y}^*)";

     private static specvar reach_a :: "obj => bool";
     private vardefs "reach_a == (% x. (a,x) : {(x, y). x..next = y}^*)";

     private static specvar reach_b :: "obj => bool";
     private vardefs "reach_b == (% x. (b,x) : {(x, y). x..next = y}^*)";

     invariant dllist1: "ALL x. x..prev..next = x | x..prev = null & (ALL y. y..next ~= x)"
     invariant dllist2: "ALL x. x..next..prev = x | x..next = null & (ALL y. y..prev ~= x)"

     invariant nullPrev: "null..prev = null";
     invariant nullNext: "null..next = null";

     invariant "a ~= null & b ~= null";

     invariant aAcyclic: "reach_a null";
     invariant bAcyclic: "reach_b null";
   
     invariant abDisjoint: "ALL x. reach_a x & reach_b x --> x = null";
   */
    
   public static void delete_a (Node q)
   {
      //: assume "q ~= null & reach_a q & q ~= a";
      //: assume "ALL x y. x ~= y & y ~= null & reach x y --> reach x (y..prev) & y..prev ~= null";
      Node p = q.prev;
      //: noteThat "p ~= null";
      if (q.next != null) q.next.prev = p;
      p.next = q.next;      
      q.next = null;
      q.prev = null;
   }

}
 
