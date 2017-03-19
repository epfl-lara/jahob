public final class Node {
   public /*: claimedby List */ Node next1;
   public /*: claimedby List */ Node next2;
   public /*: claimedby List */ Object data1;
   public /*: claimedby List */ Object data2;
}

public class List 
{
   private static Node a;
   private static Node b;
   
   /*:
     private static ghost specvar nexta :: "obj => obj";
     private static ghost specvar nextb :: "obj => obj";

     //private static specvar reach :: "obj => obj => bool";
     //private vardefs "reach == (% x y. (x,y) : {(x, y). x..next = y}^*)";

     private static specvar reacha :: "obj => bool";
     private vardefs "reacha == (% x. (a,x) : {(x, y). x..nexta = y}^*)";

     private static specvar reachb :: "obj => bool";
     private vardefs "reachb == (% x. (b,x) : {(x, y). x..nextb = y}^*)";

     invariant nullNext1: "null..next1 = null";
     invariant nullNext2: "null..next2 = null";

     
     invariant nextaDef: "ALL x. x..data1 = a..data1 & x..nexta = x..next1 |
                                 x..data2 = a..data1 & x..nexta = x..next2";

     invariant nextbDef: "ALL x. x..data1 = b..data1 & x..nextb = x..next1 |
                                 x..data2 = b..data1 & x..nextb = x..next2";
   
     invariant "a ~= null & b ~= null";
     invariant "a..data1 ~= b..data1";
     
     invariant "ALL x. x..data1 ~= x..data2";
     
     invariant aAcyclic: "reacha null";
     invariant bAcyclic: "reachb null";
   
     //invariant abDisjoint: "ALL x. reacha x & reachb x --> x = null";
   */
    
   public static void delete_a (Node p)
   {
      //: assume "p ~= null & nexta p ~= null & reacha p";

      Node q;
      if (p.data1 == a.data1) {
	 q = p.next1;
      } else {
	 q = p.next2; 
      }

      Node n;
      if (q.data1 == a.data1) {
	 n = q.next1;
	 q.next1 = null;
      } else {
	 n = q.next2;
	 q.next2 = null;
      }
     
      if (p.data1 == a.data1) {
	 p.next1 = n;
      } else {
	 p.next2 = n;
      }
      //: "p..nexta" := "n";
      //: "q..nexta" := "null";
     
   }
}
 
