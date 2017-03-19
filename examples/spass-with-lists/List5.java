public final class Node {
   public /*: claimedby List */ int next;
   public /*: claimedby List */ int prev;
   public /*: claimedby List */ int data;
   public /*: claimedby List */ Boolean head;
}

public class List 
{
   private static Node a;
   private static Node b;
   
   private static Node[] memory;

   /*:
     private static ghost specvar absNext :: "obj => obj";
     private static ghost specvar absPrev :: "obj => obj";
     public static specvar clause :: "int => int";
     private vardefs "clause == (% x. x - (x mod 3))";  

     private static specvar reach :: "obj => obj => bool";
     private vardefs "reach == (% x y. (x,y) : {(x, y). x..absNext = y}^*)";

     private static specvar aReach :: "obj => bool";
     private vardefs "aReach == (% x. (a,x) : {(x, y). x..absNext = y}^*)";

     private static specvar validIndex :: "int => bool";
     private vardefs "validIndex == (% n. n >= 0 & n < memory..Array.length)";


     public static specvar aClauses :: "int set";
     private vardefs "aClauses == {x. EX z. validIndex z & clause z = x & aReach (memory.[z]) & memory.[z] ~= null & memory.[z] ~= a}";
     
     invariant memoryNotNull: "memory ~= null";
     invariant memoryInitialized: "memory.[1] = a & memory.[2] = b";
     invariant memoryAligned: "memory..Array.length >= 3 & memory..Array.length mod 3 = 0";
          
     invariant absNextDef1: "ALL x. x ~= null & validIndex (x..next) --> x..absNext = memory.[x..next]";
     invariant absNextDef2: "ALL x. x = null | ~ validIndex (x..next) --> x..absNext = null";
     
     invariant absPrefDef1: "ALL x. x ~= null & validIndex (x..prev) --> x..absPrev = memory.[x..prev]";
     invariant absPrefDef2: "ALL x. x = null | ~ validIndex (x..prev) --> x..absPrev = null";

     invariant absDLL1: "ALL x. x..absPrev..absNext = x | x..absPrev = null & (ALL y. y..absNext ~= x)";
     invariant absDLL2: "ALL x. x..absNext..absPrev = x | x..absNext = null & (ALL y. y..absPrev ~= x)";

     // invariant "ALL n. validIndex n & n mod 3 ~= 0 --> reach a (memory.[n]) | reach b (memory.[n])";
     invariant nextAligned: "ALL x. reach a x & x ~= null & validIndex (x..next) --> x..next mod 3 > 0";
     invariant prevAligned: "ALL x. reach a x & x ~= null & validIndex (x..prev) --> x..prev mod 3 > 0";

     invariant headsNotReachable: "ALL n. validIndex n & n mod 3 = 0 --> ~ reach a (memory.[n]) & ~ reach b (memory.[n])";
     invariant headsNotNull: "ALL n. validIndex n & n mod 3 = 0 --> memory.[n] ~= null";

     invariant memoryInjective: "ALL n m. validIndex n & validIndex m & memory.[n] = memory.[m] --> n = m | memory.[n] = null"; 

     invariant "ALL n. validIndex n & memory.[n] ~= null & validIndex (memory.[n]..next) --> memory.[memory.[n]..next] ~= null";
     invariant "ALL n. validIndex n & memory.[n] ~= null & validIndex (memory.[n]..prev) --> memory.[memory.[n]..prev] ~= null";

     invariant "ALL n m. validIndex n & validIndex m & memory.[n] ~= null & memory.[m] ~= null & memory.[m]..data = memory.[n]..data & clause n = clause m --> n = m";

     invariant "a..data ~= b..data";
     
     //invariant "ALL x. x = null | x..data1 ~= x..data2";

     invariant "ALL x. aReach x & x ~= null --> x..data = a..data";
     
     invariant aAcyclic: "aReach null";
   
     invariant abDisjoint: "ALL x. reach a x & reach b x --> x = null";
   */

   public static void delete_a (int ha)
   /*: requires "ha : aClauses"
       modifies "Array.arrayState", aClauses 
       ensures "True";
       //: ensures "aClauses = old aClauses - {ha}";
   */
   {
      //: assume "ALL x y. x ~= y & y ~= null & reach x y --> reach x (y..absPrev) & y..absPrev ~= null";
      int qa, pa, na;
      Node q, p, n;

      if (memory[ha+1] != null && memory[ha+1].data == a.data) qa = ha + 1;
      else qa = ha + 2;

      q = memory[qa];
      
      pa = q.prev;
      p = memory[q.prev];

      na = q.next;

      if (na >= 0 && na < memory.length) {
	 n = memory[q.next];
	 n.prev = pa;
	 //: "n..absPrev" := "p";
      } else {
	 n = null;
      }
      

      p.next = na;
      //: "p..absNext" := "n";

      q.next = -1;
      q.prev = -1;
      
      //: "q..absNext" := "null";
      //: "q..absPrev" := "null";

      memory[qa] = null;
   }

   public static void insert_a (int qa)
   //: modifies "Array.arrayState" ensures "True";
   {
      //: assume "ALL x y. x ~= y & y ~= null & reach x y --> reach x (y..absPrev) & y..absPrev ~= null";
      Node q, p, n;
   }
}
 
