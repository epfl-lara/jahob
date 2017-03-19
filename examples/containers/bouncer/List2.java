public class List 
{
   private static Node p;
   
   /*:
     private static ghost specvar next0 :: "obj => obj";
     private static ghost specvar a :: "obj";
     private static ghost specvar b :: "obj";
     
     private static  specvar content :: "obj set";
     private vardefs "content == {x. (p,x) : {(x,y). x..Node.next = y}^*}";

     invariant "ALL x y. Node.next x = y --> (x=a --> y=b) & (x~=a --> next0 x = y)";
   
     invariant "tree [next0]";
   */

   public static void test(Node q){
      //: assume "(p,q) : {(x,y). x..Node.next = y}^*";
      //: assume "p = q --> (p..Node.next,p) : {(x,y). x..Node.next = y}^*";
      //: assume "p ~= null";
      
      //: assert "(p,q) : {(x,y). x..Node.next = y}^*";
      p = p.next;
      while(p != null && p != q){
	 //: assert "(p,q) : {(x,y). x..Node.next = y}^*";
	 p = p.next;
      }      
   }

   public static void test2(Node q, Node y){
      Node x;
      //: assume "p ~= q";
      // assume "(p,x) : {(a,b). a ~= q & a..Node.next = b}^* & x ~= q --> (y,q) : {(a,b). a ~= x & a..Node.next = b}^*"; 
      //: assume "(p,x) : {(a,b). a ~= q & a..Node.next = b}^* & x ~= q --> (y,q) : {(a,b). a..Node.next = b}^*"; 
      /*: assume "(p,q) : {(a,b). a ~= x & a..Node.next = b}^* | (p,x) : {(a,b). a..Node.next = b}^*";
      */ 
      //: assume "x = a & a ~= null";
      //: assume "p ~= null";
      x.next = y;
      //: b := "y";

      //: assert "(p,q) : {(x,y). x..Node.next = y}^*";
      p = p.next;
      while(p != null && p != q){
	 //: assert "(p,q) : {(x,y). x..Node.next = y}^*";
	 p = p.next;
      }  
   }

   public static void test3(Node q, Node y)

   {
      /*:
	private static specvar reach_y :: objset;
	private vardefs "reach_y == {x. (y,x) : {(a,b). a..Node.next = b}^*}";
      */
      //: track(reach_y);
      Node x;
      boolean nobreak;
      //: assume "p ~= q & q : content";
      // assume "(p,x) : {(a,b). a ~= q & a..Node.next = b}^* & x ~= q --> (y,q) : {(a,b). a ~= x & a..Node.next = b}^*"; 
      // assume "(p,x) : {(a,b). a ~= q & a..Node.next = b}^* & x ~= q --> (y,q) : {(a,b). a..Node.next = b}^*"; 
      //: assume "(y,q) : {(a,b). a..Node.next = b}^*";
      //: assume "ALL z. z ~= q & (p,z) : {(a,b). a ~= q & a..Node.next = b}^* --> z ~: reach_y";
      //: assume "p ~= null";
      x = p;
      while(nobreak && x.next != null){
	 //: track(reach_y);
	 boolean nobreak1;
	 nobreak = nobreak1;
	 x = x.next;
      }
      //: track(reach_y);
      //: assume "x = a";
      x.next = y;
      //: b := "y";

      //: assert "(p,q) : {(x,y). x..Node.next = y}^*";
      p = p.next;
      while(p != null && p != q){
	 //: track(reach_y);
	 //: assert "(p,q) : {(x,y). x..Node.next = y}^*";
	 p = p.next;
      }  
   }
}
