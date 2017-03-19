public class List 
{
   private static Node p;
   
   /*:
     private static  specvar content :: "obj set";
     private vardefs "content == {x. (p,x) : {(x,y). x..Node.next = y}^*}";

     invariant "tree [Node.next]";
   */

   public static void test3(Node y)
   {
      /*:
	private static specvar reach_y :: objset;
	private vardefs "reach_y == {x. (y,x) : {(a,b). a..Node.next = b}^*}";
      */
      //: track(reach_y);
      Node x;
      boolean nobreak;
      //: assume "y ~= null --> (ALL x. x..Node.next ~= y)";
      //: assume "ALL x. x : content & x : reach_y --> x = null";
      //: assume "p ~= null";
      x = p;
      while(nobreak && x.next != null){
	 //: track(reach_y);
	 boolean nobreak1;
	 nobreak = nobreak1;
	 x = x.next;
      }
      //: track(reach_y);
      x.next = y;
      //: assert "(p,null) : {(x,y). x..Node.next = y}^*";
      p = p.next;
      while(p != null){
	 //: track(reach_y);
	 //: assert "(p,null) : {(x,y). x..Node.next = y}^*";
	 p = p.next;
      }  
   }
}
