public class List 
{
   private static Node first;
   
   /*:
     private static specvar reach :: "obj => obj => bool";
     private vardefs "reach == 
     (% a b. rtrancl_pt (% x y. x..Node.next = y) a b)";

     public static specvar content :: objset;
     private vardefs "content == {x. x ~= null & reach first x}";

     private ghost specvar jp :: "obj => obj";


     invariant "first ~= null --> (ALL n. n..Node.next ~= first)";
   
     invariant "tree [Node.next]";
   */
    
   public static void reverse ()
      /*: modifies content
	ensures "content = old content";
      */
   {
      Node t, e;
      e = first;
      first = null;
      while /*: inv "old content = content Un {x. x ~= null & reach e x} &
	             content Int {x. reach e x} = {} &
	             tree [Node.next] &
		     (e ~= null --> (ALL n. n..Node.next ~= e)) &
                     (first ~= null --> (ALL n. n..Node.next ~= first))" */
	  (e != null) {
	 t = first;
	 first = e;
	 e = e.next;
	 first.next = t;
      }
   }

   public static void reverse_propagation ()
      /*: modifies content
	ensures "content = old content";
      */
   {
      /*:
	private specvar has_pred :: objset;
	private vardefs "has_pred == {x. ALL n. n..Node.next ~= x}";

	private specvar reach_e :: objset;
	private vardefs "reach_e == {x. reach e x}";

	assume "e = null | ~(reach first e)";

      */
      Node t, e;
      e = null;
      while (first != null) {
	 //: track(reach_e);
	 //: track(has_pred);
	 t = e;
	 e = first;
	 first = first.next;
	 e.next = t;
      }
      first = e;
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

   // Fun example
   public static void example()
   /*: ensures "True";
    */
   {
       //: private ghost specvar numbers :: "int set";
       int x = 7;

       //: "numbers" := "{ y. y > 6}";
       
       //: assert "x : numbers";
       x = x - 1;
       //: assert "x ~: numbers";
   }
}
 
