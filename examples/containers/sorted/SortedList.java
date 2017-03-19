class SortedList 
    /* sorted list  */
{
    private static Node first;

    /*: 
      private static specvar reach :: "obj => obj => bool";
      vardefs
        "reach == (% a b. rtrancl_pt (% x y. x..next=y) a b)";

      public static specvar content :: objset;
      vardefs
        "content == {n. n ~= null & (first, n) : {(x,y). x..next = y}^*}";

      invariant "tree [next]";

      invariant "first = null | (ALL n. n..next ~= first)";
      
      invariant "ALL x n. x ~= null & n ~= null & x..next = n --> n : content";

      invariant "(ALL n. n : content & n..next ~= null --> n..key <= n..next..key)";
      //invariant "(ALL x y. x : content & (x,y) : {(x,y). x..next = y}^* & x ~= y & y ~= null --> x..key < y..key)";
    */

   public static void add2(Node nn)
    /*: requires "nn ~= null & nn ~: content"
        modifies content
        ensures "content = old content Un {nn}"
    */
    {
	Node prev = null;
	Node current = first;
	while ((current != null) && (current.key < nn.key)) {
	   prev = current;
	   current = current.next;                    
	}
	nn.next = current;
	if (prev != null){
	   prev.next = nn;
	} else {
	   first = nn;
	}
    }

   public static void add(Node nn)
      /*: requires "nn ~= null & nn ~: content"
	modifies content
	ensures "content = old content Un {nn}"
      */
   {
      if (first==null) {
	 first = nn;
	 nn.next = null;
	 return;
      } else if (first.key >= nn.key) {
	 nn.next = first;
	 first = nn;
	 return;
      }

      Node prev = first;
      Node current = first.next;
      while ((current != null) && (current.key < nn.key)) {
	 prev = current;
	 current = current.next;                    
      }
      nn.next = current;
      prev.next = nn;
   }

   public static void remove(Node nn)
      /*: requires "nn ~= null" 
	modifies content
	ensures "content = old content - {nn}"
      */
   {
      Node prev = null;
      Node current = first;
      while /*
	      inv "(prev ~= null --> prev..next = current) &
	           (prev = null --> current = first) &
	           (current ~= null --> current : content) &
                   (prev ~= null --> prev : content) &
		   (reach current nn | nn ~: content)& 
		   null..next = null
		   "
	     */
	 ((current != null) && (current.key < nn.key)) {
	 prev = current;
	 current = current.next;                    
      }
      
      if (current == nn) {
	 if (prev != null) {
	    prev.next = current.next;
	 } else {
	    first = current.next;
	 }
	 current.next = null;
      }
   }

   public static void remove2(Node nn)
      /*: requires "nn : content" 
	modifies content
	ensures "content = old content - {nn}"
      */
   {
      Node prev = null;
      Node current = first;
      while /*:
	      inv "(prev ~= null --> prev..next = current) &
	           (prev = null --> current = first) &
	           current : content &
                   (prev ~= null --> prev : content) &
		   reach current nn & 
		   null..next = null &
		   nn : content 
		   "
	     */
	 (current.key < nn.key) {
	 prev = current;
	 current = current.next;                    
      }
      
      //: noteThat "current = nn";
      
      if (prev != null) {
	 prev.next = current.next;
	    
      } else {
	 first = current.next;
      }
      current.next = null;
   }
}
