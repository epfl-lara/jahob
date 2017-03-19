private class Thread {
  // control flow encoding:
  // A=00, B=01, C=10
  public boolean pc_bit_0;
  public boolean pc_bit_1;
  public static int count;
  public static Thread t;

  public static void world()
  // initial state
  /*:
     // requires "count = (card Thread) & (ALL tt. tt:Thread --> ~(tt..pc_bit_1) & ~(tt..pc_bit_0))"
     requires "  count = (card {tt. tt:Thread & ~(tt..pc_bit_1) & ~(tt..pc_bit_0)})
               & (ALL tt. tt:Thread --> ~(tt..pc_bit_1) & ~(tt..pc_bit_0))"
     modifies count, t, "Thread.pc_bit_0", "Thread.pc_bit_1"
     ensures "True"
  */
  {
    while
      /*: inv "  (count = (card {tt. tt:Thread & ~(tt..pc_bit_1) & ~(tt..pc_bit_0)}))
               & (ALL tt. ((tt:Thread & tt..pc_bit_1 & ~(tt..pc_bit_0)) --> count=0))
              ";
        // 11 of 14 sequents proved
      */ 
      /* inv "  (count = (card (Thread Int {tt. ~(tt..pc_bit_1) & ~(tt..pc_bit_0)})))
               & (ALL tt. ((tt:Thread & tt..pc_bit_1 & ~(tt..pc_bit_0)) --> count=0))
              ";
        // 10 of 14 sequents proved
      */ 
      /* inv "  (count = (card (Thread Int {tt. ~(tt..pc_bit_1) & ~(tt..pc_bit_0)})))
               & (ALL tt. ((tt:(Thread Int {tt. tt..pc_bit_1 & ~(tt..pc_bit_0)})) --> count=0))
              ";
      */ 
      (true) {
        //: havoc t;
        //: assume "(t:Thread) & (t~=null)";
        if(!t.pc_bit_1) {
          if(t.pc_bit_0) {
            // from B
            if(count==0) { t.pc_bit_1=true; t.pc_bit_0=false; }
          } else {
            // from A
            count=count-1;
            t.pc_bit_0=true;
          } // end if-else-
        } // end if-else-
      } // end while
  } //end world
} // end class
