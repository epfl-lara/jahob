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
     requires "  count >= (card {tt. tt~=null & tt:Thread})
               & (ALL tt. ((tt~=null & tt:Thread) --> ~(tt..pc_bit_1) & ~(tt..pc_bit_0)))
              "
     modifies count, t, "Thread.pc_bit_0", "Thread.pc_bit_1"
     ensures "True"
  */
  /*
     requires "  count >= (card {tt. tt~=null & tt:Thread})
               & (ALL tt. ((tt~=null & tt:Thread) --> ~(tt..pc_bit_1) & ~(tt..pc_bit_0)))
               & (card {tt. tt~=null & tt:Thread & tt..pc_bit_1 & ~tt..pc_bit_0}) = 0
              "
     modifies count, t, "Thread.pc_bit_0", "Thread.pc_bit_1"
     ensures "True"
  */
  {
    while
      /*: inv "  (count >= (card ({tt. tt~=null & tt:Thread & ~(tt..pc_bit_1) & ~(tt..pc_bit_0)})))
               & (ALL tt. ((tt~=null & tt:Thread & tt..pc_bit_1 & ~(tt..pc_bit_0)) --> count=0))
              ";
      */
      /* inv "  (count >= (card ({tt. tt~=null & tt:Thread & ~(tt..pc_bit_1) & ~(tt..pc_bit_0)})))
              & ((card {tt. tt~=null & tt:Thread & tt..pc_bit_1 & ~tt..pc_bit_0}) = 0 | count=0)
             ";
      */
      // Remark that Isabelle would allow writing the type after the identifier, as in {tt::obj. ...}.
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
          } // end if(t.pc_bit_0)-else-
        } // end if(!t.pc_bit_1)-else-
      } // end while
  } //end world
} // end class
