public class Thread {
  public static Thread t;
  public static int count;
  public static boolean b;
  /*:
    public static ghost specvar A :: objset;
    public static ghost specvar B :: objset;
    public static ghost specvar C :: objset;
  */

  public static void world()
  // initial state
  /*:
     requires "  count >= (card A) & (B===\<emptyset>) & (C===\<emptyset>) & (A \<subseteq> Thread) & (ALL t1. ((t1:Thread) --> t1~=null))"
     modifies count, t, A, B, C
     ensures "True"
  */
  {
    while
      /* having a conjunct (ALL t2. ((t2:Thread) --> t2~=null)) is not a problem, if null is not a pre-assumed object */ 
      /*: inv "  (count >= (card A))  & ((A Un B Un C) \<subseteq> Thread) & ((A Int B) === \<emptyset>) & ((A Int C)===\<emptyset>) & ((B Int C)===\<emptyset>)
               & ((C === \<emptyset>) | count=0)
              ";
      */ 
      (true) {
        //: havoc b;
        //: havoc t;
        if(b) {
	  // from A
          //: assume "t:A";
          count=count-1;
          /*:
            A := "A \<setminus> {t}";
            B := "B Un {t}";
	  */
	} else {
          //from B
          //: assume "t:B";
          if(count==0) { 
            /*:
              B:="B \<setminus> {t}";
              C:="C Un {t}";
	    */
	    // That's what we want to show:
            //: assert "A === \<emptyset>"
          } // end if(count==0)
        } // end if(b) else-
      } // end while(true)
  } //end world()

  public static void world_failing()
  // initial state
  /*:
     requires "count = (card A)-1 & (B===\<emptyset>) & (C===\<emptyset>) & (A \<subseteq> Thread) & (ALL t1. ((t1:Thread) --> t1~=null))"
     modifies count, t, A, B, C
     ensures "True"
  */
  {
    while
      /* having a conjunct (ALL t2. ((t2:Thread) --> t2~=null)) is not a problem, if null is not a pre-assumed object */ 
      /*: inv "  (count = (card A)-1)  & ((A Un B Un C) \<subseteq> Thread) & ((A Int B) === \<emptyset>) & ((A Int C)===\<emptyset>) & ((B Int C)===\<emptyset>)
               & ((C === \<emptyset>) | count=0)
              ";
      */ 
      (true) {
        //: havoc b;
        //: havoc t;
        if(b) {
	  // from A
          //: assume "t:A";
          count=count-1;
          /*:
            A := "A \<setminus> {t}";
            B := "B Un {t}";
	  */
	} else {
          //from B
          //: assume "t:B";
          if(count==0) { 
          /*:
            B:="B \<setminus> {t}";
            C:="C Un {t}";
	  */
	  // That's what has to fail:
          //: assert "A === \<emptyset>"
          } // end if(count==0)
        } // end if(b) else-
      } // end while(true)
  } //end world_failing()
} // end class
