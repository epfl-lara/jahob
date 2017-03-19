public class Comparable {

    private final int key;

    /*: public static specvar compFunc :: "(obj \<Rightarrow> obj \<Rightarrow> int)";
        vardefs "compFunc == 
	  (\<lambda> o1. 
	    (\<lambda> o2.
	      if (o1 = null) then 
	        (if (o2 = null) then 0 else -1) else 
		(if (o2 = null) then 1 else
	          (if ((o1..key - o2..key) < 0) then -1 else
		    (if ((o1..key - o2..key) > 0) then 1 else 0)))))";

	ensured invariant ReflexiveInv:
	"\<forall> x. compFunc x x = 0"

	ensured invariant TransitiveInv:
	"\<forall> x y z. 0 \<le> compFunc x y \<and> 0 \<le> compFunc y z \<longrightarrow> 0 \<le> compFunc x z"

    */

    public int compareTo(Comparable o1)
    //: ensures "result = compFunc this o1 \<and> alloc = old alloc"
    {
	if (o1 == null)
	    return 1;

	int ct = key - o1.key;

	if (ct < 0)
	    return -1;

	if (ct > 0)
	    return 1;

	return 0;
    }
}