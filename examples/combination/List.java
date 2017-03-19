class List {
   private List next;
   private Object data;
   private static List root;
   private static int size;
   /*: private static specvar nodes :: objset = "{}";
     public static specvar content :: objset = "{}";
     vardefs "nodes == {n. n \<noteq> null \<and> (root,n) \<in> {(u,v). u..next=v}^*}";
     vardefs "content == {x.\<exists>n. x=n..data \<and> n \<in> nodes}";
     invariant sizeInv: "size = cardinality content";
     invariant treeInv: "tree [List.next]";
     invariant rootInv: "root \<noteq> null \<longrightarrow> (\<forall> n. n..next \<noteq> root)";
     invariant nodesAlloc: "nodes \<subseteq> alloc";
     //invariant contentAlloc: "content \<subseteq> alloc"; 
     */
   
   public static void addNew(Object x)
   /*: requires "comment ''xFresh'' (x \<notin> content)"
     modifies content
     ensures "content = old content \<union> {x}" */
   {
      List n1 = new List();
      n1.next = root; n1.data = x;
      root = n1; size = size + 1;
      /*: noteThat "nodes = {n1} \<union> old nodes";
        noteThat "comment ''newContent'' (content = {x} \<union> old content)";
        noteThat "theinv sizeInv" from sizeInv, xFresh, newContent; 
      */
   }

   public static void addNewNoHint(Object x)
   /*: requires "comment ''xFresh'' (x \<notin> content)"
     modifies content
     ensures "content = old content \<union> {x}"
   */
   {
      List n1 = new List();
      n1.next = root;
      n1.data = x;
      root = n1;
      size = size + 1;
      /* noteThat "nodes = {n1} \<union> old nodes";
	noteThat "content = {x} \<union> old content";
      */
   }

   public static void addBroken(Object x) // soundness test, should fail
   /*: requires "True"
     modifies content
     ensures "content = old content \<union> {x}"
   */
   {
      List n1 = new List();
      n1.next = root;
      n1.data = x;
      root = n1;
      size = size + 1;
      /*: noteThat "nodes = {n1} \<union> old nodes";
        noteThat "content = {x} \<union> old content";
        noteThat sizeOk: "theinv sizeInv";
      */
   }

   public static void init(Object x)
   /*: modifies content
     ensures "content = {}"
   */
   {
      root = null;
      size = 0;
      /*: noteThat "nodes = {}";
        noteThat "comment ''newContent'' (content = {})";
        noteThat sizeOk: "theinv sizeInv" from sizeInv, newContent;
      */
   }
   
   public static int getSize()
   //: ensures "result = cardinality content"
   {
      return size;
   }
   
   public static boolean member(Object x)
   //: ensures "result = (x \<in> content)"
   {
      List current = root;
      //: ghost specvar seen :: objset = "{}"
      while /*: inv "(current = null \<or> current \<in> nodes) \<and> 
	      seen = {n. n \<in> nodes \<and> (current,n) \<notin> {(u,v). List.next u=v}^*} \<and> 
	      (\<forall> n. n \<in> seen \<longrightarrow> List.data n \<noteq> x)" */
	 (current != null) {
	 if (current.data==x) {
	    return true;
	 }
	 //: seen := "seen \<union> {current}"
	 current = current.next;
      }
      //: noteThat seenAll: "seen = nodes";
      return false;
   }
}
