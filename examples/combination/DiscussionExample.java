class List {
    private List next;
    private Object data;

    private static List root;
    private static int size;

    /*:
      private static ghost specvar nodes :: objset;
      private static ghost specvar content :: objset;

      invariant nodesDef: "nodes = {n. n ~= null & rtrancl_pt (% u v. List.next u=v) root n}";
      invariant contentDef: "content == {x. EX n. x=List.data n & n : nodes}";

      invariant famousI: "size = card content";
      invariant treness: "tree [List.next]";
      invariant rootAlone: "root ~= null --> (ALL n. List.next n ~= root)";
      invariant nodesAlloc: "nodes \<subseteq> Object.alloc";
      invariant contentAlloc: "content \<subseteq> Object.alloc";
     */

    public static void insert()
    /*: requires "True"
        ensures "True"
    */
    {
        List n1 = new List();
        List d1 = new Object();
        n1.next = root;
        n1.data = d1;
        root = n1;
        size = size + 1;
        /*: noteThat fresh: "d1 ~: content";
            nodes := "{n1} Un nodes";
            content := "{d1} Un content";
        */
    }
}
