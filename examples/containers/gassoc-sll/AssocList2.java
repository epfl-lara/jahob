// Not finished
public final class AssocList 
    /* unsorted global association list with no duplicate keys */
{
    private static Node first;

    /*: 
      private static specvar inlist :: objset;
      vardefs
        "inlist == {n. n ~= null & rtrancl_pt (% x y. x..Node.next=y) AssocList.first n}";

      public static specvar content :: "(obj * obj) set";
      vardefs 
        "content == {(k,v). EX n. k = n..Node.key & v = n..Node.value & n : inlist}";

      private static specvar reach :: "obj => obj => bool";
      vardefs
        "reach == (% a b. rtrancl_pt (% x y. x..Node.next=y) a b)";

      invariant "ALL v. v : inlist --> (v..Node.key ~= null) & (v..Node.value ~= null)";

      invariant "ALL x y. x : inlist & y : inlist & x..key = y..key --> x = y";

      invariant "reach first null";
    */

    public static void init()
    /*: modifies content
        ensures "ALL x. x ~: content"
    */
    {
        first = null;
        //: noteThat "ALL x. x ~: inlist";
    }

    public static boolean isEmpty()
    /*: ensures "result = (content = {})";
    */
    {
        boolean res = (first==null);
        return res;
    }

    public static boolean defined(Object key)
    /*: ensures "result = (EX v. (key,v) : content)" */
    {
        Node n = first;
        while /*: inv "reach first n &
                       (ALL v. v ~= null & reach first v & ~ reach n v --> v..Node.key ~= key)" */
            (n != null) {
            if (n.key==key) {
                return true;
            }
            n = n.next;
        }
        return false;
    }

    public static Object lookup(Object key)
    /*: ensures "(key,result) : content | 
                 (ALL v. (key,v) ~: content)" */
    {
        Node n = first;
        while /*: inv "reach first n &
                       (ALL v. v ~= null & reach first v & ~ reach n v --> v..Node.key ~= key)" */
            (n != null) {
            if (n.key==key) {
                return n.value;
            }
            n = n.next;
        }
        return null;
    }

    public static void remove(Object key)
    /*: requires "key ~= null & (EX v. (key,v) : content)"
        modifies content
        ensures "content = old content - {(x,y). x = key}"
    */
    {
       Node prev = null;
       Node n = first;
       while /*: inv "n ~= null &
	              (prev ~= null --> reach first prev & prev..next = n) &
	              (prev = null --> first = n) &
                      (EX v. v ~= null & reach n v & v..Node.key = key) &
                      (ALL v. v ~= null & reach first v & ~ reach n v --> v..Node.key ~= key)" */
	  (n.key != key) {
	  prev = n;
	  n = n.next;
       }

       if (prev == null) {
	  first = first.next;
       } else {
	  prev.next = n.next;
	  //: noteThat "inlist = inlist - {n}";
       }
    }

    public static void add(Object key, Object value)
    /*: requires "key ~= null & value ~= null"
        modifies content
        ensures "content = (old content - {(x,y). x=key}) Un {(key,value)}"
    */
    {
        Node n = first;
        while /*: inv "reach first n &
                       (ALL v. v ~= null & reach first v & ~ reach n v --> v..Node.key ~= key)" */
            ((n != null) && (n.key != key)) {
            n = n.next;
        }
        if (n==null) {
            n = new Node();
            n.key = key;
            n.value = value;
            n.next = first;
            first = n;
        } else {
            n.value = value;
        }
    }
}
