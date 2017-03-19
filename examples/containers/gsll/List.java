public class List // Global singly linked list with data fields and no duplicates
{
   private static Node first;
   private static int size;
    /*:
      private static specvar inlist :: objset;
      private vardefs "inlist == {n. (first, n) : {(x, y). x..Node.next = y}^* & n ~= null}";
      
      public static specvar content :: objset;
      vardefs "content == {x. EX n. x = n..Node.data & n : inlist}";

      invariant "tree [Node.next]";

      invariant "ALL n. n : inlist --> n..Node.data ~= null";

      invariant "first ~= null --> (ALL n. n..Node.next ~= first)";

      invariant DataInjective: "ALL n m. n : inlist & m : inlist & n..Node.data = m..Node.data --> n = m";
    
      invariant "size = card content"
    */
    
    public static void add(Object o1)
    /*: requires "o1 ~: content & o1 ~= null & o1 ~: Node"
        modifies content
        ensures "comment ''elementInserted'' (content = old content Un {o1})"
    */
    {
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
	size = size + 1;
    }

    public static boolean empty()
    /*: ensures "result = (content = {})";
    */
    {
        boolean b = (size==0);
        return b;
    }

    public static Object getOne()
    /*: requires "EX x. x : content"
        ensures "result : content";
    */
    {
       //: noteThat "first..data : content";
        return first.data;
    }


    public static void remove (Object o1)
    /*: requires "o1 : content"
        modifies content
	ensures "content = old content - {o1}"
     */
    {
       Node prev = null;
       Node current = first;
       while (current.data != o1) {
	  prev = current;
	  current = current.next;
       }
       if(prev != null){
	  prev.next = current.next;
	  current.next = null;
       } else {
	  first = first.next;
	  current.next = null;
       } 
       size = size - 1;
    }

}
