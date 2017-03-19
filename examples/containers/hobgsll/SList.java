class Node {
    public /*: claimedby List */ Node next;
}
class List
{
   private static Node first;  
   /*:
     public static specvar content :: objset;
     vardefs "content == {x. x ~= null & (first,x) : {(v,w). v..Node.next=w}^*}";

     public static specvar pointed :: "obj => bool";
     public vardefs "pointed == (% n. EX x. x ~= null & x..Node.next = n)";

     invariant firstUnaliased: "first ~= null --> ~ pointed first";
     invariant isTree: "tree [Node.next]";
   */

    public static void add(Node n)
    /*: requires "n ~: content & n ~= null & n..Node.next = null & ~ pointed n"
        modifies content, pointed
        ensures "comment ''post'' (content = old content Un {n})"
    */
    {
	n.next = first;
	first = n;
    }
}
