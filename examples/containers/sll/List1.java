/*
  Current status: add, empty, getOne verify.
  Remove is close to verifying
 */
public class Node {
    public /*: claimedby List */ Object data;
    public /*: claimedby List */ Node next;
}
public final class List 
{
   private Node first;

   /*: 
     private specvar inlist :: objset;
     private vardefs "inlist == {n. rtrancl_pt (% x y. Node.next x = y) first n & n ~= null}";

     public specvar content :: objset;
     vardefs "content == {x. (EX n. x = n..Node.data & n : inlist)}";

     invariant "tree [List.first, Node.next]";

     //invariant "ALL n m. n : inlist & m : inlist & n..Node.data = m..Node.data --> n = m";

     //public ensured invariant "content \<subseteq> Object.alloc";
   */

    public List()
    //: modifies content ensures "ALL x. x ~: content"
    {
        first = null;
    }
      
    public void add(Object o1)
    /*: requires "o1 ~: content"
        modifies content
        ensures "content = old content Un {o1}"
    */
    {
        Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
        //: noteThat "thisInlistInserted": "inlist = old inlist Un {n} & n ~: old inlist";
        //: assert "content = old content Un {o1}";
        //: assume "False";
    }

    public boolean empty()
    /*: ensures "((ALL x. x ~: content) --> (result=True)) & ((EX x. x : content) --> (result=False))";
    */
    {
        if (first==null) {
            //: noteThat "ALL x. x ~: inlist";
            return true;
        } else {
            //: noteThat "EX x. x : inlist";
            return false;
        }
    }

    public Object getOne()
    /*: requires "EX x. x : content"
        ensures "result : content";
    */
    {
        //: noteThat "comment ''B'' (first : inlist)";
        return first.data;
    }

    public void remove (Object o1)
    /*: requires "o1 : content"
        modifies content
	ensures "content = old content - {o1}"
     */
    {
       /*:
	 private ghost specvar inlist_curr :: objset;
       */
       Node prev = null;
       Node current = first;
       //: noteThat "EX x. x : inlist";
       //: inlist_curr := "inlist";
       while /*: inv "inlist_curr = {n. rtrancl_pt (% x y. Node.next x = y) current n & n ~= null} &
               current ~= null &
               (EX n. o1 = n..Node.data & n : inlist_curr) &
	       rtrancl_pt (% x y. Node.next x = y) first current &
	       (prev ~= null --> prev..Node.next = current) &
	       (prev = null --> current = first)" */
	  (current.data != o1) {
	  //: inlist_curr := "inlist_curr - {current}";
	  prev = current;
	  current = current.next;
	  /*: noteThat "(EX n. o1 = n..Node.data & n : inlist_curr)";
              noteThat "inlist_curr = {n. rtrancl_pt (% x y. Node.next x = y) current n & n ~= null}";
              noteThat "(ALL n. n : inlist_curr --> n ~= null & current : inlist)";
          */
       }
       if(prev != null){
	  prev.next = current.next;
	  current.next = null;
       } else {
	  first = first.next;
	  current.next = null;
       }
       //: noteThat "comment ''currentNotInInlist'' (inlist = old inlist - {current})";
       //: noteThat "comment ''otherInlistSame'' (ALL (x::obj). x : Object.alloc & x : List & x ~= this --> x..inlist = old (x..inlist))";
       //: noteThat "comment ''otherContentSame'' (ALL (x::obj). x : Object.alloc & x : List & x ~= this --> x..content = old (x..content))";
       // assert "tree [List.first, Node.next]";
       // assume "False";
    }

   public void remove1 (Object o1)
   /*: requires "o1 : content"
     modifies content
     ensures "content = old content - {o1}"
   */
   {
      if(first != null){
	 if (first.data==o1) {
	    first = first.next;
	 } else {
	    Node prev = first;
	    Node current = first.next;
	    boolean go = true;
	    while (go && (current!=null)) {
	       if (current.data==o1) {
		  prev.next = current.next;
		  go = false;
	       }
	       current = current.next;
	    }
	 }
      }
   }
}
