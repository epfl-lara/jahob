/*
  Current status: add, empty, getOne, and remove verify with Z3 and MONA.
 */
class Node {
    public /*: claimedby List */ Object data;
    public /*: claimedby List */ Node next;
}
class List // Instantiatable singly-linked list with data field and first field
{
   private Node first;

   /*: 
     private specvar inlist :: objset;
     private vardefs "inlist == {n. (first, n) : {(x,y). x..Node.next = y}^* & n ~= null}";

     public specvar content :: objset;
     vardefs "content == {x. x ~= null & (EX n. x = n..Node.data & n : inlist)}";

     invariant "(first, this) : {(x,y). x..Node.next = y}^* --> this = null";

     invariant "ALL n. n : inlist --> n..Node.data ~= null";

     //invariant "tree [List.first, Node.next]";

     invariant "ALL n m. n : inlist & m : inlist & n..Node.data = m..Node.data --> n = m";
   */

    public List()
    //: modifies content ensures "content = {}"
    {
        first = null;
    }
      
    public void add(Object o1)
    /*: requires "o1 ~= null"
        modifies content
        ensures "content = old content Un {o1}"
    */
    {
        Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
        //: noteThat "comment ''thisInlistInserted'' (inlist = old inlist Un {n})";
        //: noteThat "comment ''otherInlistSame''  (ALL (x::obj). x : Object.alloc & x : List & x ~= this --> x..List.inlist = old (x..List.inlist))";
    }

    public boolean empty()
    /*: ensures "result = (content = {})"; 
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
        ensures "result : content & result ~= null";
    */
    {
       //: noteThat "EX n. n : inlist";
       //: noteThat "first : inlist";
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
       //: inlist_curr := "inlist";
       //: noteThat "EX n. n : inlist";
       while /*: inv "inlist_curr = {n. (current,n) : {(x,y). x..Node.next = y}^* & n ~= null} &
               current ~= null &
               (EX n. o1 = n..Node.data & n : inlist_curr) &
	       (first,current) : {(x,y). x..Node.next = y}^* &
	       (prev ~= null --> prev..Node.next = current) &
	       (prev = null --> current = first)" */
	  (current.data != o1) {
	  //: inlist_curr := "inlist_curr - {current}";
	  prev = current;
	  current = current.next;
	  //: noteThat "(EX n. o1 = n..Node.data & n : inlist_curr)";
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

    public static void main(String[] args)
    {
        test();
    }

    public static void test()
    {
        List lst = new List();
        Object o1 = new Object();
        Object o2 = new Object();
        Object o3 = new Object();
        Object o4 = new Object();
        Object o5 = new Object();
        lst.add(o1);
        lst.add(o2);
        lst.add(o3);
        lst.add(o4);
        lst.remove(o2);
        lst.remove(o1);
        lst.remove(o4);
        //lst.remove(o5); // this should crash
        lst.remove(o3);
    }
}
