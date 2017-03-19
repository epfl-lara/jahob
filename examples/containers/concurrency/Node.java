public class Node {
	public Object data;
	public Node next;

    /*:
      public ghost specvar con :: objset = "{} :: objset";

      public ensured invariant ConAlloc: "con \<subseteq> Object.alloc";

      public invariant ConNull: "this = null --> con = {}";
      public invariant ConDef: "this ~= null --> 
	                            con = {this..data} Un next..con & 
	                            data ~: next..con";

	  static specvar edge :: "obj => obj => bool";
	  vardefs "edge == (% x y. (x : Node & y = x..Node.next))";

	  invariant ("Inj") "ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2";

    */

	/*
	  public specvar last_data :: object = "null";
	  vardefs "last_data == 
	*/

	public void test3(Object p)
	/*:
	  requires "(ALL n. n..Node.next ~= this) & p ~= null & p ~: this..next..con"
	  modifies con,data
	  ensures "p : this..con";
	 */
	{
		Object tmp = this.data;
		this.data = p;
		// "this..Node.con" := "(old this..Node.con \<setminus> {old this..Node.data}) Un {a}";
		// "this..Node.con" := "(old this..Node.con \<setminus> {tmp}) Un {a}";
		// "this..con" := "(this..con \<setminus> {tmp}) Un {p}";
		//: "this..con" := "this..next..con Un {p}";
	}

	public void test4(Object p)
	/*:
	  requires "(ALL n. n..Node.next ~= this) & p ~= null & p ~: this..con"
	  modifies con,data,next
	  ensures "p : this..con";
	 */
	{
		if (this.next == null) {
			this.data = p;
			//: "this..con" := "this..next..con Un {p}";
		}
		else {
			Node tmp = this.next;
			if (tmp != null) {
				this.next = null;
				//: assert "p ~= null & p ~: tmp..con";
				//: assert "(ALL n. n..Node.next ~= tmp)";
				tmp.test4(p);
				this.next = tmp;
				//: "this..con" := "tmp..con Un {this..data}";
			}
		}
	}

}


//	public Node test2(Object a)
// 	/*:
// 	  ensures "result..con = {a}";
// 	 */
// 	{
// 		Node tmp = new Node();
// 		tmp.data = a;
// 		tmp.next = null;
// 		//: "tmp..con" := "{a}";
// 		return tmp;
// 	}

// 	public void test(Object a)
// 	/*:
// 	  requires "a ~= null"
// 	  modifies "this..Node.con"
// 	  ensures "this..Node.con = {a}";
// 	 */
// 	{
// 		Object tmp = this.data;
// 		this.data = a;
// 		// "this..Node.con" := "(old this..Node.con \<setminus> {old this..Node.data}) Un {a}";
// 		// "this..Node.con" := "(old this..Node.con \<setminus> {tmp}) Un {a}";
// 		//: "this..Node.con" := "(this..Node.con \<setminus> {tmp}) Un {a}";
// 		this.next = null;
// 		//: "this..Node.con" := "{a}";
// 	}

// 	public void test1(Node p)
// 	/*:
// 	  requires "this..Node.data ~: p..Node.con"
// 	  modifies "this..Node.next"
// 	  ensures "this..Node.next = p";
// 	 */
// 	{
// 		this.next = p;
// 		// "this..Node.next" := "p";
// 		//: "this..Node.con" := "{this..Node.data} Un p..Node.con";
// 	}

// 	public void test4(Object a)
// 	/*:
// 	  modifies con
// 	  ensures "a : con";
// 	*/
// 	{
// 		if (!member(a)) {
// 			Object tmp = data;
// 			data = a;
// 			// "con" := "(old con \<setminus> {tmp}) Un {a}";
// 			//: "con" := "(con \<setminus> {tmp}) Un {a}";
// 			// "con" := "(old con \<setminus> {old data}) Un {a}";
// 			// assume "False";
// 		}
// 		else { 
// 			//: assume "False"; 
// 		}
// 	}

//     private boolean member1(Object o1)
//     /*:
//         ensures "result = (o1 : con)"
//     */
//     {
//         Node current = this;
//         while /*: inv "current : Node & current : Object.alloc & 
//                        (o1 : con) = (o1 : current..Node.con)" */
//             (current != null) {
//             if (current.data==o1) {
//                 return true;
//             }
//             current = current.next;
//         }
//         return false;
//     }

// 	public boolean member(Object o)
// 	/*:
// 	  ensures "result = (o : con)";
// 	 */
// 	{
// 		return member1(o);
// 	}
// }
