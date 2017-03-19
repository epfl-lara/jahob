class Node {
    Node next;
}
class Test {
    private static Object chooseObj() {
	return new Node();
    }

    private static Node chooseNode() {
	return new Node();
    }

    /*
    public static void main(String[] args)
    {
     Node x = (Node)chooseObj(); 
     Node y = (Node)chooseObj();
     if ((x != null) && (y != null) && (x.next==y.next)) {
	 assert x==y;
     }
    }
    */

    public static void test()
    {
     Node x = chooseNode(); 
     Node y = chooseNode();
     if ((x != null) && (y != null) && (x.next==y.next)) {
	 if (x!=y) {
	     // now x and y are not used any more, so we can \forall quantify?
	     boolean b;
	     //: havoc b;
	     //: assert "b";
	 }
     }
    }

}
