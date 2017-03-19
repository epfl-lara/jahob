public class Test {

   public static void main(String[] args) {

	Node smallest, nbor;
	
 	System.out.println("Empty tree: " + Tree.isEmpty()); 	
	Tree.add(2);
 	System.out.println("Empty tree: " +Tree.isEmpty()); 
 	System.out.println();

 	smallest = Tree.findSmallestLeaf();
	nbor = TreeUtil.findNeighbor(smallest);
	System.out.println("Find neighbor test with 1 leaf");
	if(nbor == null)
		System.out.println("Neighbor of " + smallest.v + " is null");
	else
		System.out.println("Error: neighbor of " + smallest.v + " is " + nbor.v);
	System.out.println();
	
	Tree.add(1);
	
	smallest = Tree.findSmallestLeaf();

	nbor = TreeUtil.findNeighbor(smallest);
	System.out.println("Find neighbor test with 2 leaves");
	System.out.println("Neighbor of " + smallest.v + " is " + nbor.v);
	System.out.println();
	
	Tree.add(3);
	nbor = TreeUtil.findNeighbor(smallest);
	System.out.println("Find neighbor test with 3 leaves");
	System.out.println("Neighbor of " + smallest.v + " is " + nbor.v);
	nbor = TreeUtil.findNeighbor(smallest.next);
	System.out.println("Neighbor of " + smallest.next.v + " is " + nbor.v);
	System.out.println();

	Tree.add(4);
	
	System.out.println("Find neighbor test with 4 leaves");
	nbor = TreeUtil.findNeighbor(smallest);
	System.out.println("Neighbor of " + smallest.v + " is " + nbor.v);
	nbor = TreeUtil.findNeighbor(smallest.next);
	System.out.println("Neighbor of " + smallest.next.v + " is " + nbor.v);
	nbor = TreeUtil.findNeighbor(smallest.next.next);
	System.out.println("Neighbor of " + smallest.next.next.v + " is " + nbor.v);	
	System.out.println();
	
	System.out.println("In-order tree traversal:");
	TreeUtil.printTree();
   	System.out.println();
   	System.out.println("List traversal following next fields:");
   	TreeUtil.printList();
   	System.out.println();
   	
    }


}
