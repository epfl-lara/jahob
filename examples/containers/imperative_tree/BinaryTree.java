public class BinaryTree {

   private static Node root;

   /*:
     static specvar reach :: "obj => obj => bool"
     vardefs "reach == (% x y. rtrancl_pt (% a b. a..Node.left = b | a..Node.right = b) x y)"; 

     static specvar nodes :: "obj => obj set";
     vardefs "nodes == (% n. {x. reach n x})";

     static specvar keys :: "obj => int set";
     vardefs "keys == (% n. {x. EX y. y : nodes n & y ~= null & y..Node.key = x})";

     public static specvar content :: "int set";
     vardefs "content == keys root";
     
     invariant "tree [Node.left, Node.right]";

     invariant "ALL n. n..Node.left = root | n..Node.right = root --> root = null";
     
     invariant leftKeysSmaller: "ALL n k. n ~= null & n : nodes root & k : keys (n..Node.left) --> k < n..Node.key"; 

     invariant rightKeysGreater: "ALL n k. n ~= null & n : nodes root & k : keys (n..Node.right) --> ~(k < n..Node.key)"; 
		       
   */

    public static void add(int key) 
       /*:
	 requires "key ~: content"
	 modifies content
	 ensures "content = old content Un {key}"
       */
   {
      /*:
	ghost specvar oldparent :: obj;
      */

      Node parent = null;
      Node node = root;
      boolean wentLeft = false;
      while /*: inv "
	      (wentLeft & parent ~= null --> parent..Node.left = node & key < parent..Node.key) &
	      (~wentLeft & parent ~= null --> parent..Node.right = node & ~(key < parent..Node.key)) &
	      parent : nodes root & 
	      node : nodes root &
	      (parent = null --> node = root) &
	      (parent ~= null --> (ALL n. n ~= null & n : nodes root & parent : nodes (n..Node.left) --> key < n..Node.key)) &  
	      (parent ~= null --> (ALL n. n ~= null & n : nodes root & parent : nodes (n..Node.right) --> ~(key < n..Node.key)))	  
	      " 
	    */
	 (node != null) {
	 wentLeft = (node.key > key);
	 //: oldparent := "parent";
	 if (wentLeft) {
	    parent = node;
	    node = node.left;
	 } else {
	    parent = node;
	    node = node.right;
	 }
	 //: noteThat "oldparent = null --> (ALL n. parent ~: nodes (n..Node.left) & parent ~: nodes (n..Node.right))";
	 /*: 
	   noteThat "oldparent ~= null & oldparent..Node.left = parent -->
	                 {n. parent : nodes (n..Node.left)} = {n. oldparent : nodes (n..Node.left)} Un {oldparent} &
			 {n. parent : nodes (n..Node.right)} = {n. oldparent : nodes (n..Node.right)}";
	   noteThat "oldparent ~= null & oldparent..Node.right = parent --> 
	                 {n. parent : nodes (n..Node.left)} = {n. oldparent : nodes (n..Node.left)} &
			 {n. parent : nodes (n..Node.right)} = {n. oldparent : nodes (n..Node.right)} Un {oldparent}";
	 */
      }

      Node newNode = new Node();
      newNode.key = key;
      //: noteThat "newNode ~: nodes root";
      //: noteThat "ALL x. x : nodes null <-> x = null";
      if (parent == null) {
	 root = newNode;
      } else if (wentLeft) {
	 parent.left = newNode;
      } else {
	 parent.right = newNode;
      }
      /*:
	noteThat "ALL n. n ~= null & n : old (nodes root) & n ~= parent & newNode : nodes (n..Node.left) --> 
	        parent : nodes (n..Node.left)"
	noteThat "ALL n. n ~= null & n : old (nodes root) & n ~= parent & newNode : nodes (n..Node.right) --> 
	        parent : nodes (n..Node.right)"

	noteThat "parent ~= null --> (ALL n. parent : nodes n --> nodes n = old (nodes n) Un {newNode})";
	noteThat "parent ~= null --> (ALL n. parent ~: nodes n --> nodes n = old (nodes n))";
	noteThat "nodes newNode = {newNode} Un {null}";

	noteThat "wentLeft --> newNode ~: nodes (parent..Node.right)";
	noteThat "~wentLeft --> newNode ~: nodes (parent..Node.left)";
	noteThat "ALL n. n ~= null & n : old (nodes root) & newNode : nodes (n..Node.left) --> key < n..Node.key";
	noteThat "ALL n. n ~= null & n : old (nodes root) & newNode : nodes (n..Node.right) --> ~(key < n..Node.key)";
      */
   }

   
   public static void remove(int key)
     /*:
       requires "key : content"
       modifies content
       ensures "content = old content - {key}"
     */
   {
      /*:
	ghost specvar oldparent :: obj;

	noteThat "(EX x. x ~= null & x : nodes root)";
      */

      Node parent = null;
      Node node = root;
      boolean wentLeft = false;
      while /*: inv "
	      (wentLeft & parent ~= null --> parent..Node.left = node & key < parent..Node.key) &
	      (~wentLeft & parent ~= null --> parent..Node.right = node & ~(key < parent..Node.key)) &
	      parent : nodes root & 
	      node : nodes root &
	      key : keys node &
	      node ~= null &
	      (parent = null --> node = root)
	      " */
	 (node.key != key){
	 wentLeft = (key < node.key);
	 //: noteThat "ALL i j k. i < j & ~(k < j) --> i ~= k"; 
	 //: noteThat "key ~= node..Node.key";
	 //: noteThat "ALL n. n ~= null --> nodes n = nodes (n..Node.left) Un nodes (n..Node.right) Un {n}"; 
	 //: noteThat "ALL n. n ~= null --> keys n = keys (n..Node.left) Un keys (n..Node.right) Un {n..Node.key}"; 
	 if(wentLeft){
	    //: noteThat "key < node..Node.key & (ALL k. k : keys (node..Node.right) --> ~(k < node..Node.key))";
	    //: noteThat "key ~: keys (node..Node.right)";
	    //: noteThat "key : keys (node..Node.left)";
	    //: noteThat "EX x. x ~= null & x : nodes (node..Node.left)";
	    parent = node;
	    node = node.left;
	 } else {
	    //: noteThat "~(key < node..Node.key) & (ALL k. k : keys (node..Node.left) --> k < node..Node.key)";
	    //: noteThat "key ~: keys (node..Node.left)";
	    //: noteThat "key : keys (node..Node.right)";
	    //: noteThat "EX x. x ~= null & x : nodes (node..Node.right)";
	    parent = node;
	    node = node.right;
	 }
      }

      Node newSubroot = null;
      
      if(node.left != null && node.right != null){
	 Node newSubrootParent = null;
	 newSubroot = node.left;
	 while /*: inv "
		 newSubrootParent : nodes (node..Node.left) & 
		 newSubroot : nodes (node..Node.left) & 
		 newSubroot ~= null &
		 (newSubrootParent ~= null --> newSubrootParent..Node.right = newSubroot) &
		 (newSubrootParent = null --> newSubroot = node..Node.left)
		 "; */
	       (newSubroot.right != null){
	    newSubrootParent = newSubroot;
	    newSubroot = newSubroot.right;
	 }

	 if(newSubrootParent != null){
	    newSubrootParent.right = newSubroot.left;
	    newSubroot.left = node.left;
	 }
	 newSubroot.right = node.right;

      } else if(node.left == null){
	 newSubroot = node.right;
      } else if(node.right == null){
	 newSubroot = node.left; 
      }

      node.left = null;
      node.right = null;

      if (parent == null){
	 root = newSubroot;
      } else if(wentLeft){
	 parent.left = newSubroot;
      } else {
	 parent.right = newSubroot;
      }
      
      //: assert "tree [Node.left, Node.right]";
      //: assert "ALL n. n..Node.left = root | n..Node.right = root --> root = null";
      //: assume "False";
   }
}
