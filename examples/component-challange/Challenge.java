class Component {
    Component parent;
    Component left, right;
    int val;
    /*:
      public ghost specvar sum :: "int" = "0";
      public ghost specvar ok :: "bool";
      invariant sumInv: "ok --> (sum = val + left..sum + right..sum)";
      invariant parentLeftInv: "left ~= null --> left..parent = this";
      invariant parentRightInv: "right ~= null --> right..parent = this";
      invariant rootInv: "this ~= null & parent = null --> 
        (ALL x. x..left ~= this & x..right ~= this)";
     */

    public void addLeft(Component sub)
    /*:
      requires "(ALL x. x ~= null --> x..ok) & 
                left = null & sub ~= null & sub..parent = null" 
      modifies "ok"
      ensures "left = sub & ok"
     */
    {
	left = sub;
	sub.parent = this;
	//: ok := "False"
	update();
    }

    public void update()
    /*:
      requires "~ok & (ALL x. x ~= null & x ~= this --> x..ok)"
      modifies "Component.sum", "Component.ok"
      ensures "(ALL x. x ~= null --> x..ok) & val = old val"
     */
    {
	//: sum := "val + left..sum + right..sum"
	//: ok := "True"
	if (parent != null) {
	    //: "parent..ok" := "False";
	    parent.update();
	}
    }
}
