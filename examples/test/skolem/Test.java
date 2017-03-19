class Test {
    // Soundness testing for name clashes

    public Test another;
    public int x;

    
    public void changeThis() 
    /*:
      requires "x = 3"
      ensures "ALL this. this : Object.alloc & this : Test & 
                         this ~= null --> this..x = 3";
     */
    {
    }

    public void change(Test t) 
    /*:
      requires "t..x = 3"
      ensures "ALL t. t : Object.alloc & t : Test & 
                         t ~= null --> t..x = 3";
     */
    {
    }

}
