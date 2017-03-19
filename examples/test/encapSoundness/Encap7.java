/** Soundness tests for encapsulation checks **/

class Encap7 {
    
    public void caller()
    {
	Object someObj = new Object();
	callee(someObj);
    }

    private void callee(/*: encap+ */ Object paramObj)
    {
    }

}