/** Soundness tests for encapsulation checks **/

class Encap8 {
    
    public void caller(Object unencapObj)
    {
	callee(unencapObj);
    }

    private void callee(/*: encap */ Object paramObj)
    {
    }

}