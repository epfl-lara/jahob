/** Soundness tests for encapsulation checks **/

class Encap13 {

    public /*: encap */ void encapCaller(Encap13 unencapObj)
    {
	unencapObj.encapCallee();
    }

    public /*: encap */ void encapCallee()
    {
    }
}