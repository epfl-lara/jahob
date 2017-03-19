/** Soundness tests for encapsulation checks **/

class Encap12 {

    public /*: encap */ void encapMethod()
    {
	unencapMethod();
    }

    public void unencapMethod()
    {
    }
}