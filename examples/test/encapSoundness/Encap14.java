/** Soundness tests for encapsulation checks **/

class Encap14 {

    public /*: encap */ Encap14 encapMethod()
    {
	return new Encap14();
    }
}