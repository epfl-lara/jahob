/** Soundness tests for encapsulation checks **/

class Encap3 {

    private Object encapParamReturned(/*: encap */ Object encapObj)
    {
	return encapObj;
    }

}