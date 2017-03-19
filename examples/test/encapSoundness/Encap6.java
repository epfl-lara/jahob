/** Soundness tests for encapsulation checks **/

class Encap6 {

    private /*: encap */ Object encapObj; 

    private void encapFieldUnencapObj(Object unencapObj)
    {
	encapObj = unencapObj;
    }

}