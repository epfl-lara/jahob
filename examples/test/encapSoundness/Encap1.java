/** Soundness tests for encapsulation checks **/

class Encap1 {

    private /*: encap */ Object encap_o;

    public void encapFieldUnencapObj(Encap1 unencapObj)
    {
	unencapObj.encap_o = null;
    }

}