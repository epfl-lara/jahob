/** Soundness tests for encapsulation checks **/

class Encap9 {

    private Object randomField;
    
    public /*: encap */ void encapMethodModifiesUnencap(Encap9 unencapObj)
    {
	unencapObj.randomField = null;
    }
}