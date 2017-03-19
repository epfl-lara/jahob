/** Soundness tests for encapsulation checks **/

class Encap10 {

    public /*: encap */ void encapMethodModifiesUnencap(Object[] unencapArr)
    {
	unencapArr[0] = null;
    }
}