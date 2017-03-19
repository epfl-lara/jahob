/** Soundness tests for encapsulation checks **/

class Encap11 {

    static Object staticField;

    public /*: encap */ void encapMethodModifiesStaticField()
    {
	staticField = null;
    }
}