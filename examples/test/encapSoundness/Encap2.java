/** Soundness tests for encapsulation checks **/

class Encap2 {

    static Object staticField;

    private void encapParamStaticField(/*: encap */ Object encapObj)
    {
	staticField = encapObj;
    }

}