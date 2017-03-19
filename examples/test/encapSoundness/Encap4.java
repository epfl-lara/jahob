/** Soundness tests for encapsulation checks **/

class Encap4 {

    private /*: encap */ Object[] encapArr; 

    private void encapFieldEncapPlusParam(/*: encap+ */ Object[] encapPlusArr)
    {
	encapArr = encapPlusArr;
    }

}