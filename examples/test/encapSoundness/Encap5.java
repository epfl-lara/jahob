/** Soundness tests for encapsulation checks **/

class Encap5 {

    private /*: encap+ */ Object[] encapPlusArr; 

    private void encapArgEncapPlusField(/*: encap */ Object[] encapArr)
    {
	encapPlusArr = encapArr;
    }

}