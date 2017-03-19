/*/////////////////////////////////////
 *//////////// Set ////////////////////
 /////////////////////////////////////*/
class Set
{
  public  Object element;
  Object current;
  private Set next;

   /*: 
    public ghost specvar content :: objset = "({} :: objset)";
    public ghost specvar iter :: objset = "({} :: objset)";
    public ghost specvar size :: int = "cardinality content"

    invariant "this = null --> this..content = {}";
    public ensured invariant "this..content \<subseteq> Object.alloc";
     invariant "this ~= null -->  this..element~=null";    
    */

  
    public static Set insert(Object x, Set l)
    /*: requires "x ~= null"
        ensures "result..content = l..content Un {x} 
	& Object.alloc = (old Object.alloc) Un {result}"
    */
    {
	Set r = new Set();
        r.element = x;
        r.next = l;
        //: "r..content" := "l..content Un {x}";
        return r;
    }

    public static boolean isEmpty(Set l)
    /*: requires "True"
	ensures "result = (l..content = {}) 
      & Object.alloc = old Object.alloc";
    */
    {
	return (l == null);
    }

   
   public static Set remove(Object n, Set l)
      /*: 
	requires "n : l..content"
    //    modifies "l..content", 
//		 "l..iter"
        ensures "comment ''elementRemoved'' ((result..content = l..content \<setminus> {n}) & 
					      (result..iter = l..iter \<setminus> {n}))"
      */
   {

      if (l == null) return l;

	if (n == l.element) {
	   //: "l..content" := "l..content - {n} ";
  	   //: "l..iter" := "l..iter - {n}";
	    return remove(n, l.next);
	} else
	    return insert(l.element, remove (n, l.next));
    }

   

  public void initIter()
      /*:
	requires "True" 
	modifies "this..iter"
        ensures "comment ''initIter'' (this..iter = this..content)"
      */
   {
      //: "this..iter" := "this..content";
      current = element;
   }

   public Object nextIter()
      /*: requires "EX x. x : this..iter" 
        modifies "this..iter"
	ensures "comment ''nextIter'' (this..iter = old this..iter - {result} & result : old this..iter)"
      */
    {
      Object n;
      n = current;
      //: "this..iter" := "this..iter - {n}"
      current = next.element;
      return n;
   }
		

    public static boolean member(Object x, Set l)
    /*: requires "True"
        ensures "result = (x : l..content)";
    */
    {
	if (l == null) {
            return false;
        }
	if (x == l.element) {
	    return true;
        }
	else {            
            // assume "False";
	    return member(x, l.next);
        }
    }
}
