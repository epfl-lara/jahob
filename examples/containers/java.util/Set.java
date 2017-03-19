public class Set {
    /* Interface of a bounded set of objects.

       Please ignore implementation. This is just an interface.*/

    /*: 
      public specvar content :: objset;

      vardefs "content == {}";
    */

    public Set() 
    /*:
      modifies content
      ensures "content = {}";
     */
    {}

    public boolean isEmpty()
    /*:
      ensures "result = (content = {})";
     */
    {
        return false;
    }

    public boolean contains(Object x)
    /*:
      ensures "result = (x : content)";
     */
    {
       return false;
    }

    public boolean add(Object x)
    /*:
      modifies content
      ensures "content = old content Un {x} 
             & result = (x ~: old content)";
     */
    {
       return false;
    }

    public boolean remove(Object x)
    /*:
      modifies content
      ensures "content = old content - {x}
             & result = (x : old content)";
     */
    {
       return false;
    }

   public Iterator iterator()
      /*: 
        ensures "result ~= null & 
                 result..Iterator.content = content & 
                 result..Iterator.collection = this";
      */
   {
      return null;
   }


   public void clear()
      /*:
	ensures "content = {}"
      */
   {}

}
