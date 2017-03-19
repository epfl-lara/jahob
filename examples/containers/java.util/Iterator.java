public class Iterator {
   /*:
     public specvar content :: objset;
     public specvar collection :: obj;
     vardefs "content == {}";
     vardefs "collection == null";

     public invariant "content \<subseteq> collection..Set.content";
     public invariant "ALL (this :: obj). this : Iterator & this ~: Object.alloc --> this..content = {}";
   */
   
   public Iterator(Set s)
   /*: 
     requires "s ~= null"
     modifies content, collection
     ensures "content = s..Set.content & collection = s";
   */
   {  
   }

   public boolean hasNext()
   //: ensures "result = (content ~= {})";
   {
      return false;
   }

   public Object next()
   /*:
     requires "content ~= {}"
     modifies content
     ensures "result : old content & content = old content - {result}";
   */
   { 
      return null;
   }
}