/*
 * AssocList.java
 *
 * Created on June 24, 2006
 * Functional List
 */

class Pair
{
   public Object key;
   public Object value;
}

class AssocList 
{
   private Object key;
   private Object data;
   private AssocList next;

   /*: 
    public ghost specvar content :: "(obj * obj) set" = "({} :: (obj * obj) set)";

    public ensured invariant "this = null --> content = {}"
    public ensured invariant "content = {} --> this = null"
    invariant "this ~= null --> ( content = {(key, data)} Un next..content)"
    invariant "this ~= null --> data ~= null"
    invariant "this ~= null --> key ~= null"
    invariant "{v. (EX k. (k,v) : content)} \<subseteq> Object.alloc"
    invariant "{k. (EX v. (k,v) : content)} \<subseteq> Object.alloc"
    */

   public static AssocList nil() 
   /*: requires "True"
       ensures "result..content = {} & Object.alloc = old Object.alloc"
    */
   {
      return null;
   }
   
    public static AssocList cons(Object k, Object v, AssocList l)
    /*: requires "k ~= null & v ~= null"
        ensures "result..content = l..content Un {(k,v)} &
                 Object.alloc = old Object.alloc Un {result}"
    */
    {
	AssocList r = new AssocList();
        r.data = v;
	r.key = k;
        r.next = l;
        //: "r..content" := "l..content Un {(k,v)}";

        return r;
    }

    public static boolean is_nil(AssocList l)
    /*: ensures "result = (l..AssocList.content = {}) & Object.alloc = old Object.alloc";
    */
    {
        return (l==null);
    }


    public static AssocList remove_all (Object k, AssocList l)
    /*: requires "k ~= null"
        ensures "result..AssocList.content = l..AssocList.content - {(x,v). x=k}";
    */
    {
	if (l == null) return null;
	if (k == l.key)
	    return remove_all(k,l.next);
	else
	    return cons (l.key, l.data, remove_all (k, l.next));
    }

public static AssocList remove (Object k, Object v, AssocList l)
    /*: requires "k ~= null & v ~= null"
        ensures "result..AssocList.content = l..AssocList.content - {(k,v)}
	       & Object.alloc <= (old Object.alloc) Un AssocList";
    */
    {
	if (l == null) return null;
	if (k == l.key && v == l.data)
	    return remove(k,v, l.next);
	else
	    return cons (l.key, l.data, remove (k, v, l.next));
    }


 public static Object lookup (Object k, AssocList l)
    /*: requires "k ~= null"
        ensures "((k,result) : l..content & result ~= null) | 
	((ALL v. (k,v) ~: l..content) & result = null)";
    */
    {
	if (l == null) return null;
	if (k == l.key)
	    return l.data;
	else
	    return lookup(k, l.next);
    }

    public static Pair getOne (AssocList l)
    /*: requires "l..content ~= {}"
      ensures "result ~= null 
      & result..Pair.key ~= null 
      & result..Pair.value ~= null 
      & (result..Pair.key, result..Pair.value) : l..content & Object.alloc = (old Object.alloc) Un {result}";
    */
    {
	Pair p = new Pair();
	p.key = l.key;
	p.value = l.data;
	return p;   
    }
}
