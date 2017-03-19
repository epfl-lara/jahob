/*
 * AssocList.java
 *
 * Created on June 24, 2006
 * Functional List
 */
public final class AssocList 
{
   private Object key;
   private Object data;
   private AssocList next;

   /*: 
    public ghost specvar content :: "(obj * obj) set" = "({} :: (obj * obj) set)";

    invariant "this = null --> content = {}"
    invariant "content = {} --> this = null"
    invariant "this ~= null --> ( content = {(key, data)} Un next..content)"
    invariant "this ~= null --> data ~= null"
    invariant "this ~= null --> key ~= null"
    invariant "{v. (EX k. (k,v) : content)} \<subseteq> Object.alloc"
    invariant "{k. (EX v. (k,v) : content)} \<subseteq> Object.alloc"
    */

   public static AssocList nil() 
   /*: requires "True"
       ensures "result..AssocList.content = {}"
    */
   {
      return null;
   }
   
    public static AssocList cons(Object k, Object v, AssocList l)
    /*: requires "k ~= null & v ~= null"
        ensures "result..AssocList.content = l..AssocList.content Un {(k,v)}"
    */
    {
	return cons1(k,v,l);
    }

    private static AssocList cons1(Object k, Object v, AssocList l)
    /*: requires "k ~= null & v ~= null & theinvs"
        ensures "result..AssocList.content = l..AssocList.content Un {(k,v)} & theinvs"
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
    /*: ensures "result = (l..AssocList.content = {})";
    */
    {
        return (l==null);
    }



    public static AssocList remove_all (Object k, AssocList l)
    /*: requires "k ~= null"
        ensures "result..AssocList.content = l..AssocList.content - {(x,v). x=k}";
    */
    {
	return remove_all1(k, l);
    }


    private static AssocList remove_all1 (Object k, AssocList l)
    /*: requires "k ~= null & theinvs"
        ensures "result..AssocList.content = l..AssocList.content - {(x,v). x=k} & theinvs";
    */
    {
	if (l == null) return null;
	if (k == l.key)
	    return remove_all1(k,l.next);
	else
	    return cons1 (l.key, l.data, remove_all1 (k, l.next));
    }

    public static AssocList remove (Object k, Object v, AssocList l)
    /*: requires "k ~= null & v ~= null"
        ensures "result..AssocList.content = l..AssocList.content - {(k,v)}";
    */
    {
	return remove1(k,v,l);
    }

    private static AssocList remove1 (Object k, Object v, AssocList l)
    /*: requires "k ~= null & v ~= null & theinvs"
        ensures "result..AssocList.content = l..AssocList.content - {(k,v)} & theinvs";
    */
    {
	if (l == null) return null;
	if (k == l.key && v == l.data)
	    return remove1(k,v, l.next);
	else
	    return cons1 (l.key, l.data, remove1 (k, v, l.next));
    }


    public static Object lookup (Object k, AssocList l)
    /*: requires "k ~= null"
        ensures "((k,result) : l..content & result ~= null) | 
	((ALL v. (k,v) ~: l..content) & result = null)";
    */
    {
	return lookup1(k,l);
    }

    private static Object lookup1 (Object k, AssocList l)
    /*: requires "k ~= null & theinvs"
        ensures "(((k,result) : l..content & result ~= null) | 
	((ALL v. (k,v) ~: l..content) & result = null)) & theinvs";
    */
    {
	if (l == null) return null;
	if (k == l.key)
	    return l.data;
	else
	    return lookup1(k, l.next);
    }

 public static FuncList image (Object x, AssocList l)
    /*: requires "x ~= null"
        ensures "result..FuncList.content = {y. (x,y) : l..AssocList.content}";
    */
    {
	return image1(x,l);
    }

 private static FuncList image1 (Object x, AssocList l)
    /*: requires "x ~= null & theinvs"
        ensures "result..FuncList.content = {y. (x,y) : l..AssocList.content} & theinvs";
    */
    {
	if (l == null) 
	    return FuncList.nil();
	else {
	    if (x == l.key)
		return FuncList.cons(l.data, image(x, l.next));
	    else
		return image1(x, l.next);
	}
    }

 public static FuncList inverseImage (Object y, AssocList l)
    /*: requires "y ~= null"
        ensures "result..FuncList.content = {x. (x,y) : l..AssocList.content}";
    */
    {
	return inverseImage1(y,l);
    }

 private static FuncList inverseImage1 (Object y, AssocList l)
    /*: requires "y ~= null & theinvs"
        ensures "result..FuncList.content = {x. (x,y) : l..AssocList.content} & theinvs";
    */
    {
	if (l == null) 
	    return FuncList.nil();
	else {
	    if (y == l.data)
		return FuncList.cons(l.key, inverseImage1(y, l.next));
	    else
		return inverseImage1(y, l.next);
	}
    }

public static FuncList domain (AssocList l)
    /*: 
        ensures "result..FuncList.content = {x. EX y. (x,y) : l..AssocList.content}";
    */
    {
	return domain1(l);
    }

private static FuncList domain1 (AssocList l)
    /*: 
    requires "theinvs"   
    ensures "result..FuncList.content = {x. EX y. (x,y) : l..AssocList.content} & theinvs";
    */
    {
	if (l == null) 
	    return FuncList.nil();
	else {
	    return FuncList.cons(l.key, domain1(l.next));
	}
    }

}
