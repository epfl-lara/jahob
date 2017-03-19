/*
 * List.java
 *
 * October 13, 2007
 * Simple and basic functional List implementing a set. Unsorted.

PLUS
 instantiable
 nil, cons, pattern-match like test, reverse, concat
MINUS
 it's just a functional list

 */

class Match // Match is a view of a representation-independent view of non-empty association list
{
    public Object data;
    public List rest;
}

class List 
{
   private Object data;
   private List next;

   /*: 
    public ghost specvar content :: "obj set" = "({} :: obj set)";

    public ensured invariant nullEmpty: "this = null --> content = {}"
    public ensured invariant emptyNull: "content = {} --> this = null"
    invariant contentDef: "this ~= null --> (content = {data} Un next..content)"
    invariant dataNonNull: "this ~= null --> data ~= null"
    invariant contentAlloc: "content \<subseteq> Object.alloc"
    */

   public static List nil() 
   /*: requires "True"
       ensures "result..content = {} & Object.alloc = old Object.alloc"
    */
   {
      return null;
   }
   
    public static List cons(Object x, List l)
    /*: requires "x ~= null"
        ensures "result..content = l..content Un {x} &
                 Object.alloc = old Object.alloc Un {result}"
    */
    {
	List r = new List();
        r.data = x;
        r.next = l;
        //: "r..content" := "l..content Un {x}";
        return r;
    }

    public static boolean is_nil(List l)
    /*: ensures "(result = (l..List.content = {})) & 
                 Object.alloc = old Object.alloc"; */
    {
        return (l==null);
    }

    public static List remove_all (Object x, List l)
    /*: requires "x ~= null"
        ensures "result..List.content = l..List.content - {x}";
    */
    {
	if (l == null) return null;
	if (x == l.data)
	    return remove_all(x,l.next);
	else
	    return cons(l.data, remove_all (x, l.next));
    }

    public static boolean member(Object x, List l)
    /*: requires "x ~= null"
        ensures "(result = (x : l..List.content))
	       & Object.alloc = old Object.alloc";
    */
    {
	if (l == null) return false;
        else
            if (x == l.data)
                return true;
            else
                return member(x, l.next);
    }

    public static Object getFirst(List l)
    /*: requires "l..content ~= {}"
        ensures "result ~= null & (result : l..content)
               & Object.alloc = old Object.alloc" */
    {
	return l.data;
    }

    public static List getRest(List l)
    /*: requires "l..content ~= {}"
        ensures "result..content \<subseteq> l..content" */
    {
	return l.next;
    }

    public static Match getMatch(List l) // decompose list into components
    /*: requires "l..content ~= {}"
      ensures "result ~= null 
      & result..Match.data ~= null 
      & l..content = {result..Match.data} Un result..Match.rest..content
      & Object.alloc = (old Object.alloc) Un {result}";
    */
    {
	Match m = new Match();
        m.data = l.data;
        m.rest = l.next;
	return m;
    }

    public static List reverse_append (List l, List acc)
    /*: requires "True"
        ensures "result..content = l..content Un acc..content" */
    {
	if (l == null) return acc;
	return reverse_append(l.next, cons(l.data, acc));
    }

    public static List reverse (List l)
    /*: requires "True"
        ensures "result..content = l..content" */
    {
	return reverse_append(l, nil());
    }

    public static List concat(List l1, List l2)
    /*: ensures "result..content = l1..content Un l2..content" */
    {
	// also shows how one can use list from outside, without rep
	List res = nil();
	if (is_nil(l1)) {
	    return l2;
	} else {
	    Match m = getMatch(l1);
	    return cons(m.data, concat(m.rest, l2));
	}
    }
}
