/*
 * AssocList.java
 *
 * Created on June 24, 2006
 * Extended October 13, 2007
 * Functional Association List implementing a map.  Instantiable. Unsorted.

PLUS:
  -all basic operations on association list, 
   decomposition operations, 
   as well as reverse and concat
MINUS:
  -only functional
  -countKeys has very partial spec (would need BAPA for that)

 */

class Pair
{
   public Object key;
   public Object value;
}
class Match // Match is a view of a representation-independent view of non-empty association list
{
    public Object key;
    public Object value;
    public AssocList rest;
}

class AssocList 
{
   private Object key;
   private Object data;
   private AssocList next;

   /*: 
    public ghost specvar content :: "(obj * obj) set" = "({} :: (obj * obj) set)";

    public ensured invariant nullEmpty: "this = null --> content = {}"
    public ensured invariant emptyNull: "content = {} --> this = null"
    invariant contentDef: "this ~= null --> ( content = {(key, data)} Un next..content)"
    invariant dataNonNull: "this ~= null --> data ~= null"
    invariant keyNonNull: "this ~= null --> key ~= null"
    invariant valsAlloc: "{v. (EX k. (k,v) : content)} \<subseteq> Object.alloc"
    invariant keysAlloc: "{k. (EX v. (k,v) : content)} \<subseteq> Object.alloc"
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
    /*: ensures "(result = (l..AssocList.content = {})) & 
                 Object.alloc = old Object.alloc"; */
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

    public static AssocList update(Object k, Object v, AssocList l)
    /*: requires "k ~= null & v ~= null"
        ensures "result..AssocList.content = (l..AssocList.content - {(x,y). x=k}) Un {(k,v)}";
    */
    {
        return cons(k, v, remove_all(k, l));
        /*
	if (l == null) return cons(k, v, null);
        else 
            if (k == l.key)
                return cons(k, v, update(k, v, l.next));
            else
                return cons(l.key, l.data, update(k, v, l.next));
        */
    }

    public static boolean member(Object k, Object v, AssocList l)
    /*: requires "k ~= null & v ~= null"
        ensures "(result = ((k,v) : l..AssocList.content))
	       & Object.alloc = old Object.alloc";
    */
    {
	if (l == null) return false;
        else
            if (k == l.key && v == l.data)
                return true;
            else
                return member(k, v, l.next);
    }

    public static int countKeys(Object k, AssocList l)
    /*: requires "k ~= null"
        ensures "result >= 0
               & Object.alloc = old Object.alloc";
    */
    {
	if (l == null) return 0;
        else
            if (k == l.key)
                return 1 + countKeys(k, l.next);
            else
                return countKeys(k, l.next);
    }

    public static AssocList remove (Object k, Object v, AssocList l)
    /*: requires "k ~= null & v ~= null"
        ensures "result..content = l..content - {(k,v)}
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
        ensures "( ((k,result) : l..content & result ~= null) | 
                   ((ALL v. (k,v) ~: l..content) & result = null)) & 
                 Object.alloc = old Object.alloc";
    */
    {
	if (l == null) return null;
	if (k == l.key)
	    return l.data;
	else
	    return lookup(k, l.next);
    }

    public static Pair getFirst(AssocList l)
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

    public static AssocList getRest(AssocList l)
    /*: requires "l..content ~= {}"
        ensures "result..content \<subseteq> l..content" */
    {
	return l.next;
    }

    public static Match getMatch(AssocList l) // decompose list into components
    /*: requires "l..content ~= {}"
      ensures "result ~= null 
      & result..Match.key ~= null 
      & result..Match.value ~= null 
      & l..content = {(result..Match.key, result..Match.value)} Un result..Match.rest..content
      & Object.alloc = (old Object.alloc) Un {result}";
    */
    {
	Match m = new Match();
	m.key = l.key;
        m.value = l.data;
        m.rest = l.next;
	return m;
    }

    public static AssocList reverse_append (AssocList l, AssocList acc)
    /*: requires "True"
        ensures "result..content = l..content Un acc..content" */
    {
	if (l == null) return acc;
	return reverse_append(l.next, cons(l.key, l.data, acc));
    }

    public static AssocList reverse (AssocList l)
    /*: requires "True"
        ensures "result..content = l..content" */
    {
	return reverse_append(l, nil());
    }

    public static AssocList concat(AssocList l1, AssocList l2)
    /*: ensures "result..content = l1..content Un l2..content" */
    {
	// also shows how one can use list from outside, without rep
	AssocList res = nil();
	if (is_nil(l1)) {
	    return l2;
	} else {
	    Match m = getMatch(l1);
	    return cons(m.key, m.value, concat(m.rest, l2));
	}
    }
}
