//////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////
//
//		  Dijkstra Program
//	Verification Case Study using Jahob
//	   By Robin Mange & Jonathan Kuhn
//
//////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////

class Node
{
	public /*: claimedby Dijkstra */ int x,y;
	public /*: claimedby Dijkstra */ Path[] paths;
	public /*: claimedby Dijkstra */ int nb_paths;
}

class Path
{
	public /*: claimedby Node */ int dest;
	public /*: claimedby Node */ int value;
}

//////////////////////////////////////////////////////////
//Vector Class simulating the Vector Object	(OK)
//////////////////////////////////////////////////////////

class Vector
{
	private static Integer[] a;
	public /* readonly */ int size;
	/*:
	public static ghost specvar init :: bool;

	public static specvar content :: objset;
	vardefs
		"content == {n. EX j. n = a.[j] & 0 <= j & j < size}";

	invariant "init --> a ~= null & 0<a..Array.length & 0 <= 20 & 20<=a..Array.length";
	*/

	public void initialize()
	/*:
	requires "True"
	modifies init, content, size
	ensures "init & content = {} & size = 0";
	*/
	{
		a = new Integer[20];
		size = 0;
		//: init := "True";
	}

	public void add(Integer e)
	/*:
      	requires "init & e~=null"
      	modifies content, "Array.arrayState", size
      	ensures "((content = old content Un {e}) & (size = (old size) + 1)) | ((content = old content) & (size = (old size)))";
    	*/
	{
		if ((a == null) || (e == null)) {
			//: noteThat "content = old content";
			//: noteThat "size = old size";
			return;
		}
 		if ((size>=0) && (size < a.length)) {
			if (a[size] == null) a[size] = new Integer();
            		a[size] = e;
            		size = size + 1;
            		//: noteThat "content = old content Un {e}";
			//: noteThat "size = old size + 1";
        	} else {
            		//: noteThat "content = old content";
			//: noteThat "size = old size";
        	}
	}
	public void removeElement(Integer e)
	/*:
      	requires "init"
      	modifies content, size, "Array.arrayState"
      	ensures "((content = old content - {e}) & (size = (old size) - 1)) | ((content = old content) & (size = (old size)))";
    	*/
	{
		if ((size<=0) || (size > a.length)) {
			//: noteThat "content = old content";
			return;
		}
		int i=size-1;
		int save = -1;
		while //: inv "i>=-1 & i <size";
		(i>=0) 
		{
 			if (a[i] == e) save = i;
		}

		if (save==-1) {
			//: noteThat "content = old content";
			return;
		}
		else {
			if (size > 0) {
				a[save] = a[size-1];
				size = size - 1;
				//: noteThat "content = old content - {e}";
			}
		}
	}
	public boolean contains(Integer e)
	/*:
      	requires "init & e ~= null & size>=0"
      	ensures "result = (e : content) | result = False";
     	*/
	{
		//: ghost specvar content_i :: objset;
        	int i = 0;
		if (size > a.length) return false;
		
        	//: content_i := "{}";
        	while /*: inv "0 <= i & i <= size &
                       (content_i = {n. EX j. n = a.[j] & 0 <= j & j < i }) &
                       (e ~: content_i)" */
            	(i < size) {
            		if (a[i] == e) {
				return true;
            		} else {
                		//: content_i := "content_i Un {a.[i]}";
                		i = i + 1;
            		}
        	}
        	//: noteThat "i = size";
        	//: noteThat "content_i = content";
        	return false;   
	}
}

//////////////////////////////////////////////////////////
//Integer Class simulating the Integer Object	(OK)
//////////////////////////////////////////////////////////

class Integer
{
	public  /*: claimedby Dijkstra */ int a;
}

//////////////////////////////////////////////////////////
//Dijkstra Class				(OK)
//////////////////////////////////////////////////////////

public class Dijkstra
{
	private static Integer[] results;
	private static Integer[] previous;
	public /*: readonly */ static int num;

	/*: 
	public static ghost specvar init :: bool;
	public static ghost specvar initFields :: bool;

	public static specvar content1 :: objset;
      	vardefs
        	"content1 == {n. EX j. n = results.[j] & 0 <= j & j < num}";

	invariant initInv: "init --> (results ~= null & 0 < results..Array.length & 
	                    20 <= results..Array.length)";

	invariant initFieldsInv: "initFields --> (ALL j. 0 <= j & j < num --> results.[j] ~= null)";

	public static specvar content2 :: objset;
      	vardefs
        	"content2 == {n. EX j. n = previous.[j] & 0 <= j & j < num}";

	invariant prevInv: "init --> (previous ~= null & 0 < previous..Array.length & 
						20 <= previous..Array.length)";

	invariant prevFieldInv: "initFields --> (ALL j. 0 <= j & j < num --> previous.[j] ~= null)";
        */

	public static void initialize() 
    	/*:
      	modifies init, content1, content2, num
      	ensures "init & content1 = {} & content2 = {}";
    	*/
    	{
			results = new /*: hidden */ Integer[20];
			previous = new /*: hidden */ Integer[20];
			num = 0;
        	//: init := "True";
    	}

	public boolean DefaultValue(int nb)
	/*:
	      requires "init & nb >= 0 & nb <= 20 & num=0"
	      modifies initFields, content1, content2, "Array.arrayState", num, "Integer.a"
	      ensures "init=True & initFields=True";
	*/
	{
		while /*: inv "0 <= num & num <= nb & (ALL x. 0 <= x & x < num --> results.[x] ~= null & previous.[x] ~= null)";
		      */
		(num < nb) {
			results[num] = new Integer();
			results[num].a = -1; //Set each distance to infinity.
			//: content1 := "content1 Un {results.[num]}";
 			previous[num] = new Integer();
	 		previous[num].a = -1; //Set each previous node to undefined.
			//: content2 := "content2 Un {previous.[num]}";
			num = num+1;
		}
		//: noteThat "num=nb";
		//: initFields := "True";
		if (num==nb) return true;
		else return false;
	}

	public void CalculateBranching(Node n, int lim, int u)
	/*:
	      requires "init & initFields & lim >= 0 & lim <= n..Node.paths..Array.length & u>=0 & u < num & n~=null & (n..Node.paths~=null) & (ALL j. j>=0 & j<lim --> n..Node.paths.[j]~=null) & num < 20"
	      modifies content1, content2,  "Integer.a"
	      ensures "True";
	*/
	{
		int i = 0;
		while /*: inv "i>=0 & i<=lim & (n~=null)";
			  */
		(i < lim) {
			if (i >= n.paths.length) return;
			else {
				int v = n.paths[i].dest;
				if ((v < 0) || (v >= num)) return;
				else {
					if (((results[u].a + n.paths[i].value) < results[v].a) || (results[v].a == -1))
					{
						results[v].a = results[u].a + n.paths[i].value;
						previous[v].a = u;
					}
				}
			}
			i = i + 1;
		}
		//: noteThat "i=lim";
	}

	public void Algorithm(Node m_node[], int nb, int start)
	    /*:
	      requires "init & nb > 0 & nb <= 20 & num=0 & start>=0 & start<nb & (m_node~=null) & (m_node..Array.length < num) & (ALL x. 0 <= x & x < nb --> m_node.[x] ~= null & m_node.[x]..Node.nb_paths >= 0 & m_node.[x]..Node.nb_paths <= 20 & (ALL y. 0 <= y & y < m_node.[x]..Node.nb_paths --> m_node.[x]..Node.paths.[y] ~= null))"
	      modifies init, initFields, content1, content2, "Array.arrayState", num, "Vector.size", "Vector.content", "Vector.init", "Integer.a"
	      ensures "init=True";
	    */
	{

		Vector vec1 = new Vector();
		vec1.initialize();
		    
		Vector vec2 = new Vector();
		vec2.initialize();

		/////////////////////////////////////////////////////////
		//Reset All variables to initial Values for the algorithm (OK)
		//////////////////////////////////////////////////////////

		num = 0;
		DefaultValue(nb);
		//: assert "initFields=True";
		if (start >= num) return;
		else {
			results[start].a = 0; //Initial node, dist set to 0.

			//////////////////////////////////////////////////////////////////
			//Enter all nodes except the initial one to one Vector Object (OK)
			//////////////////////////////////////////////////////////////////

			Integer tmp = new Integer();

			int i = 0;
			while 	//: inv "0 <= i & i <= nb & (vec1~=null) & (tmp~=null) & theinvs";
			(i < nb) {
				tmp.a = i;
				if (i != start) vec1.add(tmp); //Add all elements except start to the vector	
				i = i + 1;
			}
			//: noteThat "i=nb";

			/////////////////////////////////////////////////////////////
			//Main Algorithm Loop		(OK)
			/////////////////////////////////////////////////////////////
		
			i = 0;
			while 	//: inv "(vec1~=null & vec2~=null) & theinvs";		   
 			(vec1.size > 0)
			{
 				int u = SmallestDist(vec1, nb);

				if ((u < 0) || (u >= m_node.length)) return;
				else {
 
			    	Integer val = new Integer();
			    	val.a = u;
			    	vec1.removeElement(val);
			    	vec2.add(val);
			    
			    	if ((m_node[u] == null) || (m_node[u].paths == null)) return;
					else {
						int lim = m_node[u].nb_paths;

						if ((lim < 0) || (lim > m_node[u].paths.length)) return;
						else CalculateBranching(m_node[u], lim, u);
					}
				}
			}
		}
	}

	//////////////////////////////////////////////////////////
	//SmallestDist Method	(OK)
	//////////////////////////////////////////////////////////

	public int SmallestDist(Vector vec, int nb)
	    /*:
	      requires "init & initFields & nb > 0 & nb <= 20 & vec ~= null & vec..Vector.size >= 0 & Vector.init=True"
	      modifies "Integer.a"
	      ensures "True";
	    */
	{
		int tmp = 10001;
		int index = -1;
		int i = 0;
		
		Integer val = new Integer();

		while /*: inv "0 <= i & i <= nb & (val~=null) & theinvs";
		      */
		(i < nb) {
		    if (results[i]==null) return index; //was: 'return;'
			else {
				val.a = i;
				if ((tmp > results[i].a) && (results[i].a != -1) && (vec.contains(val)))
				{
				    if (results[i]==null) return index; //was: 'return;'
					else {
						tmp = results[i].a;
						index = i;
					}
				}
			}
			i = i + 1;
		}
		return index;
	}
}
