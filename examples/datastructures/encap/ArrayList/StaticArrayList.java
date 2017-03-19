public class ArrayList
{
    private static Object[] elementData;
    private static int size;
    
    /*: public static specvar init :: bool;
        public static specvar content :: "(int * obj) set";
	public static specvar csize :: int;
	public static specvar msize :: int;
	
	vardefs "init == elementData ~= null"
	vardefs "content == {(i, n). 0 <= i & i < size & n = elementData.[i]}"
	vardefs "csize == size"
	vardefs "msize == elementData..Array.length"

	invariant InitInv: 
	  "~init --> size = 0 & elementData = null"
	invariant SizeInv: 
	  "init --> 0 <= size & size <= elementData..Array.length"
	invariant ElementDataInv: 
	"init --> elementData : alloc & elementData : hidden"
	invariant HiddenInv: "hidden \<subseteq> alloc";

	invariant NotHiddenInv:
	  "init --> 
	    (ALL i. ((0 <= i & i < size) --> elementData.[i] ~: hidden))"

	invariant AllocInv:
	  "init -->
	    (ALL i. ((0 <= i & i < size) --> elementData.[i] : alloc))"

	invariant RangeInv1:
	  "init --> (ALL i. 0 <= i & i < size --> (EX v. (i,v) : content))";
	invariant RangeInv2:
	  "init --> (ALL i v. (i,v) : content --> 0 <= i & i < size)";
	invariant RangeInvInj:
	  "init --> (ALL i v1 v2. (i,v1) : content & (i,v2) : content --> v1=v2)"
    */

    public static void init(int initialCapacity)
    /*: requires "~init & 0 < initialCapacity"
        modifies "init", "msize"
        ensures "init & content = {} & csize = 0 & msize = initialCapacity"
    */
    {
	elementData = new /*: hidden */ Object[initialCapacity];
    }

    public static void trimToSize()
    /*: requires "init"
        modifies msize
	ensures "msize = csize"
    */
    {
	int oldCapacity = elementData.length;
	if (size < oldCapacity) {
	    Object oldData[] = elementData;
	    elementData = new /*: hidden */ Object[size];
	    int i = 0;
	    while /*: inv "0 <= i &
		    (ALL j. (oldData.[j] =
		    arrayRead (old Array.arrayState) (old elementData) j)) &
		    (ALL j. (((0 <= j & j < i) -->
		     elementData.[j] = oldData.[j]))) &
		    (ALL a i. a ~= elementData -->
		     arrayRead (old Array.arrayState) a i = a.[i])"
		  */
		(i < size)
	    {
		elementData[i] = oldData[i];
		i = i + 1;
	    }
	}
    }

    public static void ensureCapacity(int minCapacity)
    /*: requires "init"
        modifies msize
        ensures "minCapacity <= msize & old msize <= msize"
    */
    {
	_ensureCapacity(minCapacity);
    }

    private static void _ensureCapacity(int minCapacity)
    /*: requires "init & theinvs"
        modifies "Array.arrayState", elementData, msize, "ArrayList.hidden"
        ensures "minCapacity \<le> msize \<and> old msize \<le> msize \<and>
	         init = old init &
	         (\<forall> a j. a \<noteq> elementData \<longrightarrow> a.[j] = arrayRead (old arrayState) a j) \<and>
		 (\<forall> j. ((0 \<le> j \<and> j < size) \<longrightarrow>
	          elementData.[j] = arrayRead (old arrayState) (old elementData) j)) \<and>
		 (ALL o1. o1 : hidden & o1 : old alloc --> o1 : old hidden) &
		 (ALL o1. o1 : old hidden & o1 : old alloc --> o1 : hidden) &
		 theinvs"
    */
    {
	int oldCapacity = elementData.length;
	if (minCapacity > oldCapacity) {
	    Object oldData[] = elementData;
	    int newCapacity = (oldCapacity * 3)/2 + 1;
	    if (newCapacity < minCapacity)
		newCapacity = minCapacity;
	    elementData = new /*: hidden */ Object[newCapacity];
	    int i = 0;
	    while /*: inv "0 \<le> i \<and>
		    (\<forall> j. ((0 \<le> j \<and> j < size \<longrightarrow>
		      oldData.[j] = arrayRead (old arrayState) (old elementData) j))) \<and>
		    (\<forall> j. ((0 \<le> j \<and> j < i) \<longrightarrow> elementData.[j] = oldData.[j])) \<and> 
                    (\<forall> a j. a \<noteq> elementData \<longrightarrow> a.[j] = arrayRead (old arrayState) a j)" */
		(i < size)
	    {
		elementData[i] = oldData[i];
		i = i + 1;
	    }
	}
    }

    public static int size()
    /*: requires "init"
        ensures "result = csize"
    */
    {
	return size;
    }

    public static boolean isEmpty()
    /*: requires "init"
        ensures "result = (csize = 0)"
    */
    {
	return size == 0;
    }
    
    public static boolean contains(Object elem)
    /*: requires "init"
        ensures "(result = (EX i. (i, elem) : content))";
    */
    {
	int index = indexOfInt(elem);
	//: noteThat PosIndex: "0 <= index --> ((index,elem) : content)";
	//: noteThat NegIndex: "index = -1 --> ~(EX i. (i,elem) : content)";
	//: noteThat IndexLemma: "0 <= index | index = -1";
	boolean res = (0 <= index);
	/*: noteThat ResultLemma: "res = (EX i. (i, elem) : content)" 
	  from PosIndex, NegIndex, IndexLemma, ResultLemma;
	*/
	return res;
    }

    public static int indexOf(Object elem)
    /*: requires "init"
        ensures "-1 <= result & result < csize &
	         (result ~= -1 --> (result, elem) : content) &
		 (result ~= -1 --> ~(EX i. i < result & (i, elem) : content)) &
                 (result = -1 --> ~(EX i. (i, elem) : content))"
    */
    {
	return indexOfInt(elem);
    }

    private static int indexOfInt(Object elem)
    /*: requires "init & theinvs"
        ensures "-1 <= result & result < csize &
	         (result ~= -1 --> (result, elem) : content) &
		 (result ~= -1 --> ~(EX i. i < result & (i, elem) : content)) &
                 (result = -1 --> ~(EX i. (i, elem) : content)) & theinvs"
    */
    {
	int i = 0;
	
	while /*: inv "0 <= i &
		       (ALL j. 0 <= j & j < i --> elem ~= elementData.[j])" */
	    (i < size)
	{
	    if (elementData[i] == elem)
		return i;
	    i = i + 1;
	}
	return -1;
    }

    public static int lastIndexOf(Object elem)
    /*: requires "init"
        ensures "-1 <= result & result < csize &
	         (result ~= -1 --> 
		  ((result, elem) : content) &
		  ~(EX i. result < i & (i, elem) : content)) &
                 (result = -1 --> ~(EX i. (i, elem) : content))"
    */
    {
	int i = size - 1;
	while /*: inv "i < size &
		       (ALL j. i < j & j < size --> elem ~= elementData.[j])"
	      */
	    (i >= 0)
	{
	    if (elementData[i] == elem)
		return i;
	    i = i - 1;
	}
	return -1;
    }

    public static Object[] toArray()
    /*: requires "init"
        modifies "new..arrayState"
        ensures "(ALL i e. (i, e) : content --> result.[i] = e) &
	         (ALL i. 0 <= i & i < result..Array.length --> 
		  (i, result.[i]) : content)"
    */
    {
	int i = 0;
	Object[] res = new Object[size];
	
	while /*: inv "theinvs &
		comment ''C1'' (0 <= i) & comment ''C2'' (content = old content) &
		comment ''IA'' (ALL j. (0 <= j & j < i --> res.[j] = elementData.[j])) &
		comment ''IB'' (ALL x i. (x ~= res -->
		  x.[i] = arrayRead (old Array.arrayState) x i)) &
		comment ''IC'' (ALL j. ((0 <= j & j < size) --> elementData.[j] ~: hidden)) &
		comment ''ID'' (ALL j. 
		  ((0 <= j & j < size) --> elementData.[j] : alloc))"
	      */
	    (i < size)
	{
	    res[i] = elementData[i];
	    i = i + 1;
	}
	return res;
    }

    public static Object get(int index)
    /*: requires "init & 0 <= index & index < csize"
        ensures "(index, result) : content"
     */
    {
	return elementData[index];
    }

    public static Object set(int index, Object element)
    /*: requires "init & 0 <= index & index < csize"
        modifies content
	ensures "(index, result) : old content & 
	  content = (old content - {(index, result)}) Un {(index, element)}"
    */
    {
	Object oldValue = elementData[index];
	elementData[index] = element;
	return oldValue;
    }

    private static boolean add1(Object o)
    /*: requires "init & theinvs"
        modifies "Array.arrayState", elementData, msize, "ArrayList.hidden", content, size, csize
	ensures "(old csize, o) : content &
	         comment ''addContentChange'' (ALL j. ((0 <= j & j < old csize) -->
		  ((ALL e. (j, e) : content --> (j, e) : old content) &
		   (ALL e. (j, e) : old content --> (j, e) : content)))) &
	         comment ''csizeChange'' (csize = old csize + 1) & result &
                 old msize <= msize & csize <= msize &
	         (ALL a j. a ~: hidden -->
		   a.[j] = arrayRead (old Array.arrayState) a j) &
		 (ALL o1. o1 : old hidden & o1 : old alloc --> o1 : hidden) &
		 (ALL o1. o1 : hidden & o1 : old alloc --> o1 : old hidden) &
		 theinvs"
    */
    {
	_ensureCapacity(size + 1);
	elementData[size] = o;
	size = size + 1;
	//: noteThat "old csize < size";
	//: noteThat "theinvs";
	return true;
    }

    public static boolean add(Object o)
    /*: requires "init"
        modifies content, csize, msize
	ensures "(old csize, o) : content &
	         (ALL j. ((0 <= j & j < old csize) -->
		  ((ALL e. (j, e) : content --> (j, e) : old content) &
		   (ALL e. (j, e) : old content --> (j, e) : content)))) &
	         csize = old csize + 1 & result &
                 old msize <= msize & csize <= msize"
    */
    {
	return add1(o);
    }

    public static void add_at(int index, Object element)
    /*: requires "comment ''addAtPre'' (init & 0 <= index & index <= csize)"
        modifies content, csize, msize
	ensures "((index, element) : content) &
	         (ALL j e.
                  (0 <= j & j < index --> ((j, e) : content) = ((j, e) : old content)) &
		  (index < j & j < csize --> ((j, e) : content) = ((j - 1, e) : old content))) &
	         (csize = (old csize) + 1) &
		 (msize >= (old msize)) &
		 (csize <= msize)"
    */
    {
	_ensureCapacity(size + 1);
	int i = size - 1;
	while /*: inv "index - 1 <= i & i <= size - 1 &
		      (ALL a j. (a ~= elementData & a ~= old elementData -->
		       a.[j] =
		       arrayRead (old Array.arrayState) a j)) &
		      ((i = size - 1) -->
		       (ALL j. ((0 <= j & j < size) -->
		        elementData.[j] ~: hidden))) &
		      ((i < size - 1) -->
		       (ALL j. ((0 <= j & j < size + 1) -->
		        elementData.[j] ~: hidden))) &
		      ((i = size - 1) -->
		       (ALL j. ((0 <= j & j < size) --> 
		        elementData.[j] : alloc))) &
		      ((i < size - 1) -->
		       (ALL j. ((0 <= j & j < size + 1) -->
		        elementData.[j] : alloc))) &
		      ((ALL j. ((0 <= j & j <= i) -->
		      elementData.[j] =
		      arrayRead (old Array.arrayState) (old elementData) j))) &
		      ((ALL j. ((0 <= j & j <= index & j < size) -->
		      elementData.[j] =
		      arrayRead (old Array.arrayState) (old elementData) j))) &
		      ((ALL j. ((i < j & j < size) -->
		      elementData.[j + 1] =
		      arrayRead (old Array.arrayState) (old elementData) j)))"
	      */
	    (index <= i)
	    {
		elementData[i + 1] = elementData[i];
		i = i - 1;
	    }
	elementData[index] = element;
	size = size + 1;
	/*: noteThat InvMeans: 
	  "(ALL j. ((0 <= j & j < index & j < (old size)) -->
	            elementData.[j] =
		    arrayRead (old Array.arrayState) (old elementData) j)) &
	   (ALL j. ((index <= j & j < (old size)) -->
	            elementData.[j + 1] =
		    arrayRead (old Array.arrayState) (old elementData) j))";
	*/
	//: noteThat IndexRange: "0 <= index & index <= old size";
	//: noteThat CsizeIsSize: "csize = size";
	/*: noteThat PostCond: 
	  "(ALL j e.
	    (0 <= j & j < index --> ((j, e) : content) = ((j, e) : old content)) &
	    (index < j & j < csize --> ((j, e) : content) = ((j - 1, e) : old content)))"
	  from InvMeans, PostCond, content_def, IndexRange, CsizeIsSize;
	*/
	/*: noteThat OtherPostCond: "(index, element) : content"
	  from OtherPostCond, content_def, IndexRange;
	 */
    }

    public static Object remove_at(int index)
    /*: requires "init & 0 <= index & index < csize"
        modifies content, csize
	ensures "(ALL j e.
                  (0 <= j & j < index --> ((j, e) : content) = ((j, e) : old content)) &
		  (index <= j & j < csize --> ((j, e) : content) = ((j + 1, e) : old content))) &
		 ((index, result) : old content) &
                 (csize = old csize - 1)";
    */
    {
	Object oldValue = elementData[index];
	fastRemove(index);
	return oldValue;
    }

    public static Object remove_at_dep(int index)
    /*: requires "init & 0 <= index & index < csize"
        modifies content, csize
	ensures "((index, result) : old content) &
	         (csize = old csize - 1) &
                 (ALL j e. 
		  ((0 <= j & j < index) --> ((j, e) : content) = ((j, e) : old content)) &
		  ((index <= j & j < csize) --> ((j, e) : content) = ((j + 1, e) : old content)))" */
    {
	Object oldValue = elementData[index];
	int i = index;
	while /*: inv "index <= i & 
		(ALL j. ((0 <= j & j < index) --> 
		 elementData.[j] = 
		  (arrayRead (old Array.arrayState) (old elementData) j))) &
		(ALL j. ((index <= j & j < i) -->
		 elementData.[j] = 
		  (arrayRead (old Array.arrayState) elementData (j + 1)))) &
		(ALL j. ((i <= j & j < size) -->
		 elementData.[j] = 
		  (arrayRead (old Array.arrayState) (old elementData) j))) &
                (ALL x i. x ~= elementData -->
		 x.[i] = arrayRead (old Array.arrayState) (old x) i)"
	      */
	    (i < size - 1)
	{
	    elementData[i] = elementData[i+1];
	    i = i + 1;
	}
	size = size - 1;
	elementData[size] = null;

	return oldValue;
    }

    public static boolean remove(Object o1)
    /*: requires "init"
        modifies content, csize
	ensures "((\<exists> i. (i, o1) \<in> old content) \<longrightarrow> (result \<and>
	          (\<exists> i. ((i, o1) \<in> old content) \<and>
		         \<not>(\<exists> j. j < i \<and> (j, o1) \<in> old content) \<and>
			  (\<forall> j e. ((0 \<le> j \<and> j < i) \<longrightarrow>
			             (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
				    ((i \<le> j \<and> j < csize) \<longrightarrow>
			             (((j, e) \<in> content) = ((j + 1, e) \<in> old content))))))) \<and>
	         (\<not>(\<exists> i. (i, o1) \<in> old content) \<longrightarrow> (\<not>result \<and> (content = old content)))"
    */
    {
	int index = 0;
	while /*: inv "0 \<le> index \<and> theinvs \<and> alloc = old alloc \<and>
                       (\<forall> j. 0 \<le> j \<and> j < index \<longrightarrow> o1 \<noteq> elementData.[j]) \<and>
                       (\<forall> a i. a.[i] = old (a.[i])) \<and>
		       content = old content & size = old size" */
	    (index < size)
	{
	    if (elementData[index] == o1) {
		fastRemove(index);
		/*: noteThat indexInOld: "(index, o1) \<in> old content"; */
		/*: noteThat noOtherIndex: 
		  "\<not>(\<exists> j. j < index \<and> (j, o1) \<in> old content)"; */
		/*: noteThat ThisContent: 
		  "\<forall> j e. ((0 \<le> j \<and> j < index) \<longrightarrow>
		  (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
		  ((index \<le> j \<and> j < csize) \<longrightarrow>
		  (((j, e) \<in> content) = ((j + 1, e) \<in> old content)))"
		  from ThisContent, fastRemove_Postcondition, ContentLoop; */
		/*: noteThat indexExists:
		  "((index, o1) \<in> old content) \<and>
		   \<not>(\<exists> j. j < index \<and> (j, o1) \<in> old content) \<and>
		   (\<forall> j e. ((0 \<le> j \<and> j < index) \<longrightarrow>
		    (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
		    ((index \<le> j \<and> j < csize) \<longrightarrow>
		    (((j, e) \<in> content) = ((j + 1, e) \<in> old content))))"
		    from indexExists, indexInOld, noOtherIndex, ThisContent; */
		/*: noteThat postCond1:
		  "(\<exists> i. (((i, o1) \<in> old content) \<and>
	                  \<not>(\<exists> j. j < i \<and> (j, o1) \<in> old content) \<and>
			  (\<forall> j e. ((0 \<le> j \<and> j < i) \<longrightarrow>
			   (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
			   ((i \<le> j \<and> j < csize) \<longrightarrow>
			   (((j, e) \<in> content) = ((j + 1, e) \<in> old content))))))"
		  from indexExists, postCond1; */
		/*: note postCond2: 
		    "(\<not>(\<exists> i. (i, o1) \<in> old content) \<longrightarrow> (\<not>True \<and> (content = old content)))"
		  from postCond1, postCond2; */
		return true;
	    }
	    index = index + 1;
	}
	return false;
    }

    private static void fastRemove(int index)
    /*: requires "init & 0 <= index & index < size & theinvs"
        modifies "Array.arrayState", size, content, csize
	ensures "(ALL j. ((0 <= j & j < index) -->
	          elementData.[j] =
		  arrayRead (old Array.arrayState) (old elementData) j)) &
		 (ALL j. ((index <= j & j < size) -->
		  elementData.[j] =
		  arrayRead (old Array.arrayState) (old elementData) (j + 1))) &
		 elementData.[size] = null &
		 (ALL a i. a ~= elementData -->
		  a.[i] = arrayRead (old Array.arrayState) (old a) i) &
		 (size = old size - 1) & 
		 (\<forall> j e. ((0 \<le> j \<and> j < index) \<longrightarrow>
		 (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
		 ((index \<le> j \<and> j < csize) \<longrightarrow>
		 (((j, e) \<in> content) = ((j + 1, e) \<in> old content)))) \<and>
		 theinvs"
    */
    {
	int i = index;
	while /*: inv "index <= i \<and>
		(ALL j. ((0 <= j & j < index) --> 
		 elementData.[j] = 
		 (arrayRead (old Array.arrayState) (old elementData) j))) &
		(ALL j. ((index <= j & j < i) -->
		 elementData.[j] = 
		 (arrayRead (old Array.arrayState) (old elementData) (j + 1)))) &
		(ALL j. ((i <= j & j < size) -->
		 elementData.[j] = 
		 (arrayRead (old Array.arrayState) (old elementData) j))) &
		(ALL a i. ((a ~= elementData) -->
		 a.[i] = arrayRead (old Array.arrayState) (old a) i)) \<and>
		(\<forall> j e. ((0 \<le> j \<and> j < index) \<longrightarrow>
		(((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
		 ((index \<le> j \<and> j < i) \<longrightarrow>
		 (((j, e) \<in> content) = ((j + 1, e) \<in> old content))))"
	      */
	    (i < size - 1)
	{
	    elementData[i] = elementData[i+1];
	    i = i + 1;
	}
	size = size - 1;
	elementData[size] = null;
    }

    public static void clear()
    /*: requires "init"
        modifies content, csize
	ensures "content = {} & csize = 0"
     */
    {
	int i = 0;
	
	while /*: inv "0 <= i &
		   (ALL x i. x \<noteq> elementData \<longrightarrow>
		    x.[i] = arrayRead (old Array.arrayState) (old x) i)"
	      */
	    (i < size)
        {
	    elementData[i] = null;
	    i = i + 1;
	}
	size = 0;
    }

    // Two stack operations

    public static void pushLast(Object element)
    /*: requires "init"
        modifies content, csize, msize
	ensures "comment ''sizeInc'' (csize = old csize + 1) &
                 comment ''contentAdd'' (content = old content Un {(csize - 1,element)})"
     */
    {
	boolean res = add1(element);
	//: noteThat inserted: "(csize - 1, element) : content";
	{ //: pickAny i::int, e::obj
	    {//: assuming h1: "(i,e) : old content";
	     //: noteThat g1: "0 <= i & i < old csize";		
             //: noteThat g2: "(i,e) : content" from g2,g1, addContentChange, h1;
	    }
	    //: noteThat thus1: "(i,e) : old content --> (i,e) : content";
	    {//: assuming hh1: "(i,e) : content";
             //: noteThat gg1: "0 <= i & i < csize";
             //: noteThat gg2: "i = csize - 1 --> (i,e) : old content Un {(csize - 1,element)}";
		{//: assuming hh2: "i < csize - 1";
                 //: noteThat gg3: "(i,e) : old content" from addContentChange, hh2, gg1, hh1, csize_def, csizeChange;
		}
             //: noteThat possible: "i < csize - 1 | i = csize - 1";
             //: noteThat gg4: "(i,e) : old content Un {(csize - 1,element)}" from gg1, gg3, gg2, g2, h1, csize_def, csizeChange, possible;
	    }
	    /*: noteThat pointwise: 
                  "((i,e) : old content --> (i,e) : content) &
                   ((i,e) = (csize - 1, element) --> (i,e) : content) &
                   ((i,e) : content --> (i,e) : (old content Un {(csize - 1,element)}))" forSuch i,e;
	     */
	}
	//: noteThat tpost: "(content = old content Un {(csize - 1,element)})" from pointwise;
    }

    public static Object popLast()
    /*: requires "init & csize > 0"
        modifies content, csize
	ensures "csize = old csize - 1 &
                 content = old content - {(csize,result)}"
     */
    {
	size = size - 1;
	Object res = elementData[size];
	elementData[size] = null;
	return res;
    }
}
