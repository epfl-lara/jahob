public class ArrayList
{
    private Object[] elementData;
    private int size;
    
    /*: public specvar init :: bool;
        public specvar content :: "(int * obj) set";
	public specvar csize :: int;
	public specvar msize :: int;
	
	vardefs "init == elementData ~= null"
	vardefs "content == {(i, n). 0 <= i & i < size & n = elementData.[i]}"
	vardefs "csize == size"
	vardefs "msize == elementData..Array.length"

	invariant InitInv: 
	  "~init --> size = 0 & elementData = null"
	invariant SizeInv: 
	  "init --> 0 <= size & size <= elementData..Array.length"
	invariant ElementDataInv: 
	"init --> elementData : hidden"

	invariant NotHiddenInv:
	  "init --> 
	    (ALL i. ((0 <= i & i < size) --> elementData.[i] ~: hidden))"

	invariant RangeInvInj:
	  "init --> (ALL i v1 v2. (i,v1) : content & (i,v2) : content --> v1=v2)"

	invariant InjInv:
	  "ALL x y. x ~= y & x..elementData ~= null --> 
	  x..elementData ~= y..elementData";
    */

    public ArrayList(int initialCapacity)
    /*: requires "~init & 0 < initialCapacity"
        modifies "init", "msize"
        ensures "init & content = {} & csize = 0 & msize = initialCapacity"
    */
    {
	elementData = new /*: hidden */ Object[initialCapacity];
    }

    public void trimToSize()
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

    public void ensureCapacity(int minCapacity)
    /*: requires "init"
        modifies msize
        ensures "minCapacity <= msize & old msize <= msize"
    */
    {
	_ensureCapacity(minCapacity);
    }

    private  void _ensureCapacity(int minCapacity)
    /*: requires "init & theinvs"
        modifies "Array.arrayState", elementData, msize, "ArrayList.hidden"
        ensures "minCapacity \<le> msize \<and> old msize \<le> msize \<and>
	         (\<forall> x. x..init = (fieldRead (old ArrayList.init) x)) \<and>
	         (\<forall> a j. a \<noteq> elementData \<longrightarrow> a.[j] = arrayRead (old arrayState) a j) \<and>
		 (\<forall> j. ((0 \<le> j \<and> j < size) \<longrightarrow>
	          elementData.[j] = arrayRead (old arrayState) (old elementData) j)) \<and>
	         (\<forall> o1. (o1 \<in> old alloc) \<longrightarrow> ((o1 \<in> old hidden) = (o1 \<in> hidden))) \<and> theinvs" */
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

    public int size()
    /*: requires "init"
        ensures "result = csize"
    */
    {
	return size;
    }

    public boolean isEmpty()
    /*: requires "init"
        ensures "result = (csize = 0)"
    */
    {
	return size == 0;
    }
    
    public boolean contains(Object elem)
    /*: requires "init"
        ensures "(result = (EX i. (i, elem) : content))";
    */
    {
	int index = indexOfInt(elem);
	//: noteThat PosIndex: "0 <= index --> ((index,elem) : content)";
	//: noteThat NegIndex: "index = -1 --> ~(EX i. (i,elem) : content)";
	//: noteThat IndexLemma: "0 <= index | index = -1";
	boolean res = (0 <= index);
	/*: note ResultLemma: "res = (EX i. (i, elem) : content)" from PosIndex, NegIndex, IndexLemma;
	*/
	return res;
    }

    public int indexOf(Object elem)
    /*: requires "init"
        ensures "-1 <= result & result < csize &
	         (result ~= -1 --> (result, elem) : content) &
		 (result ~= -1 --> ~(EX i. i < result & (i, elem) : content)) &
                 (result = -1 --> ~(EX i. (i, elem) : content))"
    */
    {
	return indexOfInt(elem);
    }

    private int indexOfInt(Object elem)
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

    public int lastIndexOf(Object elem)
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
		       (ALL j. i < j & j < size --> elem ~= elementData.[j])" */ 
	    
	    (i >= 0)
	{
	    if (elementData[i] == elem)
		return i;
	    i = i - 1;
	}
	return -1;
    }

    public Object[] toArray()
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
		comment ''IC'' (ALL j. ((0 <= j & j < size) --> elementData.[j] ~: hidden))" */
	    (i < size)
	{
	    res[i] = elementData[i];
	    i = i + 1;
	}
	return res;
    }

    public Object get(int index)
    /*: requires "init & 0 <= index & index < csize"
        ensures "(index, result) : content"
     */
    {
	return elementData[index];
    }

    public Object set(int index, Object element)
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

    private  boolean add1(Object o1)
    /*: requires "init & theinvs"
        modifies "Array.arrayState", elementData, msize, "ArrayList.hidden", content, size, csize
	ensures "(old csize, o1) : content &
	         comment ''addContentChange'' (ALL j. ((0 <= j & j < old csize) -->
		  ((ALL e. (j, e) : content --> (j, e) : old content) &
		   (ALL e. (j, e) : old content --> (j, e) : content)))) &
	         comment ''csizeChange'' (csize = old csize + 1) & result &
                 old msize <= msize & csize <= msize &
	         (ALL a j. a ~: hidden -->
		   a.[j] = arrayRead (old Array.arrayState) a j) &
		 (ALL o1. (o1 : old alloc) -->
		   ((o1 : old hidden) = (o1 : hidden))) & 
		   (ALL x. x..init = (fieldRead (old ArrayList.init) x)) &
		   theinvs"
    */
    {
	_ensureCapacity(size + 1);
	elementData[size] = o1;
	size = size + 1;
	//: noteThat "old csize < size";
	return true;
    }

    public boolean add(Object o1)
    /*: requires "init"
        modifies content, csize, msize
	ensures "(old csize, o1) : content &
	         (ALL j. ((0 <= j & j < old csize) -->
		  ((ALL e. (j, e) : content --> (j, e) : old content) &
		   (ALL e. (j, e) : old content --> (j, e) : content)))) &
	         csize = old csize + 1 & result &
                 old msize <= msize & csize <= msize"
    */
    {
	return add1(o1);
    }

    public void add_at(int index, Object element)
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
		      (ALL a j. ((a ~: hidden) -->
		       a.[j] =
		       arrayRead (old Array.arrayState) a j)) &
		      ((i = size - 1) -->
		       (ALL j. ((0 <= j & j < size) -->
		        elementData.[j] ~: hidden))) &
		      ((i < size - 1) -->
		       (ALL j. ((0 <= j & j < size + 1) -->
		        elementData.[j] ~: hidden))) &
		      ((ALL j. ((0 <= j & j <= i) -->
		      elementData.[j] =
		      arrayRead (old Array.arrayState) (old elementData) j))) &
		      ((ALL j. ((0 <= j & j <= index & j < size) -->
		      elementData.[j] =
		      arrayRead (old Array.arrayState) (old elementData) j))) &
		      ((ALL j. ((i < j & j < size) -->
		      elementData.[j + 1] =
		      arrayRead (old Array.arrayState) (old elementData) j))) &
		      (ALL x i. (x ~= elementData & x ~= (old elementData)) -->
		      (x.[i] = (arrayRead (old Array.arrayState) (old x) i)))"
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

    public Object remove_at(int index)
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
	shift(index);
	return oldValue;
    }

    public Object remove_at_dep(int index)
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

    public boolean remove(Object o1)
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
	while /*: inv "0 \<le> index \<and> theinvs \<and>
                       (\<forall> j. 0 \<le> j \<and> j < index \<longrightarrow> o1 \<noteq> elementData.[j]) \<and>
                       (\<forall> a i. a.[i] = old (a.[i])) \<and>
		       comment ''ContentLoop''
		       (\<forall> x. x..content = old (x..content)) \<and>
		       (\<forall> x. x..size = old (x..size))" */
	    (index < size)
	{
	    if (elementData[index] == o1) {
		shift(index);
		/*: noteThat ThisContent: 
		    "\<forall> j e. ((0 \<le> j \<and> j < index) \<longrightarrow>
		    (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
		    ((index \<le> j \<and> j < csize) \<longrightarrow>
		    (((j, e) \<in> content) = ((j + 1, e) \<in> old content)))"
		    from shift_Postcondition, ContentLoop; */
		/*: witness "index" for PostconditionClause1:
		    "(\<exists> i. (((i, o1) \<in> old content) \<and>
		          \<not>(\<exists> j. j < i \<and> (j, o1) \<in> old content) \<and>
			  (\<forall> j e. ((0 \<le> j \<and> j < i) \<longrightarrow>
			   (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
			   ((i \<le> j \<and> j < csize) \<longrightarrow>
			   (((j, e) \<in> content) = ((j + 1, e) \<in> old content))))))"; */
		/*: note PostconditionClause2: 
		    "(\<not>(\<exists> i. (i, o1) \<in> old content) \<longrightarrow> 
		    (\<not>True \<and> (content = old content)))"
		    from PostconditionClause1; */
		return true;
	    }
	    index = index + 1;
	}
	return false;
    }

    public boolean remove2(Object o1)
    /*: requires "init"
        modifies content, csize
	ensures "(result --> (\<exists> i. ((i, o1) \<in> old content) \<and>
		         \<not>(\<exists> j. j < i \<and> (j, o1) \<in> old content) \<and>
			  (\<forall> j e. ((0 \<le> j \<and> j < i) \<longrightarrow>
			             (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
				    ((i \<le> j \<and> j < csize) \<longrightarrow>
			             (((j, e) \<in> content) = ((j + 1, e) \<in> old content)))))) \<and>
                 (~result --> (\<not>(\<exists> i. (i, o1) \<in> old content) \<and> (content = old content)))"
    */
    {
	int index = 0;
	while /*: inv "0 \<le> index \<and> theinvs \<and>
                       (\<forall> j. 0 \<le> j \<and> j < index \<longrightarrow> o1 \<noteq> elementData.[j]) \<and>
                       (\<forall> a i. a.[i] = old (a.[i])) \<and>
		       (\<forall> x. x..content = old (x..content)) \<and>
		       (\<forall> x. x..size = old (x..size))" */
	    (index < size)
	{
	    if (elementData[index] == o1) {
		shift(index);
		/*: noteThat ThisContent: 
		    "\<forall> j e. ((0 \<le> j \<and> j < index) \<longrightarrow>
		    (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
		    ((index \<le> j \<and> j < csize) \<longrightarrow>
		    (((j, e) \<in> content) = ((j + 1, e) \<in> old content)))" from shift_Postcondition, LoopInv; */
		/*: witness "index" for PostconditionClause1:
		    "(\<exists> i. (((i, o1) \<in> old content) \<and>
	                  \<not>(\<exists> j. j < i \<and> (j, o1) \<in> old content) \<and>
			  (\<forall> j e. ((0 \<le> j \<and> j < i) \<longrightarrow>
			   (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
			   ((i \<le> j \<and> j < csize) \<longrightarrow>
			   (((j, e) \<in> content) = ((j + 1, e) \<in> old content))))))"; */
		return true;
	    }
	    index = index + 1;
	}
	return false;
    }

    private void shift(int index)
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
		 (\<forall> x. x \<noteq> this \<longrightarrow> x..content = old (x..content)) \<and>
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

    public void clear()
    /*: requires "init"
        modifies content, csize
	ensures "content = {} & csize = 0"
     */
    {
	int i = 0;
	
	while /*: inv "0 <= i &
		   (ALL x i. x \<noteq> elementData \<longrightarrow>
		    x.[i] = arrayRead (old Array.arrayState) (old x) i) &
		   (ALL x. x : Object.alloc & x : ArrayList & x..init & x ~= this -->
		   (ALL i. ((0 <= i & i < x..size) --> x..elementData.[i] ~: hidden)))" */
	    (i < size)
        {
	    elementData[i] = null;
	    i = i + 1;
	}
	size = 0;
    }

    // Two stack operations

    public void pushLast(Object element)
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
	//: note ContentFrame: "ALL al. al : old alloc & al : ArrayList & al ~: hidden & al ~= this --> al..content = old (al..content)" from add1_Postcondition;
    }

    public Object popLast()
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
