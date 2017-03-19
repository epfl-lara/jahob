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

    public boolean remove_example(Object o1)
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
		shift_example(index);
		//: note IndexBounds: "0 \<le> index \<and> index < old size";
		//: note SizeChange: "size = old size - 1";
		/*: note ElementsShifted: "(ALL j. ((0 <= j & j < index) -->
	            elementData.[j] = arrayRead (old Array.arrayState) (old elementData) j)) &
		    (ALL j. ((index <= j & j < size) -->
		    elementData.[j] = arrayRead (old Array.arrayState) (old elementData) (j + 1)))" */
		/*: note ObjectRemoved: "\<forall> j e. ((0 \<le> j \<and> j < index) \<longrightarrow>
		    (((j, e) \<in> content) = ((j, e) \<in> old content))) \<and>
		    ((index \<le> j \<and> j < csize) \<longrightarrow>
		    (((j, e) \<in> content) = ((j + 1, e) \<in> old content)))" 
		    from IndexBounds, SizeChange, ElementsShifted, csize_def, content_def; */
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

    private void shift_example(int index)
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
		 a.[i] = arrayRead (old Array.arrayState) (old a) i))"
	      */
	    (i < size - 1)
	{
	    elementData[i] = elementData[i+1];
	    i = i + 1;
	}
	size = size - 1;
	elementData[size] = null;
    }
}
