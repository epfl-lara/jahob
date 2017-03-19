public class PriorityQueue
{
    private Comparable[] queue;
    private int csize;

    /*:
      public specvar init :: bool;
      public ghost specvar spqueue :: "(obj * int) set";

      vardefs "init == (queue \<noteq> null)";

      invariant QueueInv: 
        "init \<longrightarrow>
	   (\<forall> p n. ((p, n) \<in> spqueue) = (n = card (indexSet this p) \<and> 0 < n))";

      static specvar indexSet :: "obj \<Rightarrow> obj \<Rightarrow> (int set)";
      vardefs "indexSet == 
      (\<lambda> pq. (\<lambda> p. {i. 0 \<le> i \<and> i < pq..csize \<and> p = pq..queue.[i]}))";

      invariant SizeInv: "init \<longrightarrow> csize = card spqueue";
      invariant SizeLowerInv: "init \<longrightarrow> 0 \<le> csize";
      invariant SizeUpperInv: "init \<longrightarrow> csize \<le> queue..Array.length";
      invariant NonNullInv: "init \<longrightarrow> (\<forall> i. 0 \<le> i \<and> i < csize \<longrightarrow> queue.[i] \<noteq> null)";
      invariant IsNullInv:
       "init \<longrightarrow> (\<forall> i. csize \<le> i \<and> i < queue..Array.length \<longrightarrow> queue.[i] = null)";
      invariant OrderedInv: "init \<longrightarrow> (\<forall> i j.
       (0 \<le> i \<and> i < csize \<and> 0 \<le> j \<and> j < csize \<and> (j=i+i+1 \<or> j=i+i+2)
         \<longrightarrow> 0 \<le> (compFunc (queue.[i]) (queue.[j]))))";
      invariant HiddenInv: "init \<longrightarrow> queue : hidden";
      invariant InjInv: "\<forall> pq. pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..queue = queue \<and> queue \<noteq> null \<longrightarrow> pq = this";
    */

    public void PriorityQueue(int initialCapacity)
    /*: requires "\<not>init \<and> 0 < initialCapacity"
        modifies init, spqueue
	ensures "init \<and> spqueue = \<emptyset>" */
    {
	this.queue = new /*: hidden */ Comparable[initialCapacity];
	this.csize = 0;

	//: "spqueue" := "\<emptyset>";

	//: note NewNotPQ: "queue \<notin> PriorityQueue";

	{ //: pickAny pq::obj;
	    { //: assuming hyp1: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init";
		{ //: pickAny p1::obj, n1::int;
		    { //: assuming case1: "pq = this"
		      //: note lhsEmpty: "pq..spqueue = \<emptyset>";
		      //: note rhsEmpty: "(indexSet pq p1) = \<emptyset>";  
		      /*: note conc1: "((p1, n1) \<in> pq..spqueue) =
			(n1 = card (indexSet pq p1) \<and> 0 < n1)"
			from conc1, lhsEmpty, rhsEmpty; */
		    }
		    { //: assuming case2: "pq \<noteq> this"
			{ //: assuming case3: "pq = queue";
			  /*: note conc2: "((p1, n1) \<in> pq..spqueue) =
			    (n1 = card (indexSet pq p1) \<and> 0 <  n1)"
			    from conc2, NewNotPQ, hyp1, case3; */
			}
			{ //: assuming case4: "pq \<noteq> queue";
			  /*: note conc3: "((p1, n1) \<in> pq..spqueue) =
			    (n1 = card (indexSet pq p1) \<and> 0 < n1)"
			    from conc3, case2, case4, hyp1, QueueInv, init_def, indexSet_def; */
			}
			/*: note conc4: "((p1, n1) \<in> pq..spqueue) =
			  (n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
		    }
		    /*: note result1: "((p1, n1) \<in> pq..spqueue) =
		      (n1 = card (indexSet pq p1) \<and> 0 < n1)"
		      forSuch p1, n1; */
		}
		/*: note result2: "\<forall> p1 n1. ((p1, n1) \<in> pq..spqueue) =
		  (n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
	    }
	    /*: note QueueConc:
	      "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init \<longrightarrow>
	      (\<forall> p1 n1. ((p1, n1) \<in> pq..spqueue) = (n1 = card (indexSet pq p1) \<and> 0 < n1))"
	      forSuch pq; */
	}

	{ //: pickAny pq::obj;
	    { //: assuming hyp: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init";
		{ //: assuming case1: "pq = this";
		  //: note SPQueueThis: "spqueue = \<emptyset>";
		  //: note CSizeThis: "csize = 0";
		  /*: note conc1: "pq..csize = card (pq..spqueue)" 
		    from case1, conc1, SPQueueThis, CSizeThis; */
		}
		{ //: assuming case2: "pq \<noteq> this";
		  // note NewNotPQ: "queue \<notin> PriorityQueue";
		  /*: note SPQueueFrame: 
		    "\<forall> pq. pq \<noteq> this \<longrightarrow> pq..spqueue = old (pq..spqueue)"; */
		  /*: note InitFrame: 
		    "\<forall> pq. pq \<noteq> this \<longrightarrow> pq..init = old (pq..init)"; */
		  /*: note conc2: "pq..csize = card (pq..spqueue)" 
		    from conc2, SizeInv, hyp, case2, NewNotPQ, SPQueueFrame, InitFrame; */
		}
	      //: note result: "pq..csize = card (pq..spqueue)";
	    }
	    /*: note conc: 
	      "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init \<longrightarrow> 
	      pq..csize = card (pq..spqueue)" forSuch pq; */
	}
    }

    public int size()
    /*: requires "init"
        ensures "result = card spqueue" */
    {
	return csize;
    }

    public void clear()
    /*: requires "init"
        modifies spqueue
	ensures "spqueue = \<emptyset>" */
    {
	int i = 0;

	while /*: inv "comment ''IBounds'' (0 \<le> i \<and> i \<le> csize) \<and>
		       comment ''NullLoop'' 
		       (\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> queue.[j] = null) \<and>
		       comment ''NullFrame''
		       (\<forall> j. csize \<le> j \<and> j < queue..length \<longrightarrow> queue.[j] = null) \<and>
		       comment ''ArrFrame''
		       (\<forall> arr j. arr \<noteq> queue \<longrightarrow> arr.[j] = old (arr.[j]))" */
	    (i < csize) {

	    queue[i] = null;
	    i = i + 1;
	}
	csize = 0;
	//: "spqueue" := "\<emptyset>";
	
	{ //: pickAny pq::obj;
	    { //: assuming NullHyp: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init";
		{ //: assuming NullThisHyp: "pq = this";
		  /*: note NullThisConc:  "\<forall> j. pq..csize \<le> j \<and> j < pq..queue..length 
		    \<longrightarrow> pq..queue.[j] = null"; */
		}
		{ //: assuming NullOtherHyp: "pq \<noteq> this";
		  //: note QNonNull: "queue \<noteq> null";
		  //: note ThisProps: "this \<in> alloc \<and> this \<in> PriorityQueue \<and> init";
		  /*: note NullOtherConc: "\<forall> j. pq..csize \<le> j \<and> j < pq..queue..length 
		    \<longrightarrow> pq..queue.[j] = null" 
		    from NullOtherConc, NullHyp, NullOtherHyp, IsNullInv, ArrFrame, InjInv, ThisProps, QNonNull; */
		}
		/*: note NullConc: "\<forall> j. pq..csize \<le> j \<and> j < pq..queue..length 
		  \<longrightarrow> pq..queue.[j] = null" from NullConc, NullThisConc, NullOtherConc; */
	    }
	    /*: note NullPost: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init \<longrightarrow>
	      (\<forall> j. pq..csize \<le> j \<and> j < pq..queue..length \<longrightarrow> pq..queue.[j] = null)" 
	      forSuch pq; */
	}

	//: note SizePost: "theinv SizeInv" from SizePost, SizeInv;

	{ //: pickAny pq::obj;
	    { //: assuming hyp1: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init";
		{ //: pickAny p1::obj, n1::int;
		    { //: assuming case1: "pq = this"
		      //: note lhsEmpty: "pq..spqueue = \<emptyset>";
		      //: note rhsEmpty: "(indexSet pq p1) = \<emptyset>";  
		      /*: note conc1: "((p1, n1) \<in> pq..spqueue) =
			(n1 = card (indexSet pq p1) \<and> 0 < n1)"
			from conc1, lhsEmpty, rhsEmpty; */
		    }
		    { //: assuming case2: "pq \<noteq> this"
		      //: note lhsSame: "pq..spqueue = old (pq..spqueue)";
		      //: note QNonNull: "queue \<noteq> null";
		      //: note ThisProps: "this \<in> alloc \<and> this \<in> PriorityQueue \<and> init";
		      /*: note rhsSame: "indexSet pq p1 = old (indexSet pq p1)"
			from rhsSame, case2, hyp1, indexSet_def, arrFrame, InjInv, QNonNull, ThisProps, ArrFrame; */
		      /*: note oldQueueInv: "((p1, n1) \<in> old (pq..spqueue)) =
			(n1 = card (old (indexSet pq p1)) \<and> 0 < n1)"
			from oldQueueInv, QueueInv, hyp; */
		      /*: note newQueueInv: "((p1, n1) \<in> pq..spqueue) =
			(n1 = card (indexSet pq p1) \<and> 0 < n1)" 
			from newQueueInv, oldQueueInv, lhsSame, rhsSame; */
		      /* note conc3: "((p1, n1) \<in> pq..spqueue) =
			 (n1 = card (indexSet pq p1) \<and> 0 < n1)"
			 from conc3, case2, case4, hyp1, QueueInv, init_def, 
			 indexSet_def, ArrFrame, InjInv, ThisProps; */
		    }
		    /*: note result1: "((p1, n1) \<in> pq..spqueue) =
		      (n1 = card (indexSet pq p1) \<and> 0 < n1)"
		      forSuch p1, n1; */
		}
		/*: note result2: "\<forall> p1 n1. ((p1, n1) \<in> pq..spqueue) =
		  (n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
	    }
	    /*: note QueueConc:
	      "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init \<longrightarrow>
	      (\<forall> p1 n1. ((p1, n1) \<in> pq..spqueue) = (n1 = card (indexSet pq p1) \<and> 0 < n1))"
	      forSuch pq; */
	}
    }

    private static int parent(int i)
    /*: requires "i > 0"
        ensures "result >= 0 & result < i & 
	         (i = result + result + 1 | i = result + result +2) \<and> alloc = old alloc"
     */
    {
	return (i-1)/2;
    }

    private static int left(int i)
    /*: requires "0 \<le> i"
        ensures "0 \<le> result \<and> i < result \<and> result = 2 * i + 1 \<and> alloc = old alloc"
     */
    {
	return (2*i + 1);
    }

    private static int right(int i)
    /*: requires "0 \<le> i"
        ensures "0 \<le> result \<and> i < result \<and> result = 2 * i + 2 \<and> alloc = old alloc"
     */
    {
	return (2*i + 2);
    }

    private void grow(int minCapacity)
    /*: requires "init \<and> queue..length < minCapacity\<and> theinvs"
        modifies queue, "new..arrayState"
	ensures "minCapacity \<le> queue..length \<and> theinvs \<and>
	         (\<forall> arr i. arr \<noteq> queue \<longrightarrow> arr.[i] = old (arr.[i]))" */
    {
	int oldCapacity = queue.length;
	int newCapacity = ((oldCapacity < 64) ?
			   ((oldCapacity + 1) * 2):
			   ((oldCapacity / 2) * 3));
	if (newCapacity < minCapacity)
	    newCapacity = minCapacity;

	Comparable copy = new /*: hidden */ Comparable[newCapacity];
	
	int i = 0;

	while /*: inv "comment ''IBounds'' (0 \<le> i \<and> i \<le> csize) \<and>
		       comment ''CopyNonNull''
		       (\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> copy.[j] = queue.[j]) \<and>
		       comment ''CopyNull''
		       (\<forall> j. i \<le> j \<and> j < copy..length \<longrightarrow> copy.[j] = null) \<and>
		       comment ''ArrFrame''
		       (\<forall> arr j. arr \<noteq> copy \<longrightarrow> arr.[j] = old (arr.[j]))" */
	    (i < csize) {

	    copy[i] = queue[i];
	    i = i + 1;
	    
	    /*: note CopyLoop: "\<forall> j. i \<le> j \<and> j < copy..length \<longrightarrow> copy.[j] = null"
	      from CopyLoop, CopyNull; */
	}

	queue = copy;

	{ //: pickAny pq::obj;
	    {//: assuming OrderedHyp: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init";
		{//: assuming OrderedThisHyp: "pq = this";
		 //: note ThisProps: "this \<in> old alloc \<and> old (init)";
		 /*: note OrderedThisOld:
		   "\<forall> i j. (0 \<le> i \<and> i < pq..csize \<and> 0 \<le> j \<and> j < pq..csize \<and> 
		   (j=i+i+1 \<or> j=i+i+2)
		   \<longrightarrow> 0 \<le> (compFunc (old (pq..queue.[i])) (old (pq..queue.[j]))))"
		   from OrderedThisOld, OrderedThisHyp, OrderedHyp, OrderedInv, ThisProps; */
		 /*: note OrderedCopyIs: "
		   \<forall> j. 0 \<le> j \<and> j < csize \<longrightarrow> copy.[j] = old (queue.[j])"; */
		 /*: note OrderedThisConc: 
		   "\<forall> i j. (0 \<le> i \<and> i < pq..csize \<and> 0 \<le> j \<and> j < pq..csize \<and> 
		   (j=i+i+1 \<or> j=i+i+2)
		   \<longrightarrow> 0 \<le> (compFunc (pq..queue.[i]) (pq..queue.[j])))"
		   from OrderedThisConc, OrderedThisOld, OrderedCopyIs, OrderedThisHyp; */
		}
		{//: assuming OrderedOtherHyp: "pq \<noteq> this";
		 //: note CopyNotPQ: "copy \<notin> PriorityQueue";
		 //: note InitFrame: "pq..init = old (pq..init)";
		 /*: note OrderedOtherOld:
		   "\<forall> i j. (0 \<le> i \<and> i < pq..csize \<and> 0 \<le> j \<and> j < pq..csize \<and> 
		   (j=i+i+1 \<or> j=i+i+2)
		   \<longrightarrow> 0 \<le> (compFunc (old (pq..queue.[i])) (old (pq..queue.[j]))))"
		   from OrderedOtherOld, CopyNotPQ, OrderedOtherHyp, OrderedHyp, OrderedInv, InitFrame; */
		 //: note OrderedOtherFrame: "\<forall> i. pq..queue.[i] = old (pq..queue.[i])";
		 /*: note OrderedOtherConc: 
		   "\<forall> i j. (0 \<le> i \<and> i < pq..csize \<and> 0 \<le> j \<and> j < pq..csize \<and> 
		   (j=i+i+1 \<or> j=i+i+2)
		   \<longrightarrow> 0 \<le> (compFunc (pq..queue.[i]) (pq..queue.[j])))"
		   from OrderedOtherConc, OrderedOtherOld, OrderedOtherFrame; */
		}
	     /*: note OrderedAllConc: 
	       "\<forall> i j. (0 \<le> i \<and> i < pq..csize \<and> 0 \<le> j \<and> j < pq..csize \<and> 
	       (j=i+i+1 \<or> j=i+i+2)
	       \<longrightarrow> 0 \<le> (compFunc (pq..queue.[i]) (pq..queue.[j])))"
	       from OrderedAllConc, OrderedOtherConc, OrderedThisConc; */
	    }
	  /*: note OrderedConc:
	    "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init \<longrightarrow>
	     (\<forall> i j. (0 \<le> i \<and> i < pq..csize \<and> 0 \<le> j \<and> j < pq..csize \<and> 
	     (j=i+i+1 \<or> j=i+i+2) \<longrightarrow> 0 \<le> (compFunc (pq..queue.[i]) (pq..queue.[j]))))"
	     forSuch pq; */
	}

	{ //: pickAny pq::obj;
	    {//: assuming IsNullHyp: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init";
		{//: assuming IsNullThisHyp: "pq = this";
		 /*: note IsNullThisConc: 
		   "\<forall> i. pq..csize \<le> i \<and> i < pq..queue..length \<longrightarrow> 
		   pq..queue.[i] = null"; */
		}
		{//: assuming IsNullOtherHyp: "pq \<noteq> this";
		 //: note CopyNotPQ: "copy \<notin> PriorityQueue";
		 //: note InitFrame: "pq..init = old (pq..init)";
		 /*: note IsNullOtherOld: 
		   "\<forall> i. pq..csize \<le> i \<and> i < pq..queue..length \<longrightarrow> 
		   old (pq..queue.[i]) = null"
		   from IsNullOtherOld, InitFrame, CopyNotPQ, IsNullInv, IsNullHyp, IsNullOtherHyp; */
		 //: note IsNullOtherFrame: "\<forall> i. pq..queue.[i] = old (pq..queue.[i])";
		 /*: note IsNullOtherConc: 
		   "\<forall> i. pq..csize \<le> i \<and> i < pq..queue..length \<longrightarrow> 
		   pq..queue.[i] = null"
		   from IsNullOtherConc, IsNullOtherFrame, IsNullOtherOld; */
		}
	     /*: note IsNullConc: 
	       "\<forall> i. pq..csize \<le> i \<and> i < pq..queue..length \<longrightarrow> 
	       pq..queue.[i] = null"; */
	    }
	  /*: note IsNullConc:
	    "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init \<longrightarrow>
	    (\<forall> i. pq..csize \<le> i \<and> i < pq..queue..length \<longrightarrow> pq..queue.[i] = null)"
	    forSuch pq; */
	}


	{ //: pickAny pq::obj;
	    {//: assuming NonNullHyp: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init";
		{//: assuming NonNullThisHyp: "pq = this";
		 /*: note ThisOldNonNull: 
		   "\<forall> i. 0 \<le> i \<and> i < csize \<longrightarrow> old (queue.[i]) \<noteq> null"; */
		 /*: note CopyIs: "
		   \<forall> j. 0 \<le> j \<and> j < csize \<longrightarrow> copy.[j] = old (queue.[j])"; */
		 /*: note NonNullThisConc: 
		   "\<forall> i. 0 \<le> i \<and> i < pq..csize \<longrightarrow> pq..queue.[i] \<noteq> null"
		   from NonNullThisConc, NonNullThisHyp, ThisOldNonNull, CopyIs; */
		}
		{//: assuming NonNullOtherHyp: "pq \<noteq> this";
		 /*: note OtherOldNonNull:
		   "\<forall> i. 0 \<le> i \<and> i < pq..csize \<longrightarrow> 
		   old (pq..queue.[i]) \<noteq> null"; */
		 //: note OtherFrame: "\<forall> i. pq..queue.[i] = old (pq..queue.[i])";
		 /*: note NonNullOtherConc:
		   "\<forall> i. 0 \<le> i \<and> i < pq..csize \<longrightarrow> pq..queue.[i] \<noteq> null"
		   from NonNullOtherConc, OtherOldNonNull, OtherFrame, NonNullOtherHyp; */
		}
	     /*: note NonNullAllConc:
	       "\<forall> i. 0 \<le> i \<and> i < pq..csize \<longrightarrow> pq..queue.[i] \<noteq> null"
	       from NonNullAllConc, NonNullThisConc, NonNullOtherConc; */
	    }
	  /*: note NonNullConc:
	    "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init \<longrightarrow>
	    (\<forall> i. 0 \<le> i \<and> i < pq..csize \<longrightarrow> pq..queue.[i] \<noteq> null)"
	    forSuch pq; */
	}
       
	//: note NewNotPQ: "copy \<notin> PriorityQueue";
	//: note InitFrame: "\<forall> pq. pq..init = old (pq..init)";

	{ //: pickAny pq::obj;
	    { //: assuming hyp: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init";
	      //: note Init: "old (pq..init)";
	      //: note NewNotPQ: "copy \<notin> PriorityQueue";
	      /*: note result: "pq..csize = card (pq..spqueue)"
		from result, SizeInv, hyp, NewNotPQ, Init; */
	    }
	    /*: note SizeConc: 
	      "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init \<longrightarrow> 
	      pq..csize = card (pq..spqueue)" forSuch pq; */
	}

	{ //: pickAny pq::obj;
	    { //: assuming hyp1: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init";
		{ //: pickAny p1::obj, n1::int;
		    { //: assuming NewObj: "pq = copy";
		      /*: note NewConc: "((p1, n1) \<in> pq..spqueue) = 
			(n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
		    }
		    { //: assuming OldObj: "pq \<noteq> copy";
		      //: note Init: "old (pq..init)";
		      /*: note OldQueue: "((p1, n1) \<in> pq..spqueue) =
			(n1 = card (old (indexSet pq p1)) \<and> 0 <  n1)"
			from OldQueue, OldObj, hyp1, QueueInv, Init; */
			{ //: assuming ThisQ: "pq = this";
			  /*: note CopyIs: "\<forall> j. 0 \<le> j \<and> j < csize \<longrightarrow> 
			    copy.[j] = queue.[j]"; */
			  //: note ThisSame: "(indexSet pq p1) = old (indexSet pq p1)";
			  /*: note ThisConc: "((p1, n1) \<in> pq..spqueue) =
			    (n1 = card (indexSet pq p1) \<and> 0 <  n1)"
			    from ThisConc, ThisSame, OldQueue; */
			}
			{ //: assuming OtherQ: "pq \<noteq> this";
			  //: note OtherSame: "(indexSet pq p1) = old (indexSet pq p1)"
			  /*: note NotThisConc: "((p1, n1) \<in> pq..spqueue) =
			    (n1 = card (indexSet pq p1) \<and> 0 < n1)"
			    from NotThisConc, OtherSame, OldQueue; */
			}
			/*: note result0: "((p1, n1) \<in> pq..spqueue) =
			  (n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
		    }
		    /*: note result1: "((p1, n1) \<in> pq..spqueue) =
		      (n1 = card (indexSet pq p1) \<and> 0 < n1)"
		      forSuch p1, n1; */
		}
		/*: note result2: "\<forall> p1 n1. ((p1, n1) \<in> pq..spqueue) =
		  (n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
	    }
	    /*: note QueueConc:
	      "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init \<longrightarrow>
	      (\<forall> p1 n1. ((p1, n1) \<in> pq..spqueue) = (n1 = card (indexSet pq p1) \<and> 0 < n1))"
	      forSuch pq; */
	}
    }

    private int indexOf(Object o1)
    /*: requires "init \<and> theinvs"
        ensures "((\<exists> i. 0 \<le> i \<and> i < csize \<and> queue.[i] = o1) \<longrightarrow> 
	         queue.[result] = o1 \<and> 0 \<le> result \<and> result < csize) \<and>
		 (\<not> (\<exists> i. 0 \<le> i \<and> i < csize \<and> queue.[i] = o1) \<longrightarrow> 
		 result = -1) \<and> theinvs" */
    {
	if (o1 != null) {

	    int i = 0;

	    while /*: inv "0 \<le> i \<and> i \<le> csize \<and>
		           (\<forall> j. 0 \<le> j \<and> j < i \<longrightarrow> queue.[j] \<noteq> o1)" */
		(i < csize) {
		
		if (o1 == queue[i]) {
		    //: note Found: "\<exists> j. 0 \<le> j \<and> j < csize \<and> queue.[j] = o1";
		    return i;
		}

		i = i + 1;
	    }
	}
	return -1;
    }

    public boolean contains(Object o1)
    /*: requires "init"
        ensures "result = (\<exists> i. (o1, i) \<in> spqueue)" */
    {
	int index = indexOf(o1);
	boolean result = (index != -1);
	{//: assuming IsFoundHyp: "\<exists> i. 0 \<le> i \<and> i < csize \<and> queue.[i] = o1";
	 /*: note IsFoundPost: 
	   "(\<exists> i. 0 \<le> i \<and> i < csize \<and> queue.[i] = o1) \<longrightarrow> 
	   queue.[index] = o1 \<and> 0 \<le> index \<and> index < csize"; */
	 /*: note IsFoundIndex: "queue.[index] = o1 \<and> 0 \<le> index \<and> index < csize"
	   from IsFoundIndex, IsFoundHyp, IsFoundPost; */
	 //: note NotNegOne: "index \<noteq> -1" from NotNegOne, IsFoundIndex;
	 //: note IsInIndexSet: "index \<in> (indexSet this o1)" from IsInIndexSet, indexSet_def, IsFoundIndex;
	 // note SubsetEq: "{index} \<subseteq> (indexSet this o1)" from SubsetEq, IsInIndexSet;
	 // note Blah: "0 < card (indexSet this o1)" from Blah, SubsetEq;
	    {//: assuming IsSingletonHyp: "{index} = (indexSet this o1)";
	     //: note IsSingletonConc: "0 < card (indexSet this o1)" from IsSingletonHyp, IsSingletonConc;
	    }
	    {//: assuming NotSingletonHyp: "{index} \<subset> (indexSet this o1)";
	     /*: note NotSingletonConc: "0 < card (indexSet this o1)" 
	       from NotSingletonHyp, NotSingletonConc; */
	    }
	 /*: note CardIndexSet: "0 < card (indexSet this o1)" 
	   from CardIndexSet, IsSingletonConc, NotSingletonConc, IsInIndexSet;  */
	 //: note ThisProps: "this \<in> old alloc \<and> this \<in> PriorityQueue \<and> init";
	 /*: note IsFoundQDef:
	   "\<forall> n. ((o1, n) \<in> spqueue) = (n = card(indexSet this o1) \<and> 0 < n)"
	   from IsFoundQDef, QueueInv, ThisProps; */
	 //: note IsFoundInQ: "\<exists> i. (o1, i) \<in> spqueue" from IsFoundInQ, CardIndexSet, IsFoundQDef;
	 /*: note IsFoundConc: "result = (\<exists> i. (o1, i) \<in> spqueue)"
	   from IsFoundConc, NotNegOne, IsFoundInQ; */
	}
	{//: assuming NotFoundHyp: "\<not> (\<exists> i. 0 \<le> i \<and> i < csize \<and> queue.[i] = o1)";
	 /*: note NotFoundPost: "\<not> (\<exists> i. 0 \<le> i \<and> i < csize \<and> queue.[i] = o1) 
	   \<longrightarrow> index = -1"; */
	 //: note NotFoundIndex: "index = -1" from NotFoundIndex, NotFoundHyp, NotFoundPost;
	 //: note NotInIndexSet: "indexSet this o1 = {}" from NotInIndexSet, indexSet_def, NotFoundHyp;
	 //: note CardIndexSet: "0 = card (indexSet this o1)" from CardIndexSet, NotInIndexSet;
	 //: note ThisProps: "this \<in> old alloc \<and> this \<in> PriorityQueue \<and> init";
	 /*: note NotFoundQDef: 
	   "\<forall> n. ((o1, n) \<in> spqueue) = (n = card(indexSet this o1) \<and> 0 < n)"
	   from NotFoundQDef, QueueInv, ThisProps; */
	 /*: note NotFoundInQ: "\<not> (\<exists> i. (o1, i) \<in> spqueue)" 
	   from NotFoundInQ, CardIndexSet, NotFoundQDef; */
	 /*: note NotFoundConc: "result = (\<exists> i. (o1, i) \<in> spqueue)"
	   from NotFoundConc, NotFoundInQ, NotFoundIndex; */
	}
	/*: note ResultPost: "result = (\<exists> i. (o1, i) \<in> spqueue)" 
	  from ResultPost, IsFoundConc, NotFoundConc; */
	return result;
    }

    public Comparable peek()
    /*: requires "init"
        ensures "(spqueue = \<emptyset> \<longrightarrow> result = null) \<and> 
	         (spqueue \<noteq> \<emptyset> \<longrightarrow>
		  result \<noteq> null \<and>
		  (\<exists> n. (result, n) \<in> spqueue) \<and>
		  (\<forall> x m. (x, m) \<in> spqueue \<longrightarrow> (0 \<le> (compFunc result x))))" */
    {
	if (csize == 0) {
	    //: note Empty: "card spqueue = 0";
	    //: note NoElems: "spqueue = \<emptyset>";
	    return null;
	}

	{//: pickAny x::obj, m::int;
	    {//: assuming PostHyp: "(x, m) \<in> spqueue";
	     //: note NotEmpty: "0 < card (indexSet this x)";
	     //: note ExistsOne: "\<exists> y. y \<in> (indexSet this x)";
	     /*: note HasIndex: "\<exists> ind. 0 \<le> ind \<and> ind < csize \<and> x = queue.[ind]"
	       from HasIndex, indexSet_def, ExistsOne; */
	     //: note ArrLength: "0 < csize";
	     //: assume Reflexive: "\<forall> x. compFunc x x = 0";
	     /*: assume Transitive: 
	       "\<forall> x y z. 0 \<le> compFunc x y \<and> 0 \<le> compFunc y z 
	       \<longrightarrow> 0 \<le> compFunc x z"; */
	     /*: noteThat Ordering:
	       "(\<forall> i j.
	       ((0 \<le> i \<and> i < csize \<and> 0 \<le> j \<and> j < csize \<and> 
	       ((j = i + i + 1) | (j = i + i + 2)) \<longrightarrow> 
	       (0 \<le> (compFunc (queue.[i]) (queue.[j])))))) \<longrightarrow>
	       (\<forall> k. ((0 \<le> k \<and> k < csize) \<longrightarrow> 
	       (0 \<le> (compFunc (queue.[0]) (queue.[k])))))"
	       from ArrLength, Ordering, Reflexive, Transitive; */
	     //: note PostMin: "0 \<le> (compFunc (queue.[0]) x)";
	    }
	 /*: note PostConc: 
	   "(x, m) \<in> spqueue \<longrightarrow> (0 \<le> (compFunc (queue.[0]) x))"
	   forSuch x, m; */
	}
	return queue[0];
    }

    public Comparable poll()
    /*: requires "init"
        modifies spqueue
        ensures  "(old spqueue = \<emptyset> \<longrightarrow> 
	          result = null \<and> spqueue = old spqueue) \<and>
	          (old spqueue \<noteq> \<emptyset> \<longrightarrow> 
		   result \<noteq> null \<and> 
		   (\<exists> n. (result, n) \<in> old spqueue \<and>
		    (\<forall> x m. (x, m) \<in> old spqueue \<longrightarrow>
		    (0 < (compFunc result x))) \<and>
		    (n = 1 \<longrightarrow> 
		      (spqueue = old spqueue \<setminus> {(result, n)})) \<and>
		    (n < 1 \<longrightarrow> 
		      (spqueue = old spqueue \<setminus> {(result, n)} \<union> {(result, n - 1)}))))" */
    {
	if (csize == 0) {
	    //: assume "False";
	    //: note CardZero: "card spqueue = 0";
	    //: note Empty: "spqueue = \<emptyset>";
	    return null;
	}
	Comparable result = queue[0];
	csize = csize - 1;
	queue[0] = queue[csize];
	queue[csize] = null;
	//: note OldSize: "0 < old csize";
	/*: note IndexDef: 
	  "(old indexSet) this result = 
	   {i. 0 \<le> i \<and> i < (old csize) \<and> result = old (queue.[i])}"; */
	/*: note HasIndex: "0 \<in> (old indexSet) this result" 
	  from HasIndex, IndexDef, OldSize; */
	//: note IndexCard: "0 < card ((old indexSet) this result)";
	//: note ThisProps: "this \<in> alloc \<and> this \<in> PriorityQueue \<and> init";
	/*: note QueueDef: 
	  "\<forall> n1. ((result, n1) \<in> old spqueue) = 
	  (n1 = card ((old indexSet) this result) \<and> 0 < n1)"
	  from QueueDef, ThisProps, QueueInv; */
	/*: note InQueue: "\<exists> n1. (result, n1) \<in> old spqueue"
	  from InQueue, QueueDef, IndexCard; */
	//: ghost specvar n :: int;
	//: havoc n suchThat "(result, n) \<in> old spqueue";
	/*: "spqueue" := "if (n = 1) then spqueue \<setminus> {(result, n)} else
	                  spqueue \<setminus> {(result, n)} \<union> {(result, n - 1)}"; */

	{//: pickAny pq :: obj;
	    { //: assuming QueueHyp: "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init";
		{ //: pickAny p1::obj, n1::int;
		    { //: assuming ThisQueueHyp: "pq = this"
			{//: assuming IsResultQueueHyp: "p1 = result";
			    {//: assuming NotLastInstanceHyp: "n \<noteq> 1";
			     //: note InOldPQ: "(result, n) \<in> old spqueue";
			     /*: note OldCard: "card (old (indexSet pq p1)) = n \<and> 0 < n"
			       from OldCard,  InOldPQ, QueueDef, NotLastInstanceHyp, ThisQueueHyp,
			       QueueHyp; */
				{//: assuming IsEndHyp: "old (queue.[0]) = old (queue.[csize - 1])";
				 //: note SizeInSet: "csize \<in> old (indexSet pq p1)";
				 /*: note CardChange1: "card ((old (indexSet pq p1)) - {csize}) = 
				   card (old (indexSet pq p1)) - 1"; */
				 //: note IndexIs1: "indexSet pq p1 = old (indexSet pq p1) - {csize}";
				 /*: note NewCard1: "card (indexSet pq p1) = n - 1"
				   from NewCard1, IndexIs1, CardChange1, OldCard; */
				}
				{//: assuming NotEndHyp: "old (queue.[0]) \<noteq> old (queue.[csize - 1])";
				 //: note ZeroInSet: "0 \<in> old (indexSet pq p1)";
				 /*: note CardChange2: "card ((old (indexSet pq p1)) - {0}) =
				   card (old (indexSet pq p1)) - 1"; */
				 /*: note IndexIs2: "indexSet pq p1 = old (indexSet pq p1) - {0}"
				  from IndexIs2, NotEndHyp, NotLastInstanceHyp, IsResultQueueHyp,
				  ThisQueueHyp, QueueHyp, indexSet_def; */
				 /*: note NewCard2: "card (indexSet pq p1) = n - 1"
				   from NewCard2, IndexIs2, CardChange2, OldCard; */
				}
				/*: note NewCard: "card (indexSet pq p1) = n - 1"
				   from NewCard, NewCard1, NewCard2; */
				{//: assuming ParticularN1Hyp: "n1 = n - 1";
				 //: note lhsA1: "(p1, n1) \<in> pq..spqueue";
				 //: note rhsA1: "n1 = card (indexSet pq p1) \<and> 0 < n1";
				 /*: note ParticularN1Conc: "((p1, n1) \<in> pq..spqueue) =
				   (n1 = card (indexSet pq p1) \<and> 0 < n1)"
				   from ParticularN1Conc, lhsA1, rhsA1; */
				}
				{//: assuming OtherN1Hyp: "n1 \<noteq> n - 1";
				 //: note lhsA2: "(p1, n1) \<notin> pq..spqueue";
				 /*: note rhsA2: "n1 \<noteq> card (indexSet pq p1)"
				   from rhsA2, OtherN1Hyp, NewCard; */
				 /*: note OtherN1Conc: "((p1, n1) \<in> pq..spqueue) =
				   (n1 = card (indexSet pq p1) \<and> 0 < n1)"
				   from OtherN1Conc, lhsA2, rhsA2; */
				}
			    /*: note NotLastInstanceConc: "((p1, n1) \<in> pq..spqueue) =
			      (n1 = card (indexSet pq p1) \<and> 0 < n1)"
			      from NotLastInstanceConc, OtherN1Conc, ParticularN1Conc; */
			    }
			    {//: assuming IsLastInstanceHyp: "n = 1";
			     //: note lhsB: "(p1, n1) \<notin> pq..spqueue";

			     //: note NInOld: "(result, 1) \<in> old spqueue";
			     /*: note CardOldIndexSet: "card ((old (indexSet pq p1))) = 1"
			       from CardOldIndexSet, QueueHyp, ThisQueueHyp, IsResultQueueHyp, 
			       IsLastInstanceHyp, NInOld, QueueDef; */

			     //: note ZeroInOld: "0 \<in> (old (indexSet pq p1))";

			     //: note OldIndexSet: "(old (indexSet pq p1)) = {0}";

			     /*: note indexSetNow: "(indexSet pq p1) = {}"
			       from indexSetNow, OldIndexSet, indexSet_def, IsLastInstanceHyp, 
			       IsResultQueueHyp, ThisQueueHyp, QueueHyp; */
			     //: note rhsB: "card (indexSet pq p1) = 0";

			     // note ZeroInOld: "0 \<in> (old (indexSet pq p1))";
			     // note OldIndexSet: "(old (indexSet pq p1)) = {0}";
				{// assuming IsEmptyHyp: "csize = 0";
				 /* note IsEmptyConc: "((p1, n1) \<in> pq..spqueue) =
				   (n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
				}
				{// assuming NotEmptyHyp: "csize \<noteq> 0";
				 // note NotInOld: "csize \<notin> (old (indexSet pq p1))";
				 /* note NotLastElem: "old (queue.[0]) \<noteq> old (queue.[csize - 1])"
				   from NotLastElem, QueueHyp, ThisQueueHyp, IsResultQueueHyp, 
				   IsLastInstanceHyp, NotEmptyHyp, indexSet_def, OldIndexSet, OldSize; */
				 /* note IndexChange: "(indexSet pq p1) = (old (indexSet pq p1)) - {0}"
				   from IndexChange, NotLastElem, QueueHyp, ThisQueueHyp, IsResultQueueHyp, 
				   IsLastInstanceHyp, indexSet_def; */
				 // note InIndexSet: "0 \<in> (old (indexSet pq p1))";
				 /* note CardChange: 
				   "card ((old (indexSet pq p1)) - {0}) = card (old (indexSet pq p1)) - 1"; */
				 // note CardOld: "card (old (indexSet pq p1)) = n1";
				 // note CardNow: "card (indexSet pq p1) = 0";

				 /* note NotEmptyConc: "((p1, n1) \<in> pq..spqueue) =
				   (n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
				}
			     /*: note IsLastInstanceConc: "((p1, n1) \<in> pq..spqueue) =
			       (n1 = card (indexSet pq p1) \<and> 0 < n1)"
			       from IsLastInstanceConc, lhs, rhs; */
			    }
			 /*: note IsResultQueueConc: "((p1, n1) \<in> pq..spqueue) =
			   (n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
			}
			{//: assuming NotResultQueueHyp: "p1 \<noteq> result";
			    {//: assuming IsLastHyp: "p1 = old (queue.[(csize - 1)])";
			     //: note SizeGtZero: "0 < csize";
			     /*: note IndexChange: 
			       "(indexSet pq p1) = (old (indexSet pq p1)) - {csize} Un {0}"
			       from IndexChange, indexSet_def, IsLastHyp, NotResultQueueHyp,
			       ThisQueueHyp, SizeGtZero; */
			     //: note IsInIndexSet: "csize \<in> old (indexSet pq p1)";
			     /*: note Card1: 
			       "card ((old (indexSet pq p1)) - {csize}) = card (old (indexSet pq p1)) - 1"
			       from Card1, IsInIndexSet; */
			     //: note NotInIndexSet: "0 \<notin> ((old (indexSet pq p1)) - {csize})";
			     /*: note Card2:
			       "card ((old (indexSet pq p1)) - {csize} Un {0}) =
			       card ((old (indexSet pq p1)) - {csize}) + 1"; */
			     /*: note CardFrame: "card (indexSet pq p1) = old (card (indexSet pq p1))"
			       from CardFrame, IndexChange, Card1, Card2; */
			     /*: note IsLastQueueConc: "((p1, n1) \<in> pq..spqueue) =
			       (n1 = card (indexSet pq p1) \<and> 0 < n1)"
			       from IsLastQueueConc, NotResultQueueHyp, ThisQueueHyp, QueueHyp,
			       QueueInv, CardFrame, IsLastHyp; */
			    }
			    {//: assuming NotLastHyp: "p1 \<noteq> old (queue.[(csize - 1)])";
			     /*: note IndexSetFrame: "(indexSet pq p1) = ((old indexSet) pq p1)"
			       from IndexSetFrame, indexSet_def, NotLastHyp, NotResultQueueHyp,
			       ThisQueueHyp; */
			     /*: note NotLastQueueConc: "((p1, n1) \<in> pq..spqueue) =
			       (n1 = card (indexSet pq p1) \<and> 0 < n1)"
			       from NotLastQueueConc, NotResultQueueHyp, ThisQueueHyp, QueueHyp,
			       QueueInv, IndexSetFrame, NotLastHyp; */
			    }
			    /*: note NotResultQueueConc: "((p1, n1) \<in> pq..spqueue) =
			      (n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
			}
		      /*: note ThisQueueConc: "((p1, n1) \<in> pq..spqueue) =
			(n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
		    }
		    { //: assuming OtherQueueHyp: "pq \<noteq> this"
		      /* note OldQueue: "((p1, n1) \<in> old (pq..spqueue)) =
			(n1 = card ((old indexSet) pq p1) \<and> 0 < n1)"; */
		      // note QueueFrame: "pq..spqueue = old (pq..spqueue)";
		      //: note IndexSetFrame: "(indexSet pq p1) = ((old indexSet) pq p1)";
		      /*: note OtherQueueConc:  "((p1, n1) \<in> pq..spqueue) =
			(n1 = card (indexSet pq p1) \<and> 0 < n1)"
			from OtherQueueConc, OtherQueueHyp, QueueHyp, QueueInv, IndexSetFrame; */
		    }
		    /*: note AllQueueConc: "((p1, n1) \<in> pq..spqueue) =
		      (n1 = card (indexSet pq p1) \<and> 0 < n1)"
		      forSuch p1, n1; */
		}
		/*: note PreQueueConc: "\<forall> p1 n1. ((p1, n1) \<in> pq..spqueue) =
		  (n1 = card (indexSet pq p1) \<and> 0 < n1)"; */
	    }
	 /*: note QueueConc:
	      "pq \<in> alloc \<and> pq \<in> PriorityQueue \<and> pq..init \<longrightarrow>
	      (\<forall> p1 n1. ((p1, n1) \<in> pq..spqueue) = (n1 = card (indexSet pq p1) \<and> 0 < n1))"
	      forSuch pq; */
	}
	//: assume "False";

	if (0 < csize)
	    heapify(0);
	return result;
    }
    

    public boolean remove(Object o1)
    /*: requires "init"
        modifies "spqueue"
	ensures "(\<not> (\<exists> i. (o1, i) \<in> old spqueue) \<longrightarrow> 
	         (spqueue = old spqueue \<and> (\<not> result))) \<and>
		 ((\<exists> i. (o1, i) \<in> old spqueue) \<longrightarrow> 
		 (\<exists> i. (o1, i) \<in> old spqueue \<and> result \<and> 
		  (i = 1 \<longrightarrow> spqueue = old spqueue - {(o1, 1)}) \<and>
		  (1 < i \<longrightarrow> spqueue = old spqueue - {(o1, i)} \<union> {(o1, (i - 1))})))" */
    {
	int i = indexOf(o1);
	if (i == -1)
	    return false;
	else {
	    //removeAt(i);
	    return true;
	}
    }

    public void insert(Comparable e)
    /*: requires "init"
        modifies spqueue
	ensures "(e = null \<longrightarrow> spqueue = old spqueue) \<and>
	         (e \<noteq> null \<longrightarrow> 
	           ((\<not> (\<exists> n. (e, n) \<in> spqueue)) \<longrightarrow> 
		     (spqueue = old spqueue \<union> {(e, 1)})) \<and>
		   (\<exists> n. (e, n) \<in> spqueue \<longrightarrow>
		     (spqueue = old spqueue \<setminus> {(e, n)} \<union> {(e, n+1)})))" */
    {
	int i = csize;
	csize = csize + 1;

	while /*: inv "(comment ''IBounds'' (0 \<le> i \<and> i < csize)) & 
		       (comment ''RelToI''
		        (((i + i + 1 < csize) -->
			  (0 < (compFunc (queue.[(i + i + 1)]) e))) &
			 ((i + i + 2 < csize) -->
			  (0 < (compFunc (queue.[(i + i + 2)]) e))))) &
		       (comment ''ContentPostLoop''
		       (old spqueue = {(p, n). n = card {j. 0 \<le> j \<and> j < csize \<and> j \<noteq> i \<and> p = queue.[j]} \<and> 0 < n})) \<and>
		       (ALL j. 0 <= j & j < csize & j ~= i --> 
		               queue.[j] ~= null) & 
		       (comment ''PDBefore''
		        (ALL j k. 0 <= j & j < csize & 0 <= k & k < csize &
		                 queue.[j] = queue.[k] & j ~= i & k ~= i --> 
				 j = k)) &
		       theinv IsNullInv &
		       (comment ''OrderedSkipLoop''
		       (i = (old csize) -->
		        (ALL j k. 
			 (0 <= j & j < (old csize) & 0 <= k & 
			  k < (old csize) &
			  ((k = j + j + 1) | (k = j + j + 2)) -->
			   (0 \<le> (compFunc (queue.[j]) (queue.[k]))))))) &
		       (comment ''OrderedPostLoop''
		       (i ~= (old csize) -->
		        (ALL j k. 
		         (0 <= j & j < csize & 0 <= k & k < csize &
			  ((k = j + j + 1) | (k = j + j + 2)) -->
			   (0 \<le> (compFunc (queue.[j]) (queue.[k]))))))) \<and>
                       (\<forall> a i. a ~= queue \<longrightarrow> a.[i] = old (a.[i])) \<and>
                       (comment ''OrderedFrame'' 
                       (\<forall> pq. pq : PriorityQueue \<and> pq : alloc \<and> pq..init \<and> 
                        pq \<noteq> this \<longrightarrow> (\<forall> i j. 0 \<le> i \<and> i < pq..csize \<and> 0 \<le> j \<and> 
                        j < pq..length \<and> (j = i + i + 1 \<or> j = i + i + 2) \<longrightarrow> 
			(0 < (compFunc (pq..queue.[i]) (pq..queue.[j]))))))"
	      */
	    (i > 0 && queue[parent(i)].compareTo(e))
	{
	    int p = parent(i);

	    //: noteThat PBounds: "0 \<le> p \<and> p < old csize";
	    //: noteThat PIRel: "i = p + p + 1 | i = p + p + 2";
	    //: note InLoop: "0 < (compFunc (queue.[p]) e)";

	    queue[i] = queue[p];

	    /*: note iEffect1: "ALL jj. (0 \<le> jj \<and> jj < csize \<and> 
	        ((i = jj + jj + 1) | (i = jj + jj + 2)) \<longrightarrow> 
		(0 \<le> (compFunc (queue.[jj]) (queue.[i]))))"; */
	    /*: note iEffect2: "ALL kk. (0 \<le> kk \<and> kk < csize \<and>
                ((kk = i + i + 1) | (kk = i + i + 2)) \<longrightarrow>
		(0 \<le> (compFunc (queue.[i]) (queue.[kk]))))"
	        from iEffect2, OrderedPostLoop, InLoop, PIRel, PBounds; */
	    /*: note OtherEffect: 
	      "ALL jj kk. (0 \<le> jj \<and> jj < csize \<and> 0 \<le> kk \<and> kk < csize \<and> 
	       jj \<noteq> i \<and> kk \<noteq> i \<and> ((kk = jj + jj + 1) | (kk = jj + jj + 2)) \<longrightarrow> 
	       (0 \<le> (compFunc (queue.[jj]) (queue.[kk]))))"; */

	    i = p;

	    /*: noteThat sameAfter:
	      "ALL jj kk. (0 <= jj & jj < csize & 0 <= kk & kk < csize & 
	      ((kk = jj + jj + 1) | (kk = jj + jj + 2)) -->
	      (0 \<le> (compFunc (queue.[jj]) (queue.[kk]))))"
	      from sameAfter, iEffect1, iEffect2, OtherEffect; */

	    /*: noteThat ContentAfter:
	      "old spqueue = 
	       {(p, n). n = card {j. 0 \<le> j \<and> j < csize & j \<noteq> i & p = queue.[j]} \<and> 0 < n}"
	      from ContentPostLoop, IBounds, PBounds, ContentAfter;
	    */
	    /*: noteThat PDAfter:
	      "(ALL j k. 0 <= j & j < csize & 0 <= k & k < csize &
	                 queue.[j] = queue.[k] & j ~= i & k ~= i --> j = k)"
	      from PDBefore, PBounds, PDAfter;
	    */
	}
	queue[i] = e;
	/*: noteThat ContentDef:
	  "spqueue = {(p, n). n = card {j. 0 \<le> j \<and> j < csize \<and> p = queue.[j]} \<and> 0 < n}";
	*/
	/* noteThat ContentFinal: "spqueue = old spqueue Un { e }"
	  from ContentPostLoop, ContentDef, IBounds, ContentFinal;
	*/
    }

    public Comparable extractMax()
    /*: requires "init"
        modifies spqueue
        ensures  "(old spqueue = \<emptyset> \<longrightarrow> result = null \<and> spqueue = old spqueue) \<and>
	          (old spqueue \<noteq> \<emptyset> \<longrightarrow> 
		   result \<noteq> null \<and> 
		   (\<exists> n. (result, n) \<in> old spqueue \<and>
		    (\<forall> x m. (x, m) \<in> old spqueue \<longrightarrow>
		    (0 < (compFunc result x))) \<and>
		    (n = 1 \<longrightarrow> 
		      (spqueue = old spqueue \<setminus> {(result, n)})) \<and>
		    (n < 1 \<longrightarrow> 
		      (spqueue = old spqueue \<setminus> {(result, n)} \<union> {(result, n - 1)}))))" */
    {
	Comparable result = queue[0];
	//: noteThat ArrLength: "0 < csize";
	/*: noteThat Ordering:
	  "(\<forall> i j.
	    ((0 \<le> i \<and> i < csize \<and> 0 \<le> j \<and> j < csize \<and> 
             ((j = i + i + 1) | (j = i + i + 2)) \<longrightarrow> 
	     (0 \<le> (compFunc (queue.[i]) (queue.[j])))))) \<longrightarrow>
	   (\<forall> k. ((0 \<le> k \<and> k < csize) \<longrightarrow> 
	     (0 \<le> (compFunc (queue.[0]) (queue.[k])))))"
          from ArrLength, Ordering; */
	csize = csize - 1;
	queue[0] = queue[csize];
	queue[csize] = null;
	if (0 < csize) heapify(0);
	return result;
    }

    private void heapify(int i)
    /*: requires "init \<and> 0 \<le> i \<and> i < csize \<and>
                  theinv QueueInv \<and>
		  theinv SizeInv \<and>
                  theinv SizeLowerInv \<and>
                  theinv SizeUpperInv \<and> 
		  theinv NonNullInv \<and>
		  theinv IsNullInv \<and> 
		  theinv HiddenInv \<and>
		  theinv InjInv \<and>
		  comment ''GlobalOrderingPre''
		   (\<forall> k j.
		    (0 <= k & k < csize & k ~= i & 0 < j & j < csize &
		    ((j = k + k + 1) | (j = k + k + 2)) -->
		    (0 \<le> (compFunc (queue.[k]) (queue.[j]))))) \<and>
		  comment ''LocalOrderingPre''
		   (\<forall> x. 
		    ((0 <= x & (i = x + x + 1 | i = x + x + 2)) -->
		     (((i + i + 1 < csize) --> 
		      (0 \<le> (compFunc (queue.[x]) (queue.[(i + i + 1)]))) &
		      ((i + i + 2 < csize) -->
		      (0 \<le> (compFunc (queue.[x]) (queue.[(i + i + 2)])))))))) \<and>
                  (comment ''OrderedFrame'' 
                   (\<forall> pq. pq : PriorityQueue \<and> pq : alloc \<and> pq..init \<and> pq \<noteq> this \<longrightarrow> 
	            (\<forall> i j. 0 \<le> i \<and> i < pq..csize \<and> 0 \<le> j \<and> j < pq..csize \<and> 
	             (j = i + i + 1 \<or> j = i + i + 2) \<longrightarrow> 
		     (0 \<le> (compFunc (pq..queue.[i]) (pq..queue.[j]))))))"
        modifies "Array.arrayState"
        ensures "(\<forall> pq. pq..init = old (pq..init)) \<and> 
	         (\<forall> pq. pq..spqueue = old (pq..spqueue)) \<and> 
	         alloc = old alloc \<and> theinvs \<and>
	         (\<forall> a i. a \<noteq> queue \<longrightarrow> a.[i] = old (a.[i]))" */
    {
	int m = i;

	int l = 2 * i + 1;
	if (l < csize && (0 < queue[l].compareTo(queue[i])))
	    m = l;

	int r = right(i);
	if (r < csize && (0 > queue[r].compareTo(queue[m])))
	    m = r;

	if (m != i)
	{
	    //: noteThat LeftDef: "l = i + i + 1";
	    //: noteThat RightDef: "r = i + i + 2";
	    /*: noteThat mLeft: 
	      "m = l \<longrightarrow>
	        (0 < (compFunc (queue.[l]) (queue.[i]))) \<and>
		(r < csize \<longrightarrow>
		  (0 \<le> (compFunc (queue.[l]) (queue.[r]))))"; */
	    /*: noteThat mRight:
	      "m = r \<longrightarrow>
	        (0 < (compFunc (queue.[r]) (queue.[i]))) \<and>
		(l < csize \<longrightarrow>
		  (0 \<le> (compFunc (queue.[r]) (queue.[l]))))"; */


	    Comparable p = queue[m];
	    queue[m] = queue[i];
	    queue[i] = p;

	    //: noteThat iLB: "0 \<le> i";
	    //: noteThat iUB: "i < csize";
	    //: noteThat mBounds: "0 \<le> m \<and> m < csize";
	    /*: noteThat LocalOrder:
	      "((i + i + 1 < csize) \<longrightarrow> 
	        (0 \<le> (compFunc (queue.[i]) (queue.[(i + i + 1)])))) \<and> 
	       ((i + i + 2 < csize) \<longrightarrow> 
	        (0 \<le> (compFunc (queue.[i]) (queue.[(i + i + 2)]))))"
		from LeftDef, RightDef, mRight, mLeft, iLB, LocalOrder; */
	    /*: noteThat OrderingLem:
	      "(\<forall> k j.
		(0 \<le> k \<and> k < csize \<and> k \<noteq> m \<and> 0 < j \<and> j < csize \<and>
		((j = k + k + 1) \<or> (j = k + k + 2)) \<longrightarrow> 
		  (0 \<le> (compFunc (queue.[k]) (queue.[j])))))"
	      from LeftDef, RightDef, GlobalOrderingPre, LocalOrder, iLB, iUB, 
	      mBounds, LocalOrderingPre, OrderingLem;
	    */
	    //: note ContentBefore: "\<forall> pq. pq..spqueue = old (pq..spqueue)";
	    heapify(m);
	    /*: note ContentAfter: "\<forall> pq. pq..spqueue = old (pq..spqueue)"
	      from ContentAfter, ContentBefore, heapify_Postcond; */
	    /*: note ContentFrame: 
		"\<forall> pq. pq \<in> PriorityQueue \<longrightarrow> pq..spqueue = old (pq..spqueue)"
		from ContentFrame, ContentAfter; */
	}
    }
}
