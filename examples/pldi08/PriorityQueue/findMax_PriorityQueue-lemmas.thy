theory findMax_PriorityQueue_lemmas = Jahob:

lemma PriorityQueue_findMax_1: "([|(intless 0 PriorityQueue_length);
(ALL i j. (((0 <= i) & (intless i PriorityQueue_length) & (0 <= j) & (intless j PriorityQueue_length) & ((j = (intplus (intplus i i) 1)) | (j = (intplus (intplus i i) 2)))) --> ((fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue j)) <= (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue i)))))|] ==>
  (ALL x. (x <= (int n)) & (0 <= x) & (intless x PriorityQueue_length) -->
          ((((fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue x)) :: int) <= 
             (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue 0))))))"
proof -
    assume hyp0: "(intless 0 PriorityQueue_length)" (is ?P0)
    assume hyp1: "(ALL i j. (((0 <= i) & (intless i PriorityQueue_length) & (0 <= j) & (intless j PriorityQueue_length) & 
                              ((j = (intplus (intplus i i) 1)) | (j = (intplus (intplus i i) 2)))) --> 
                             ((fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue j)) <= 
                              (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue i)))))" (is "(ALL i j. ?P1 i j)")
    show goal: "(ALL x. (x <= (int n)) & (0 <= x) & (intless x PriorityQueue_length) -->
                ((fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue x)) <= 
                 (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue 0))))" (is "(ALL x. ?P n x)")
    proof (induct n)
      show "ALL x. ?P 0 x" by auto
      fix n
      assume induct_hyp: "ALL x. ?P n x"
      show "(ALL x. ?P (Suc n) x)"
	proof
	  fix x
	  show "x <= int (Suc n) & 0 <= x & intless x PriorityQueue_length -->
            arrayRead Array_arrayState PriorityQueue_queue x .. PriorityQueueElement_key
            <= arrayRead Array_arrayState PriorityQueue_queue 0 .. PriorityQueueElement_key"
	  proof
	    assume lhs: "x <= int (Suc n) & 0 <= x & intless x PriorityQueue_length"
	    from this have x_lt_len: "intless x PriorityQueue_length" by simp
	    show "arrayRead Array_arrayState PriorityQueue_queue x .. PriorityQueueElement_key
              <= arrayRead Array_arrayState PriorityQueue_queue 0 .. PriorityQueueElement_key"
	    proof (cases "x < int (Suc n)")
	      assume x_lt_suc_n: "x < int (Suc n)"
	      from induct_hyp x_lt_suc_n lhs
	      show "arrayRead Array_arrayState PriorityQueue_queue x .. PriorityQueueElement_key
		<= arrayRead Array_arrayState PriorityQueue_queue 0 .. PriorityQueueElement_key" by auto
	    next
	      assume x_nlt_suc_n: "~ x < int (Suc n)"
	      show "arrayRead Array_arrayState PriorityQueue_queue x .. PriorityQueueElement_key
		<= arrayRead Array_arrayState PriorityQueue_queue 0 .. PriorityQueueElement_key"
	      proof -
		from x_nlt_suc_n lhs have x_is_suc_n: "x = int (Suc n)" by auto
		show "?thesis"
		proof (cases "x mod 2 = 0")
		  assume even: "x mod 2 = 0"
		  show "arrayRead Array_arrayState PriorityQueue_queue x .. PriorityQueueElement_key
		    <= arrayRead Array_arrayState PriorityQueue_queue 0 .. PriorityQueueElement_key"
		  proof -
		    from even have even_ex: "EX q. x = 2 * q" by auto
		    then obtain "q" where x_is_2q: "x = 2 * q" ..
		    from hyp1 have o1: "?P1 (q - 1) (2 * q)" (is "?A1 & ?A2 & ?A3 & ?A4 & ?A5 --> ?A6") by auto
		    from x_is_2q x_is_suc_n have either_or: "?A5" by auto
		    from o1 x_is_2q x_is_suc_n x_lt_len lhs either_or have leq1: "?A6" by auto
		    -- {* This is the inductive portion. *}
		    from induct_hyp have o2: "?P n (q - 1)" by auto
		    from o2 x_is_suc_n x_lt_len x_is_2q 
		    have leq2:" arrayRead Array_arrayState PriorityQueue_queue (q - 1) .. PriorityQueueElement_key
		      <= arrayRead Array_arrayState PriorityQueue_queue 0 .. PriorityQueueElement_key" by auto
		    from leq1 leq2 x_is_2q show "?thesis" by simp
		  qed
		next assume odd: "x mod 2 ~= 0"
		  show "arrayRead Array_arrayState PriorityQueue_queue x .. PriorityQueueElement_key
		    <= arrayRead Array_arrayState PriorityQueue_queue 0 .. PriorityQueueElement_key"
		  proof -
		    from odd have odd_ex: "EX q. x = 2 * q + 1" by arith
		    then obtain "q" where x_is_2q_plus: "x = 2 * q + 1" ..
		    from hyp1 have o1: "?P1 q (2 * q + 1)" by auto
		    from o1 x_is_suc_n x_is_2q_plus x_lt_len
		    have leq1:
		      "arrayRead Array_arrayState PriorityQueue_queue (2 * q + 1) .. PriorityQueueElement_key
		      <= arrayRead Array_arrayState PriorityQueue_queue q .. PriorityQueueElement_key" by auto
		    from induct_hyp have o2: "?P n q" by auto
		    from o2 x_is_suc_n x_is_2q_plus x_lt_len
		    have leq2:
		      "arrayRead Array_arrayState PriorityQueue_queue q .. PriorityQueueElement_key
		      <= arrayRead Array_arrayState PriorityQueue_queue 0 .. PriorityQueueElement_key" by auto
		    from leq1 leq2 x_is_2q_plus show "?thesis" by simp
		  qed
		qed
	      qed
	    qed
	  qed
	qed
      qed
    qed

lemma PriorityQueue_findMax_2: "([|comment ''ArrLength'' (intless 0 (fieldRead PriorityQueue_length this));
comment ''Ordering'' (ALL i j. (((0 <= i) & (intless i (fieldRead PriorityQueue_length this)) & (0 <= j) & (intless j (fieldRead PriorityQueue_length this)) & ((j = (intplus (intplus i i) 1)) | (j = (intplus (intplus i i) 2)))) --> ((fieldRead PriorityQueueElement_key (arrayRead Array_arrayState (fieldRead PriorityQueue_queue this) j)) <= (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState (fieldRead PriorityQueue_queue this) i)))));
comment ''Ordering'' (0 <= k_bv142);
comment ''Ordering'' (intless k_bv142 (fieldRead PriorityQueue_length this))|] ==>
    comment ''Ordering'' ((fieldRead (PriorityQueueElement_key :: (obj \<Rightarrow> int)) (arrayRead Array_arrayState (fieldRead PriorityQueue_queue this) k_bv142)) <= (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState (fieldRead PriorityQueue_queue this) 0))))"
apply (unfold comment_def)
apply simp
apply (insert PriorityQueue_findMax_1 [of "PriorityQueue_length this" PriorityQueueElement_key Array_arrayState "PriorityQueue_queue this" "nat k_bv142"])
apply simp
done

end
