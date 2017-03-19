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

lemma PriorityQueue_findMax_2: "([|comment ''ArrLength'' (intless 0 PriorityQueue_length);
comment ''Ordering'' (ALL i j. (((0 <= i) & (intless i PriorityQueue_length) & (0 <= j) & (intless j PriorityQueue_length) & ((j = (intplus (intplus i i) 1)) | (j = (intplus (intplus i i) 2)))) --> ((fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue j)) <= (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue i)))));
comment ''Ordering'' (0 <= k_bv113);
comment ''Ordering'' (intless k_bv113 PriorityQueue_length)|] ==>
    comment ''Ordering'' (((fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue k_bv113)) :: int) <= (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState PriorityQueue_queue 0))))"
apply (unfold comment_def)
apply (insert PriorityQueue_findMax_1 [of PriorityQueue_length PriorityQueueElement_key Array_arrayState PriorityQueue_queue "nat k_bv113"])
apply simp
done

lemma test:
 assumes hyp: "ALL (i::nat) (j::nat). 0 <= i & i < qlen & 0 <= j & j < (qlen::nat) & (j = 2 * i + 1 | j = 2 * i + 2) --> queue j <= queue i" 
    (is "ALL i j. ?Local i j")
 shows "ALL (p::nat). p <= n & p < qlen --> (queue p :: int) <= queue 0" 
    (is "ALL p. ?P n p")
proof (induct n)
  -- {* base case *}
  show "ALL p. ?P 0 p" by auto
  -- {* inductive case *}
  fix n
  assume IH: "ALL p. ?P n p"
  show "ALL p. ?P (Suc n) p"
  proof 
    fix p
    show "p <= Suc n & p < qlen --> queue p <= queue 0"
    proof 
      assume pleqn: "p <= Suc n & p < qlen"
      from this have plq: "p < qlen" by simp
      show "queue p <= queue 0"
      proof (cases "p < Suc n")
	assume plsn: "p < Suc n"
        from plsn plq IH show "queue p <= queue 0" by auto
      next -- {* p = Suc n *}
        assume not_p_less_succ: "~ p < Suc n"
	show "queue p <= queue 0"
        proof -
          from not_p_less_succ pleqn have p_is_suc: "p = Suc n" by auto
	  show "?thesis"
	  proof (cases "p mod 2 = 0")
	  assume even: "p mod 2 = 0"
	  show "queue p <= queue 0"
	  proof -
	    from even have even1: "EX q. p = 2 * q" by auto
	    then obtain "q" where pis2q: "p = 2 * q" ..
	    from hyp have o1: "?Local (q - 1) (2 * q)" by auto
            from IH have o2: "?P n (q - 1)" by auto
	    from pis2q plq p_is_suc have o3: "q - 1 < qlen" by arith
	    from pis2q p_is_suc have o4: "q - 1 < n" by arith
	    from o2 o3 o4 have LEQ1: 
	      "queue (q - 1) <= queue 0" by auto
	    
	    from pis2q p_is_suc have o5: "2 * q = 2 * (q - 1) + 2" by arith
	    from o1 o5 pis2q plq have LEQ2:
	      "queue p <= queue (q - 1)" by auto
	    from LEQ1 LEQ2 show ?thesis by simp
	  qed

	  next assume odd: "p mod 2 ~= 0"
	  show "queue p <= queue 0"
	  proof -
	    from odd have odd1: "EX q. p = 2 * q + 1" by arith
	    then obtain "q" where pis2q1: "p = 2 * q + 1" ..
	    from hyp have oo1: "?Local q (2 * q + 1)" by auto
            from IH have oo2: "?P n q" by auto
	    from oo2 pis2q1 p_is_suc plq have LEQ1: 
	      "queue q <= queue 0" by auto	    
	    from oo1 pis2q1 plq have LEQ2:
	      "queue p <= queue q" by auto
	    from LEQ1 LEQ2 show ?thesis by simp
	  qed
	qed
      qed
    qed
  qed
qed
qed

lemma someIntsAreNat:
  "(ALL (x::nat). P x) ==> (ALL (y::int). 0 <= y --> P (nat y))"
apply simp

end
