theory peek_PriorityQueue_lemmas = Jahob:

lemma PriorityQueue_peek_induct:
  "\<lbrakk>(\<forall> x. Comparable_compFunc x x = 0);
    (\<forall> x y z. 0 \<le> Comparable_compFunc x y \<and> 0 \<le> Comparable_compFunc y z \<longrightarrow> 0 \<le> Comparable_compFunc x z);
    (intless 0 (PriorityQueue_csize this)); 
  (\<forall> i j. 0 \<le> i \<and> i < PriorityQueue_csize this \<and> 0 \<le> j \<and> j < PriorityQueue_csize this \<and> (j = 2 * i + 1 \<or> j = 2 * i + 2) \<longrightarrow> 0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) i) (Array_arrayState (PriorityQueue_queue this) j))\<rbrakk> \<Longrightarrow> 
  (\<forall> x. (x \<le> int n) \<and> 0 \<le> x \<and> x < PriorityQueue_csize this \<longrightarrow> 
  (0::int) \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0) (Array_arrayState (PriorityQueue_queue this) x))"
proof -
  assume reflexive: "\<forall> x. Comparable_compFunc x x = 0"
  assume transitive: "\<forall> x y z. 0 \<le> Comparable_compFunc x y \<and> 0 \<le> Comparable_compFunc y z \<longrightarrow> 
    0 \<le> Comparable_compFunc x z"
  assume csize_gt_zero: "intless 0 (PriorityQueue_csize this)"
  assume local_ordering: "\<forall>i j. 0 \<le> i \<and> i < PriorityQueue_csize this \<and>
    0 \<le> j \<and> j < PriorityQueue_csize this \<and> (j = 2 * i + 1 \<or> j = 2 * i + 2) \<longrightarrow>
    0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) i)
                            (Array_arrayState (PriorityQueue_queue this) j)"
  (is "(\<forall> i j. ?ordered i j)")
  show goal: "\<forall> x. x \<le> int n \<and> 0 \<le> x \<and> x < PriorityQueue_csize this \<longrightarrow>
    0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
                            (Array_arrayState (PriorityQueue_queue this) x)"
    (is "(\<forall> x. ?minimum n x)")
  proof (induct n)
    from reflexive show "\<forall> x. ?minimum 0 x" by auto
    fix n
    assume induct_hyp: "\<forall>x. x \<le> int n \<and> 0 \<le> x \<and> x < PriorityQueue_csize this \<longrightarrow>
      0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
                              (Array_arrayState (PriorityQueue_queue this) x)"
    show induct_goal: "\<forall>x. x \<le> int (Suc n) \<and> 0 \<le> x \<and> x < PriorityQueue_csize this \<longrightarrow>
      0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
                              (Array_arrayState (PriorityQueue_queue this) x)"
    proof
      fix x
      show "x \<le> int (Suc n) \<and> 0 \<le> x \<and> x < PriorityQueue_csize this \<longrightarrow>
        0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
                                (Array_arrayState (PriorityQueue_queue this) x)"
      proof
	assume lhs: "x \<le> int (Suc n) \<and> 0 \<le> x \<and> x < PriorityQueue_csize this"
	from this have x_lt_size: "x < PriorityQueue_csize this" by simp
	show "0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
	                              (Array_arrayState (PriorityQueue_queue this) x)"
	proof (cases "x < int (Suc n)")
	  assume x_lt_suc_n: "x < int (Suc n)"
	  from induct_hyp x_lt_suc_n lhs
	  show ?thesis by auto
	next
	  assume x_nlt_suc_n: "\<not> x < int (Suc n)"
	  show ?thesis
	  proof -
	    from x_nlt_suc_n lhs have x_is_suc_n: "x = int (Suc n)" by auto
	    show ?thesis
	    proof (cases "x mod 2 = 0")
	      assume even: "x mod 2 = 0"
	      show ?thesis
	      proof -
		from even have even_ex: "\<exists> q. x = 2 * q" by auto
		then obtain "q" where x_is_2q: "x = 2 * q" ..
		from local_ordering 
		have q_ordering: "?ordered (q - 1) (2 * q)" (is "?lb1 \<and> ?ub1 \<and> ?lb2 \<and> ?ub2 \<and> ?rel \<longrightarrow> ?conc") by auto
		from x_is_2q x_is_suc_n have either_or: "?rel" by auto
		from q_ordering x_is_2q x_is_suc_n x_lt_size lhs either_or
		have leq1: "?conc" by auto
		from induct_hyp have q_minimum: "?minimum n (q - 1)" by auto
		from q_minimum x_is_suc_n x_lt_size x_is_2q
		have leq2: "0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
		                                    (Array_arrayState (PriorityQueue_queue this) (q - 1))" by auto
		from transitive have inst_trans:
		  "0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
		                           (Array_arrayState (PriorityQueue_queue this) (q - 1)) \<and> 
		   0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) (q - 1))
		                           (Array_arrayState (PriorityQueue_queue this) (2 * q)) \<longrightarrow>
		  0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
		                          (Array_arrayState (PriorityQueue_queue this) (2 * q))"
		  apply (erule_tac x="(Array_arrayState (PriorityQueue_queue this) 0)" in allE)
		  apply (erule_tac x="(Array_arrayState (PriorityQueue_queue this) (q - 1))" in allE)
		  apply (erule_tac x="(Array_arrayState (PriorityQueue_queue this) (2 * q))" in allE)
		  apply simp
		  done
		from leq1 leq2 x_is_2q inst_trans show "?thesis" by auto
	      qed
	    next assume odd: "x mod 2 \<noteq> 0"
	      show ?thesis
		proof -
		  from odd have odd_ex: "\<exists> q. x = 2 * q + 1" by arith
		  then obtain "q" where x_is_2q_plus: "x = 2 * q + 1" ..
		  from local_ordering 
		  have q_ordering: "?ordered q (2 * q + 1)" (is "?lb1 \<and> ?ub1 \<and> ?lb2 \<and> ?ub2 \<and> ?rel \<longrightarrow> ?conc") by auto
		  from x_is_2q_plus x_is_suc_n have either_or: "?rel" by auto
		  from q_ordering x_is_2q_plus x_is_suc_n x_lt_size lhs either_or
		  have leq1: "?conc" by auto
		  from induct_hyp have q_minimum: "?minimum n q" by auto
		  from q_minimum x_is_suc_n x_lt_size x_is_2q_plus
		  have leq2: "0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
		                                      (Array_arrayState (PriorityQueue_queue this) q)" by auto
		  from transitive have inst_trans:
		    "0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
		                             (Array_arrayState (PriorityQueue_queue this) q) \<and>
		     0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) q)
		                             (Array_arrayState (PriorityQueue_queue this) (2 * q + 1)) \<longrightarrow>
		     0 \<le> Comparable_compFunc (Array_arrayState (PriorityQueue_queue this) 0)
		                             (Array_arrayState (PriorityQueue_queue this) (2 * q + 1))"
		    apply (erule_tac x="(Array_arrayState (PriorityQueue_queue this) 0)" in allE)
		    apply (erule_tac x="(Array_arrayState (PriorityQueue_queue this) q)" in allE)
		    apply (erule_tac x="(Array_arrayState (PriorityQueue_queue this) (2 * q + 1))" in allE)
		    apply simp
		    done
		  from leq1 leq2 x_is_2q_plus inst_trans show "?thesis" by auto
		qed
	      qed
	    qed
	  qed
	qed
      qed
    qed
  qed

lemma PriorityQueue_peek_5: "([|(ALL x. Comparable_compFunc x x = 0);
(\<forall> x y z. 0 \<le> Comparable_compFunc x y \<and> 0 \<le> Comparable_compFunc y z \<longrightarrow> 0 \<le> Comparable_compFunc x z);
(comment ''ArrLength'' (intless 0 (fieldRead PriorityQueue_csize this)));
(comment ''Ordering'' (ALL i j. (((0 <= i) & (intless i (fieldRead PriorityQueue_csize this)) & (0 <= j) & (intless j (fieldRead PriorityQueue_csize this)) & ((j = (intplus (intplus i i) 1)) | (j = (intplus (intplus i i) 2)))) --> (0 <= (Comparable_compFunc (arrayRead Array_arrayState (fieldRead PriorityQueue_queue this) i) (arrayRead Array_arrayState (fieldRead PriorityQueue_queue this) j))))));
(comment ''Ordering'' (0 <= k_121));
(comment ''Ordering'' (intless k_121 (fieldRead PriorityQueue_csize this)))|] ==>
    (comment ''Ordering'' ((0::int) <= (Comparable_compFunc (arrayRead Array_arrayState (fieldRead PriorityQueue_queue this) 0) (arrayRead Array_arrayState (fieldRead PriorityQueue_queue this) k_121)))))"
apply (unfold comment_def)
proof -
  assume reflexive: "\<forall>x. Comparable_compFunc x x = 0"
  assume transitive: "\<forall>x y z.
        0 \<le> Comparable_compFunc x y \<and> 0 \<le> Comparable_compFunc y z \<longrightarrow>
        0 \<le> Comparable_compFunc x z"
  assume csize: "intless 0 (this .. PriorityQueue_csize)"
  assume local_ordering: "\<forall>i j. 0 \<le> i \<and>
           intless i (this .. PriorityQueue_csize) \<and>
           0 \<le> j \<and>
           intless j (this .. PriorityQueue_csize) \<and>
           (j = intplus (intplus i i) 1 \<or> j = intplus (intplus i i) 2) \<longrightarrow>
           0 \<le> Comparable_compFunc
                (arrayRead Array_arrayState (this .. PriorityQueue_queue) i)
                (arrayRead Array_arrayState (this .. PriorityQueue_queue)
                  j)"
  assume klb: "0 \<le> k_121"
  assume kub: "intless k_121 (this .. PriorityQueue_csize)"
  show goal: "0 \<le> Comparable_compFunc
            (arrayRead Array_arrayState (this .. PriorityQueue_queue) 0)
            (arrayRead Array_arrayState (this .. PriorityQueue_queue) k_121)"
  proof -
    from PriorityQueue_peek_induct [of Comparable_compFunc PriorityQueue_csize this Array_arrayState PriorityQueue_queue "nat k_121"]
    have induct_lemma: "\<lbrakk>\<forall>x. Comparable_compFunc x x = 0;
   \<forall>x y z.
      0 \<le> Comparable_compFunc x y \<and> 0 \<le> Comparable_compFunc y z \<longrightarrow>
      0 \<le> Comparable_compFunc x z;
   intless 0 (PriorityQueue_csize this);
   \<forall>i j. 0 \<le> i \<and>
         i < PriorityQueue_csize this \<and>
         0 \<le> j \<and>
         j < PriorityQueue_csize this \<and> (j = 2 * i + 1 \<or> j = 2 * i + 2) \<longrightarrow>
         0 \<le> Comparable_compFunc
              (Array_arrayState (PriorityQueue_queue this) i)
              (Array_arrayState (PriorityQueue_queue this) j)\<rbrakk>
  \<Longrightarrow> \<forall>x. x \<le> int (nat k_121) \<and> 0 \<le> x \<and> x < PriorityQueue_csize this \<longrightarrow>
         0 \<le> Comparable_compFunc
              (Array_arrayState (PriorityQueue_queue this) 0)
              (Array_arrayState (PriorityQueue_queue this) x)" (is "\<lbrakk> ?A1; ?A2; ?A3; ?A4 \<rbrakk> \<Longrightarrow> ?G") by assumption
    from induct_lemma
    have induct1: "\<lbrakk> ?A1; ?A2; ?A3 \<rbrakk> \<Longrightarrow> (?A4 \<longrightarrow> ?G)" by (rule impI)
    from induct1
    have induct2: "\<lbrakk> ?A1; ?A2 \<rbrakk> \<Longrightarrow> (?A3 \<longrightarrow> (?A4 \<longrightarrow> ?G))" by (rule impI)
    from induct2
    have induct3: "\<lbrakk> ?A1 \<rbrakk> \<Longrightarrow> (?A2 \<longrightarrow> (?A3 \<longrightarrow> (?A4 \<longrightarrow> ?G)))" by (rule impI)
    from induct3
    have induct4: "(?A1 \<longrightarrow> (?A2 \<longrightarrow> (?A3 \<longrightarrow> (?A4 \<longrightarrow> ?G))))" by (rule impI)
    from induct4 reflexive
    have induct5: "(?A2 \<longrightarrow> (?A3 \<longrightarrow> (?A4 \<longrightarrow> ?G)))" by (rule mp)
    from induct5 transitive
    have induct6: "(?A3 \<longrightarrow> (?A4 \<longrightarrow> ?G))" by (rule mp)
    from induct6 csize local_ordering
    have induct7: "?G" by auto
    from induct7
    have induct8: "k_121 \<le> int (nat k_121) \<and> 0 \<le> k_121 \<and> k_121 < PriorityQueue_csize this \<longrightarrow> 
      0 \<le> Comparable_compFunc
           (Array_arrayState (PriorityQueue_queue this) 0)
           (Array_arrayState (PriorityQueue_queue this) k_121)" by (rule allE)
    have assum1: "k_121 \<le> int (nat k_121)" by auto
    from assum1 klb kub induct8
      show ?thesis by auto
  qed
qed

end
