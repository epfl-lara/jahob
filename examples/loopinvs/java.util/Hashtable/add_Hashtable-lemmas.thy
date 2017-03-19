theory add_Hashtable_lemmas = Jahob:

lemma Hashtable_add_18: "([|comment ''FirstInjInvOldFirstInj'' (ALL this. (((this : Object_alloc) & (this : Hashtable) & (fieldRead Hashtable_init this)) --> (ALL i x y. (((y = (fieldRead Node_next x)) & (y ~= null) & (0 <= i) & (intless i (fieldRead Array_length (fieldRead Hashtable_table this)))) --> (y ~= (arrayRead Array_arrayState (fieldRead Hashtable_table this) i))))));
comment ''AllocChange'' (Object_alloc_14 = (Object_alloc Un {tmp_1_19}));
comment ''NewNotHT'' (tmp_1_19 ~: Hashtable);
comment ''NewNotRef'' (ALL x. ((fieldRead (fieldWrite Node_next tmp_1_19 (arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13)) x) ~= tmp_1_19));
comment ''HCBounds'' (0 <= tmp_2_13);
comment ''HCBounds'' (intless tmp_2_13 (fieldRead Array_length (fieldRead Hashtable_table this)));
comment ''OldNotRef'' (ALL ht i. (((fieldRead Hashtable_init ht) & (0 <= i) & (intless i (fieldRead Array_length (fieldRead Hashtable_table ht))) & ((arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13) ~= null)) --> ((arrayRead (arrayWrite Array_arrayState (fieldRead Hashtable_table this) tmp_2_13 tmp_1_19) (fieldRead Hashtable_table ht) i) ~= (arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13))));
comment ''FirstInjInv_NewFirstInj'' (this__10_bv2341 : Object_alloc_14);
comment ''FirstInjInv_NewFirstInj'' (this__10_bv2341 : Hashtable);
comment ''FirstInjInv_NewFirstInj'' (fieldRead Hashtable_init this__10_bv2341);
comment ''FirstInjInv_NewFirstInj'' (y_bv2435 = (fieldRead (fieldWrite Node_next tmp_1_19 (arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13)) x_bv2343));
comment ''FirstInjInv_NewFirstInj'' (y_bv2435 ~= null);
comment ''FirstInjInv_NewFirstInj'' (0 <= i_bv2342);
comment ''FirstInjInv_NewFirstInj'' (intless i_bv2342 (fieldRead Array_length (fieldRead Hashtable_table this__10_bv2341)))|] ==>
    comment ''FirstInjInv_NewFirstInj'' (y_bv2435 ~= (arrayRead (arrayWrite Array_arrayState (fieldRead Hashtable_table this) tmp_2_13 tmp_1_19) (fieldRead Hashtable_table this__10_bv2341) i_bv2342)))"
apply (unfold comment_def)
apply (subgoal_tac "this__10_bv2341 : Object_alloc")
defer
apply force
apply (erule_tac x="this__10_bv2341" in allE)
apply (case_tac "i_bv2342 = tmp_2_13", simp)
apply (case_tac "Hashtable_table this__10_bv2341 = Hashtable_table this")
apply (case_tac "x_bv2343 ~= tmp_1_19", simp)
apply force
apply (erule_tac x="x_bv2343" in allE, simp)
apply (case_tac "x_bv2343 = tmp_1_19", simp)
apply force
apply force
apply (erule_tac x="tmp_1_19" in allE, simp)
apply (case_tac "x_bv2343 = tmp_1_19", simp)
apply (case_tac "Hashtable_table this = Hashtable_table this__10_bv2341", simp)
apply (erule_tac x="this__10_bv2341" in allE, simp)
apply (erule_tac x="tmp_2_13" in allE, simp)
apply (erule_tac x="i_bv2342" in allE, simp)
apply force
apply force
apply (case_tac "x_bv2343 = tmp_1_19", simp)
apply force
done

lemma Hashtable_add_20: "([|comment ''NextInjInvOldNextInj'' (ALL x1 x2 y. (((y ~= null) & (y = (fieldRead Node_next x1)) & (y = (fieldRead Node_next x2))) --> (x1 = x2)));
comment ''OldNotRefByNext'' (ALL x. (((arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13) ~= null) --> ((fieldRead Node_next x) ~= (arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13))));
comment ''NextInjInv_NewNextInj'' (y_bv1897 ~= null);
comment ''NextInjInv_NewNextInj'' (y_bv1897 = (fieldRead (fieldWrite Node_next tmp_1_19 (arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13)) x1_bv1805));
comment ''NextInjInv_NewNextInj'' (y_bv1897 = (fieldRead (fieldWrite Node_next tmp_1_19 (arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13)) x2_bv1806))|] ==>
    comment ''NextInjInv_NewNextInj'' (x1_bv1805 = x2_bv1806))"
apply (unfold comment_def)
apply (erule_tac x="x1_bv1805" in allE, simp)
apply safe
apply (case_tac "x1_bv1805 = tmp_1_19", simp)
apply (erule_tac x="x2_bv1806" in allE, simp)
apply (case_tac "x2_bv1806 = tmp_1_19", simp)
apply force
apply (case_tac "x1_bv1805 = tmp_1_19", simp)
apply safe
apply (case_tac "x2_bv1806 = tmp_1_19", simp)
apply simp
apply (case_tac "x2_bv1806 = tmp_1_19", simp)
apply force
apply force
done

lemma Hashtable_add_19: "([|comment ''ElementInjInvOldElemInj'' (ALL i j h1 h2. (((h1 : Object_alloc) & (h1 : Hashtable) & (fieldRead Hashtable_init h1) & (0 <= i) & (intless i (fieldRead Array_length (fieldRead Hashtable_table h1))) & (h2 : Object_alloc) & (h2 : Hashtable) & (fieldRead Hashtable_init h2) & (0 <= j) & (intless j (fieldRead Array_length (fieldRead Hashtable_table h2))) & ((arrayRead Array_arrayState (fieldRead Hashtable_table h1) i) ~= null) & ((arrayRead Array_arrayState (fieldRead Hashtable_table h1) i) = (arrayRead Array_arrayState (fieldRead Hashtable_table h2) j))) --> ((i = j) & (h1 = h2))));
comment ''AllocChange'' (Object_alloc_14 = (Object_alloc Un {tmp_1_19}));
comment ''NewNotHT'' (tmp_1_19 ~: Hashtable);
comment ''HCBounds'' (0 <= tmp_2_13);
comment ''HCBounds'' (intless tmp_2_13 (fieldRead Array_length (fieldRead Hashtable_table this)));
comment ''NewOldNEq'' (tmp_1_19 ~= (arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13));
comment ''OldNotRef'' (ht_bv2369 : Object_alloc_14);
comment ''OldNotRef'' (ht_bv2369 : Hashtable);
comment ''OldNotRef'' (fieldRead Hashtable_init ht_bv2369);
comment ''OldNotRef'' (0 <= i_bv2459);
comment ''OldNotRef'' (intless i_bv2459 (fieldRead Array_length (fieldRead Hashtable_table ht_bv2369)));
comment ''OldNotRef'' ((arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13) ~= null);
this : Object_alloc; this : Hashtable; (fieldRead Hashtable_init this)|] ==>
    comment ''OldNotRef'' ((arrayRead (arrayWrite Array_arrayState (fieldRead Hashtable_table this) tmp_2_13 tmp_1_19) (fieldRead Hashtable_table ht_bv2369) i_bv2459) ~= (arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13)))"
apply (unfold comment_def)
apply (subgoal_tac "ht_bv2369 : Object_alloc")
defer
apply force
apply (case_tac "ht_bv2369 = this")
apply (erule_tac x="tmp_2_13" in allE)
apply (erule_tac x="i_bv2459" in allE)
apply (erule_tac x="this" in allE)
apply (erule_tac x="ht_bv2369" in allE)
apply simp
apply (case_tac "i_bv2459 = tmp_2_13")
apply force
apply force
apply (erule_tac x="tmp_2_13" in allE)
apply (erule_tac x="i_bv2459" in allE)
apply (erule_tac x="this" in allE)
apply (erule_tac x="ht_bv2369" in allE)
apply simp
apply force
done

lemma Hashtable_add_8: "([|comment ''Hashtable_PrivateInvHashInvProcedurePrecondition'' (ALL this__12. (((this__12 : Object_alloc) & (this__12 : Hashtable)) --> (ALL k. ((0 <= (Hashtable_h k (fieldRead Array_length (fieldRead Hashtable_table this__12)))) & (intless (Hashtable_h k (fieldRead Array_length (fieldRead Hashtable_table this__12))) (fieldRead Array_length (fieldRead Hashtable_table this__12)))))));
comment ''ContentDefOldContentDef'' (ALL this__31. (((this__31 : Object_alloc) & (this__31 : Hashtable) & (fieldRead Hashtable_init this__31)) --> ((fieldRead Hashtable_content this__31) = {p__5. (EX k v. ((p__5 = (k, v)) & ((k, v) : (fieldRead Node_con (arrayRead Array_arrayState (fieldRead Hashtable_table this__31) (Hashtable_h k (fieldRead Array_length (fieldRead Hashtable_table this__31))))))))})));
comment ''AllocChange'' (Object_alloc_14 = (Object_alloc Un {tmp_1_19}));
comment ''NewNotHT'' (tmp_1_19 ~: Hashtable);
comment ''HProp'' (tmp_2_13 = (Hashtable_h k0 (fieldRead Array_length (fieldRead Hashtable_table this))));
comment ''NewNotRefArray'' (ALL ht i. (((ht : Object_alloc) & (ht : Hashtable) & (0 <= i) & (intless i (fieldRead Array_length (fieldRead Hashtable_table ht)))) --> ((arrayRead Array_arrayState (fieldRead Hashtable_table ht) i) ~= tmp_1_19)));
comment ''TableInjInvNewTableInj'' (ALL h1 h2. (((h1 : Object_alloc_14) & (h1 : Hashtable) & (fieldRead Hashtable_init h1) & (h2 : Object_alloc_14) & (h2 : Hashtable) & (fieldRead Hashtable_init h2) & ((fieldRead Hashtable_table h1) = (fieldRead Hashtable_table h2))) --> (h1 = h2)));
comment ''Antecedents'' (this : Object_alloc);
comment ''Antecedents'' (this : Hashtable);
comment ''Antecedents'' (fieldRead Hashtable_init this);
comment ''ContentDef_NewContentDef'' (this__6_bv1224 : Object_alloc_14);
comment ''ContentDef_NewContentDef'' (this__6_bv1224 : Hashtable);
comment ''ContentDef_NewContentDef'' (fieldRead Hashtable_init this__6_bv1224)|] ==>
    comment ''ContentDef_NewContentDef'' ((fieldRead (fieldWrite Hashtable_content this ((fieldRead Hashtable_content this) Un {(k0, v0)})) this__6_bv1224) = {p__5. (EX k v. ((p__5 = (k, v)) & ((k, v) : (fieldRead (fieldWrite Node_con tmp_1_19 ({(k0, v0)} Un (fieldRead Node_con (arrayRead Array_arrayState (fieldRead Hashtable_table this) tmp_2_13)))) (arrayRead (arrayWrite Array_arrayState (fieldRead Hashtable_table this) tmp_2_13 tmp_1_19) (fieldRead Hashtable_table this__6_bv1224) (Hashtable_h k (fieldRead Array_length (fieldRead Hashtable_table this__6_bv1224))))))))}))"
apply (unfold comment_def)
apply (subgoal_tac "this__6_bv1224 : Object_alloc")
defer
apply force
apply (erule_tac x="this__6_bv1224" in allE)
apply (erule_tac x="this__6_bv1224" in allE)
apply (erule_tac x="this__6_bv1224" in allE)
apply (erule_tac x="this__6_bv1224" in allE)
apply simp
apply (case_tac "this__6_bv1224 = this", simp_all)
apply safe
apply simp_all
apply (case_tac "Hashtable_h a (Array_length (Hashtable_table this)) = Hashtable_h k0 (Array_length (Hashtable_table this))")
apply simp_all
apply (case_tac "Hashtable_h a (Array_length (Hashtable_table this)) = Hashtable_h k0 (Array_length (Hashtable_table this))")
apply simp_all
apply (case_tac "Hashtable_h a (Array_length (Hashtable_table this)) = Hashtable_h k0 (Array_length (Hashtable_table this))")
apply simp_all
done

end