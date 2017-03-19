theory add_Hashtable_lemmas = SV:

lemma Hashtable_add_7: "([|comment ''Hashtable_PrivateInvContentDefInvProcedurePrecondition'' (Hashtable_init --> (Hashtable_content = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead Node_con (arrayRead Array_arrayState Hashtable_table (Hashtable_h k (fieldRead Array_length Hashtable_table)))))))}));
comment ''Hashtable_PrivateInvHashInvProcedurePrecondition'' (Hashtable_init --> (ALL k. ((0 <= (Hashtable_h k (fieldRead Array_length Hashtable_table))) & (intless (Hashtable_h k (fieldRead Array_length Hashtable_table)) (fieldRead Array_length Hashtable_table)))));
comment ''ContentDefInvHashtable.compute_hash_Postcondition'' (Hashtable_init --> (Hashtable_content = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead Node_con (arrayRead Array_arrayState Hashtable_table (Hashtable_h k (fieldRead Array_length Hashtable_table)))))))}));
comment ''HashInvHashtable.compute_hash_Postcondition'' (Hashtable_init --> (ALL k. ((0 <= (Hashtable_h k (fieldRead Array_length Hashtable_table))) & (intless (Hashtable_h k (fieldRead Array_length Hashtable_table)) (fieldRead Array_length Hashtable_table)))));
comment ''HProp'' (tmp_1_15 = (Hashtable_h k0 (fieldRead Array_length Hashtable_table)));
comment ''NewNotRefArray'' (ALL i. (((0 <= i) & (intless i (fieldRead Array_length Hashtable_table))) --> ((arrayRead Array_arrayState Hashtable_table i) ~= tmp_2_13)));
comment ''ContentDefInv_NewContentDef'' Hashtable_init|] ==>
    comment ''ContentDefInv_NewContentDef'' ((Hashtable_content Un {(k0, v0)}) = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead (fieldWrite Node_con tmp_2_13 ({(k0, v0)} Un (fieldRead Node_con (arrayRead Array_arrayState Hashtable_table tmp_1_15)))) (arrayRead (arrayWrite Array_arrayState Hashtable_table tmp_1_15 tmp_2_13) Hashtable_table (Hashtable_h k (fieldRead Array_length Hashtable_table)))))))}))"
apply (unfold comment_def)
apply simp
apply safe
apply simp_all
apply (case_tac "Hashtable_h a (Array_length Hashtable_table) =
  Hashtable_h k0 (Array_length Hashtable_table)", simp_all)
apply (case_tac "Hashtable_h a (Array_length Hashtable_table) =
  Hashtable_h k0 (Array_length Hashtable_table)", simp_all)
apply (case_tac "Hashtable_h a (Array_length Hashtable_table) =
  Hashtable_h k0 (Array_length Hashtable_table)", simp_all)
done

end
