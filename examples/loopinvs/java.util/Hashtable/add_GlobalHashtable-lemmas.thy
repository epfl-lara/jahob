theory add_GlobalHashtable_lemmas = Jahob:

lemma GlobalHashtable_add_6: "([|comment ''GlobalHashtable_PrivateInvContentDefInvProcedurePrecondition'' (GlobalHashtable_init --> (GlobalHashtable_content = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead Node_con (arrayRead Array_arrayState GlobalHashtable_table (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)))))))}));
comment ''GlobalHashtable_PrivateInvHashInvProcedurePrecondition'' (GlobalHashtable_init --> (ALL k. ((0 <= (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table))) & (intless (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)) (fieldRead Array_length GlobalHashtable_table)))));
comment ''HProp'' (tmp_2_11 = (GlobalHashtable_h k0 (fieldRead Array_length GlobalHashtable_table)));
comment ''NewNotRefArray'' (ALL i. (((0 <= i) & (intless i (fieldRead Array_length GlobalHashtable_table))) --> ((arrayRead Array_arrayState GlobalHashtable_table i) ~= tmp_1_17)));
comment ''ContentDefInv_NewContentDef'' GlobalHashtable_init|] ==>
    comment ''ContentDefInv_NewContentDef'' ((GlobalHashtable_content Un {(k0, v0)}) = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead (fieldWrite Node_con tmp_1_17 ({(k0, v0)} Un (fieldRead Node_con (arrayRead Array_arrayState GlobalHashtable_table tmp_2_11)))) (arrayRead (arrayWrite Array_arrayState GlobalHashtable_table tmp_2_11 tmp_1_17) GlobalHashtable_table (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)))))))}))"
apply (unfold comment_def)
apply simp
apply safe
apply simp
apply (case_tac "GlobalHashtable_h a (Array_length GlobalHashtable_table) = GlobalHashtable_h k0 (Array_length GlobalHashtable_table)", simp_all)
apply (case_tac "GlobalHashtable_h a (Array_length GlobalHashtable_table) = GlobalHashtable_h k0 (Array_length GlobalHashtable_table)", simp_all)
apply (case_tac "GlobalHashtable_h a (Array_length GlobalHashtable_table) = GlobalHashtable_h k0 (Array_length GlobalHashtable_table)", simp_all)
done

end
