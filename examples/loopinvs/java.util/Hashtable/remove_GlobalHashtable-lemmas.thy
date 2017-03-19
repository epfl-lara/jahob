theory remove_GlobalHashtable_lemmas = Jahob:

lemma GlobalHashtable_remove_52: "([|comment ''GlobalHashtable_PrivateInvContentDefInvProcedurePrecondition'' (GlobalHashtable_init --> (GlobalHashtable_content = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead Node_con (arrayRead Array_arrayState GlobalHashtable_table (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)))))))}));
comment ''GlobalHashtable_PrivateInvHashInvProcedurePrecondition'' (GlobalHashtable_init --> (ALL k. ((0 <= (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table))) & (intless (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)) (fieldRead Array_length GlobalHashtable_table)))));
comment ''HProps'' (tmp_1_31 = (GlobalHashtable_h k0 (fieldRead Array_length GlobalHashtable_table)));
comment ''NotFirstAlt'' (ALL k. (current_16 ~= (arrayRead Array_arrayState GlobalHashtable_table (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)))));
comment ''ConLInv'' (ALL n. ((n ~= current_16) --> (((fieldRead (fieldWrite Node_con_19 current_16 {((fieldRead Node_key current_16), (fieldRead Node_value current_16))}) n) = (fieldRead Node_con n)) | ((fieldRead (fieldWrite Node_con_19 current_16 {((fieldRead Node_key current_16), (fieldRead Node_value current_16))}) n) = ((fieldRead Node_con n) \<setminus> {(k0, v0)})))));
comment ''KCurrent'' ((fieldRead Node_key current_16) = k0);
comment ''VCurrent'' ((fieldRead Node_value current_16) = v0);
comment ''FConLemma'' ((fieldRead (fieldWrite Node_con_19 current_16 {((fieldRead Node_key current_16), (fieldRead Node_value current_16))}) (arrayRead Array_arrayState GlobalHashtable_table tmp_1_31)) = ((fieldRead Node_con (arrayRead Array_arrayState GlobalHashtable_table tmp_1_31)) \<setminus> {(k0, v0)}));
comment ''OtherBucketsK'' (ALL k. (((GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)) ~= tmp_1_31) --> (k ~= (fieldRead Node_key current_16))));
comment ''ContentDefInv_FBContentDef'' GlobalHashtable_init|] ==>
    comment ''ContentDefInv_FBContentDef'' ((GlobalHashtable_content \<setminus> {(k0, v0)}) = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead (fieldWrite Node_con_19 current_16 {((fieldRead Node_key current_16), (fieldRead Node_value current_16))}) (arrayRead Array_arrayState GlobalHashtable_table (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)))))))}))"
apply (unfold comment_def)
apply simp
apply safe
apply simp_all
apply (subgoal_tac "Array_arrayState GlobalHashtable_table (GlobalHashtable_h a (Array_length GlobalHashtable_table)) ~= current_16", simp_all)
apply (subgoal_tac "Array_arrayState GlobalHashtable_table (GlobalHashtable_h (Node_key current_16) (Array_length GlobalHashtable_table)) ~= current_16", simp_all)
apply force
apply force
apply force
apply (subgoal_tac "Array_arrayState GlobalHashtable_table (GlobalHashtable_h a (Array_length GlobalHashtable_table)) ~= current_16", simp_all)
apply (subgoal_tac "Array_arrayState GlobalHashtable_table (GlobalHashtable_h (Node_key current_16) (Array_length GlobalHashtable_table)) ~= current_16", simp_all)
apply force
apply force
apply force
apply (subgoal_tac "Array_arrayState GlobalHashtable_table (GlobalHashtable_h a (Array_length GlobalHashtable_table)) ~= current_16", simp_all)
apply (subgoal_tac "Array_arrayState GlobalHashtable_table (GlobalHashtable_h (Node_key current_16) (Array_length GlobalHashtable_table)) ~= current_16", simp_all)
apply force
apply force
apply force
done

lemma GlobalHashtable_remove_10: "([|comment ''GlobalHashtable_PrivateInvContentDefInvProcedurePrecondition'' (GlobalHashtable_init --> (GlobalHashtable_content = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead Node_con (arrayRead Array_arrayState GlobalHashtable_table (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)))))))}));
comment ''GlobalHashtable_PrivateInvHashInvProcedurePrecondition'' (GlobalHashtable_init --> (ALL k. ((0 <= (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table))) & (intless (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)) (fieldRead Array_length GlobalHashtable_table)))));
comment ''GlobalHashtable_PrivateInvElementInjInvProcedurePrecondition'' (GlobalHashtable_init --> (ALL i j. (((0 <= i) & (intless i (fieldRead Array_length GlobalHashtable_table)) & (0 <= j) & (intless j (fieldRead Array_length GlobalHashtable_table)) & ((arrayRead Array_arrayState GlobalHashtable_table i) ~= null) & ((arrayRead Array_arrayState GlobalHashtable_table i) = (arrayRead Array_arrayState GlobalHashtable_table j))) --> (i = j))));
comment ''GlobalHashtable_PrivateInvConDefProcedurePrecondition'' (ALL x. (((x : Node) & (x : Object_alloc) & (x ~= null)) --> (((fieldRead Node_con x) = ({((fieldRead Node_key x), (fieldRead Node_value x))} Un (fieldRead Node_con (fieldRead Node_next x)))) & (ALL v. (((fieldRead Node_key x), v) ~: (fieldRead Node_con (fieldRead Node_next x)))))));
comment ''HProps'' (tmp_1_41 = (GlobalHashtable_h k0 (fieldRead Array_length GlobalHashtable_table)));
comment ''FProps'' ((arrayRead Array_arrayState GlobalHashtable_table tmp_1_41) : Node);
comment ''FProps'' ((arrayRead Array_arrayState GlobalHashtable_table tmp_1_41) : Object_alloc);
comment ''FNonNull'' ((arrayRead Array_arrayState GlobalHashtable_table tmp_1_41) ~= null);
comment ''HCProps'' (0 <= tmp_1_41);
comment ''HCProps'' (intless tmp_1_41 (fieldRead Array_length GlobalHashtable_table));
comment ''Acyclic'' ((fieldRead Node_next (arrayRead Array_arrayState GlobalHashtable_table tmp_1_41)) ~= (arrayRead Array_arrayState GlobalHashtable_table tmp_1_41));
comment ''KFound'' ((fieldRead Node_key (arrayRead Array_arrayState GlobalHashtable_table tmp_1_41)) = k0);
comment ''VFound'' ((fieldRead Node_value (arrayRead Array_arrayState GlobalHashtable_table tmp_1_41)) = v0);
comment ''ContentDefInv_NewContentDef'' GlobalHashtable_init|] ==>
    comment ''ContentDefInv_NewContentDef'' ((GlobalHashtable_content \<setminus> {(k0, v0)}) = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead (fieldWrite Node_con (arrayRead Array_arrayState GlobalHashtable_table tmp_1_41) {((fieldRead Node_key (arrayRead Array_arrayState GlobalHashtable_table tmp_1_41)), (fieldRead Node_value (arrayRead Array_arrayState GlobalHashtable_table tmp_1_41)))}) (arrayRead (arrayWrite Array_arrayState GlobalHashtable_table tmp_1_41 (fieldRead Node_next (arrayRead Array_arrayState GlobalHashtable_table tmp_1_41))) GlobalHashtable_table (GlobalHashtable_h k (fieldRead Array_length GlobalHashtable_table)))))))}))"
apply (unfold comment_def)
apply safe
apply simp
apply (case_tac "GlobalHashtable_h a (Array_length GlobalHashtable_table) = GlobalHashtable_h k0 (Array_length GlobalHashtable_table)", simp_all)
apply (case_tac "a = k0 & b = Node_value (Array_arrayState GlobalHashtable_table (GlobalHashtable_h k0 (Array_length GlobalHashtable_table)))", simp_all)
apply (subgoal_tac "Array_arrayState GlobalHashtable_table (GlobalHashtable_h a (Array_length GlobalHashtable_table)) ~=
               Array_arrayState GlobalHashtable_table (GlobalHashtable_h k0 (Array_length GlobalHashtable_table))", simp_all)
apply (erule_tac x="GlobalHashtable_h k0 (Array_length GlobalHashtable_table)" in allE)
apply (erule_tac x="GlobalHashtable_h a (Array_length GlobalHashtable_table)" in allE, simp_all)
apply force
apply (case_tac "GlobalHashtable_h k (Array_length GlobalHashtable_table) = GlobalHashtable_h k0 (Array_length GlobalHashtable_table)", simp_all)
apply force
apply (subgoal_tac "Array_arrayState GlobalHashtable_table (GlobalHashtable_h k (Array_length GlobalHashtable_table)) ~=
                           Array_arrayState GlobalHashtable_table (GlobalHashtable_h k0 (Array_length GlobalHashtable_table))", simp_all)
apply force
apply (erule_tac x="GlobalHashtable_h k0 (Array_length GlobalHashtable_table)" in allE)
apply (erule_tac x="GlobalHashtable_h a (Array_length GlobalHashtable_table)" in allE, simp_all)
apply force
done

lemma GlobalHashtable_remove_45: "([|comment ''UpdatedConDef'' (ALL n. (((n : Node) & (n : Object_alloc_34) & (n ~= null) & (n ~= prev_20)) --> (((fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) n) = ({((fieldRead Node_key n), (fieldRead Node_value n))} Un (fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_20 (fieldRead Node_next current_18)) current_18 null) n)))) & (ALL v. (((fieldRead Node_key n), v) ~: (fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_20 (fieldRead Node_next current_18)) current_18 null) n)))))));
comment ''PrevConDef'' ((fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) prev_20) = ({((fieldRead Node_key prev_20), (fieldRead Node_value prev_20))} Un (fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_20 (fieldRead Node_next current_18)) current_18 null) prev_20))));
comment ''PrevConDef'' (ALL v. (((fieldRead Node_key prev_20), v) ~: (fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_20 (fieldRead Node_next current_18)) current_18 null) prev_20))));
comment ''ConDef_NewConDef'' (x_bv4254 : Node);
comment ''ConDef_NewConDef'' (x_bv4254 : Object_alloc_34);
comment ''ConDef_NewConDef'' (x_bv4254 ~= null)|] ==>
    comment ''ConDef_NewConDef'' (((fieldRead Node_key x_bv4254), v_bv4357) ~: (fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_20 (fieldRead Node_next current_18)) current_18 null) x_bv4254))))"
apply (unfold comment_def)
apply (case_tac "x_bv4254 = prev_20")
apply simp
apply force
done

lemma GlobalHashtable_remove_40: "([|comment ''NullNotCurrent'' (null ~= current_15);
comment ''NextOfNull'' ((fieldRead Node_next null) = null);
comment ''PrevNotCurr'' (prev_17 ~= current_15);
comment ''CurrNextNotCurr'' ((fieldRead Node_next current_15) ~= current_15);
comment ''KeyNotInRest'' ((k0, v0) ~: (fieldRead Node_con (fieldRead Node_next current_15)));
comment ''PrevNotKey'' ((fieldRead Node_key prev_17) ~= k0);
comment ''OldCurrConDef'' ((fieldRead Node_con current_15) = ({(k0, v0)} Un (fieldRead Node_con (fieldRead Node_next current_15))));
comment ''OldPrevConDef'' ((fieldRead Node_con prev_17) = ({((fieldRead Node_key prev_17), (fieldRead Node_value prev_17))} Un (fieldRead Node_con current_15)));
comment ''PrevConUpdate'' ((fieldRead (fieldWrite Node_con_18 current_15 {((fieldRead Node_key current_15), (fieldRead Node_value current_15))}) prev_17) = ((fieldRead Node_con prev_17) \<setminus> {(k0, v0)}));
comment ''ConEitherOr'' (((fieldRead (fieldWrite Node_con_18 current_15 {((fieldRead Node_key current_15), (fieldRead Node_value current_15))}) (fieldRead Node_next current_15)) = (fieldRead Node_con (fieldRead Node_next current_15))) | ((fieldRead (fieldWrite Node_con_18 current_15 {((fieldRead Node_key current_15), (fieldRead Node_value current_15))}) (fieldRead Node_next current_15)) = ((fieldRead Node_con (fieldRead Node_next current_15)) \<setminus> {(k0, v0)})))|] ==>
    comment ''PrevConADef'' ((fieldRead (fieldWrite Node_con_18 current_15 {((fieldRead Node_key current_15), (fieldRead Node_value current_15))}) prev_17) = ({((fieldRead Node_key prev_17), (fieldRead Node_value prev_17))} Un (fieldRead (fieldWrite Node_con_18 current_15 {((fieldRead Node_key current_15), (fieldRead Node_value current_15))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_17 (fieldRead Node_next current_15)) current_15 null) prev_17)))))"
apply (unfold comment_def)
apply simp
apply force
done

lemma GlobalHashtable_remove_44: "([|comment ''UpdatedConDef'' (ALL n. (((n : Node) & (n : Object_alloc_34) & (n ~= null) & (n ~= prev_20)) --> (((fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) n) = ({((fieldRead Node_key n), (fieldRead Node_value n))} Un (fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_20 (fieldRead Node_next current_18)) current_18 null) n)))) & (ALL v. (((fieldRead Node_key n), v) ~: (fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_20 (fieldRead Node_next current_18)) current_18 null) n)))))));
comment ''PrevConDef'' ((fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) prev_20) = ({((fieldRead Node_key prev_20), (fieldRead Node_value prev_20))} Un (fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_20 (fieldRead Node_next current_18)) current_18 null) prev_20))));
comment ''PrevConDef'' (ALL v. (((fieldRead Node_key prev_20), v) ~: (fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_20 (fieldRead Node_next current_18)) current_18 null) prev_20))));
comment ''ConDef_NewConDef'' (x_bv4254 : Node);
comment ''ConDef_NewConDef'' (x_bv4254 : Object_alloc_34);
comment ''ConDef_NewConDef'' (x_bv4254 ~= null)|] ==>
    comment ''ConDef_NewConDef'' ((fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) x_bv4254) = ({((fieldRead Node_key x_bv4254), (fieldRead Node_value x_bv4254))} Un (fieldRead (fieldWrite Node_con_21 current_18 {((fieldRead Node_key current_18), (fieldRead Node_value current_18))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_20 (fieldRead Node_next current_18)) current_18 null) x_bv4254)))))"
apply (unfold comment_def)
apply (case_tac "x_bv4254 = prev_20")
apply simp
apply force
done

end
