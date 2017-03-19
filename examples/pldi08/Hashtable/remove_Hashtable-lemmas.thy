theory remove_Hashtable_lemmas = SV:

lemma Hashtable_remove_84: "([|comment ''Hashtable_PrivateInvContentDefInvProcedurePrecondition'' (Hashtable_init --> (Hashtable_content = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead Node_con (arrayRead Array_arrayState Hashtable_table (Hashtable_h k (fieldRead Array_length Hashtable_table)))))))}));
comment ''Hashtable_PrivateInvHashInvProcedurePrecondition'' (Hashtable_init --> (ALL k. ((0 <= (Hashtable_h k (fieldRead Array_length Hashtable_table))) & (intless (Hashtable_h k (fieldRead Array_length Hashtable_table)) (fieldRead Array_length Hashtable_table)))));
comment ''ContentDefInvHashtable.compute_hash_Postcondition'' (Hashtable_init --> (Hashtable_content = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead Node_con (arrayRead Array_arrayState Hashtable_table (Hashtable_h k (fieldRead Array_length Hashtable_table)))))))}));
comment ''HashInvHashtable.compute_hash_Postcondition'' (Hashtable_init --> (ALL k. ((0 <= (Hashtable_h k (fieldRead Array_length Hashtable_table))) & (intless (Hashtable_h k (fieldRead Array_length Hashtable_table)) (fieldRead Array_length Hashtable_table)))));
comment ''HProps'' (tmp_1_41 = (Hashtable_h k0 (fieldRead Array_length Hashtable_table)));
comment ''NotFirstAlt'' (ALL k. (current_26 ~= (arrayRead Array_arrayState Hashtable_table (Hashtable_h k (fieldRead Array_length Hashtable_table)))));
comment ''ConLInv'' (ALL n. ((n ~= current_26) --> (((fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) n) = (fieldRead Node_con n)) | ((fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) n) = ((fieldRead Node_con n) \<setminus> {(k0, v0_44)})))));
comment ''KCurrent'' ((fieldRead Node_key current_26) = k0);
comment ''VCurrent'' ((fieldRead Node_value current_26) = v0_44);
comment ''FConLemma'' ((fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (arrayRead Array_arrayState Hashtable_table tmp_1_41)) = ((fieldRead Node_con (arrayRead Array_arrayState Hashtable_table tmp_1_41)) \<setminus> {(k0, v0_44)}));
comment ''OtherBucketsK'' (ALL k. (((Hashtable_h k (fieldRead Array_length Hashtable_table)) ~= tmp_1_41) --> (k ~= (fieldRead Node_key current_26))));
comment ''ContentDefInv_FBContentDef'' Hashtable_init|] ==>
    comment ''ContentDefInv_FBContentDef'' ((Hashtable_content \<setminus> {(k0, v0_44)}) = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (arrayRead Array_arrayState Hashtable_table (Hashtable_h k (fieldRead Array_length Hashtable_table)))))))}))"
apply (unfold comment_def)
apply simp
apply safe
apply simp_all
apply (subgoal_tac "Array_arrayState Hashtable_table 
  (Hashtable_h (Node_key current_26) (Array_length Hashtable_table)) ~= current_26", simp_all)
apply (subgoal_tac "Array_arrayState Hashtable_table 
  (Hashtable_h a (Array_length Hashtable_table)) ~= current_26", simp_all)
apply force
apply force
apply force
apply (subgoal_tac "Array_arrayState Hashtable_table 
  (Hashtable_h (Node_key current_26) (Array_length Hashtable_table)) ~= current_26", simp_all)
apply (subgoal_tac "Array_arrayState Hashtable_table 
  (Hashtable_h a (Array_length Hashtable_table)) ~= current_26", simp_all)
apply force
apply force
apply force
apply (subgoal_tac "Array_arrayState Hashtable_table 
  (Hashtable_h (Node_key current_26) (Array_length Hashtable_table)) ~= current_26", simp_all)
apply (subgoal_tac "Array_arrayState Hashtable_table 
  (Hashtable_h a (Array_length Hashtable_table)) ~= current_26", simp_all)
apply force
apply force
apply force
done

lemma Hashtable_removeArray_arrayState Hashtable_table
                   (Hashtable_h (Node_key current_26) (Array_length Hashtable_table)) =
                  current_26_77: "([|comment ''UpdatedConDef'' (ALL n. (((n : Node) & (n : Object_alloc_42) & (n ~= null) & (n ~= prev_28)) --> (((fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) n) = ({((fieldRead Node_key n), (fieldRead Node_value n))} Un (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_28 (fieldRead Node_next current_26)) current_26 null) n)))) & (ALL v. (((fieldRead Node_key n), v) ~: (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_28 (fieldRead Node_next current_26)) current_26 null) n)))))));
comment ''PrevConDef'' ((fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) prev_28) = ({((fieldRead Node_key prev_28), (fieldRead Node_value prev_28))} Un (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_28 (fieldRead Node_next current_26)) current_26 null) prev_28))));
comment ''PrevConDef'' (ALL v. (((fieldRead Node_key prev_28), v) ~: (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_28 (fieldRead Node_next current_26)) current_26 null) prev_28))));
comment ''ConDef_NewConDef'' (x_bv4618 : Node);
comment ''ConDef_NewConDef'' (x_bv4618 : Object_alloc_42);
comment ''ConDef_NewConDef'' (x_bv4618 ~= null)|] ==>
    comment ''ConDef_NewConDef'' (((fieldRead Node_key x_bv4618), v_bv4744) ~: (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_28 (fieldRead Node_next current_26)) current_26 null) x_bv4618))))"
apply (unfold comment_def)
apply (case_tac "x_bv4618 = prev_28", simp_all)
done

lemma Hashtable_remove_76: "([|comment ''UpdatedConDef'' (ALL n. (((n : Node) & (n : Object_alloc_42) & (n ~= null) & (n ~= prev_28)) --> (((fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) n) = ({((fieldRead Node_key n), (fieldRead Node_value n))} Un (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_28 (fieldRead Node_next current_26)) current_26 null) n)))) & (ALL v. (((fieldRead Node_key n), v) ~: (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_28 (fieldRead Node_next current_26)) current_26 null) n)))))));
comment ''PrevConDef'' ((fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) prev_28) = ({((fieldRead Node_key prev_28), (fieldRead Node_value prev_28))} Un (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_28 (fieldRead Node_next current_26)) current_26 null) prev_28))));
comment ''PrevConDef'' (ALL v. (((fieldRead Node_key prev_28), v) ~: (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_28 (fieldRead Node_next current_26)) current_26 null) prev_28))));
comment ''ConDef_NewConDef'' (x_bv4618 : Node);
comment ''ConDef_NewConDef'' (x_bv4618 : Object_alloc_42);
comment ''ConDef_NewConDef'' (x_bv4618 ~= null)|] ==>
    comment ''ConDef_NewConDef'' ((fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) x_bv4618) = ({((fieldRead Node_key x_bv4618), (fieldRead Node_value x_bv4618))} Un (fieldRead (fieldWrite Node_con_29 current_26 {((fieldRead Node_key current_26), (fieldRead Node_value current_26))}) (fieldRead (fieldWrite (fieldWrite Node_next prev_28 (fieldRead Node_next current_26)) current_26 null) x_bv4618)))))"
apply (unfold comment_def)
apply (case_tac "x_bv4618 = prev_28", simp_all)
done

lemma Hashtable_remove_10: "([|comment ''Hashtable_PrivateInvContentDefInvProcedurePrecondition'' (Hashtable_init --> (Hashtable_content = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead Node_con (arrayRead Array_arrayState Hashtable_table (Hashtable_h k (fieldRead Array_length Hashtable_table)))))))}));
comment ''Hashtable_PrivateInvHashInvProcedurePrecondition'' (Hashtable_init --> (ALL k. ((0 <= (Hashtable_h k (fieldRead Array_length Hashtable_table))) & (intless (Hashtable_h k (fieldRead Array_length Hashtable_table)) (fieldRead Array_length Hashtable_table)))));
comment ''Hashtable_PrivateInvElementInjInvProcedurePrecondition'' (Hashtable_init --> (ALL i j. (((0 <= i) & (intless i (fieldRead Array_length Hashtable_table)) & (0 <= j) & (intless j (fieldRead Array_length Hashtable_table)) & ((arrayRead Array_arrayState Hashtable_table i) ~= null) & ((arrayRead Array_arrayState Hashtable_table i) = (arrayRead Array_arrayState Hashtable_table j))) --> (i = j))));
comment ''Hashtable_PrivateInvConDefProcedurePrecondition'' (ALL x. (((x : Node) & (x : Object_alloc) & (x ~= null)) --> (((fieldRead Node_con x) = ({((fieldRead Node_key x), (fieldRead Node_value x))} Un (fieldRead Node_con (fieldRead Node_next x)))) & (ALL v. (((fieldRead Node_key x), v) ~: (fieldRead Node_con (fieldRead Node_next x)))))));
comment ''ContentDefInvHashtable.compute_hash_Postcondition'' (Hashtable_init --> (Hashtable_content = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead Node_con (arrayRead Array_arrayState Hashtable_table (Hashtable_h k (fieldRead Array_length Hashtable_table)))))))}));
comment ''HashInvHashtable.compute_hash_Postcondition'' (Hashtable_init --> (ALL k. ((0 <= (Hashtable_h k (fieldRead Array_length Hashtable_table))) & (intless (Hashtable_h k (fieldRead Array_length Hashtable_table)) (fieldRead Array_length Hashtable_table)))));
comment ''ElementInjInvHashtable.compute_hash_Postcondition'' (Hashtable_init --> (ALL i j. (((0 <= i) & (intless i (fieldRead Array_length Hashtable_table)) & (0 <= j) & (intless j (fieldRead Array_length Hashtable_table)) & ((arrayRead Array_arrayState Hashtable_table i) ~= null) & ((arrayRead Array_arrayState Hashtable_table i) = (arrayRead Array_arrayState Hashtable_table j))) --> (i = j))));
comment ''ConDefHashtable.compute_hash_Postcondition'' (ALL x. (((x : Node) & (x : Object_alloc_42) & (x ~= null)) --> (((fieldRead Node_con x) = ({((fieldRead Node_key x), (fieldRead Node_value x))} Un (fieldRead Node_con (fieldRead Node_next x)))) & (ALL v. (((fieldRead Node_key x), v) ~: (fieldRead Node_con (fieldRead Node_next x)))))));
comment ''HProps'' (tmp_1_41 = (Hashtable_h k0 (fieldRead Array_length Hashtable_table)));
comment ''FProps'' ((arrayRead Array_arrayState Hashtable_table tmp_1_41) : Node);
comment ''FProps'' ((arrayRead Array_arrayState Hashtable_table tmp_1_41) : Object_alloc);
comment ''FNonNull'' ((arrayRead Array_arrayState Hashtable_table tmp_1_41) ~= null);
comment ''HCProps'' (0 <= tmp_1_41);
comment ''HCProps'' (intless tmp_1_41 (fieldRead Array_length Hashtable_table));
comment ''Acyclic'' ((fieldRead Node_next (arrayRead Array_arrayState Hashtable_table tmp_1_41)) ~= (arrayRead Array_arrayState Hashtable_table tmp_1_41));
comment ''KFound'' ((fieldRead Node_key (arrayRead Array_arrayState Hashtable_table tmp_1_41)) = k0);
comment ''VFound'' ((fieldRead Node_value (arrayRead Array_arrayState Hashtable_table tmp_1_41)) = v0_44);
comment ''ContentDefInv_NewContentDef'' Hashtable_init|] ==>
    comment ''ContentDefInv_NewContentDef'' ((Hashtable_content \<setminus> {(k0, v0_44)}) = {p__6. (EX k v. ((p__6 = (k, v)) & ((k, v) : (fieldRead (fieldWrite Node_con (arrayRead Array_arrayState Hashtable_table tmp_1_41) {((fieldRead Node_key (arrayRead Array_arrayState Hashtable_table tmp_1_41)), (fieldRead Node_value (arrayRead Array_arrayState Hashtable_table tmp_1_41)))}) (arrayRead (arrayWrite Array_arrayState Hashtable_table tmp_1_41 (fieldRead Node_next (arrayRead Array_arrayState Hashtable_table tmp_1_41))) Hashtable_table (Hashtable_h k (fieldRead Array_length Hashtable_table)))))))}))"
apply (unfold comment_def)
apply simp
apply safe
apply (case_tac "Hashtable_h a (Array_length Hashtable_table) = 
                Hashtable_h k0 (Array_length Hashtable_table)", simp_all)
apply (case_tac "Array_arrayState Hashtable_table (Hashtable_h a (Array_length Hashtable_table)) =
                 Array_arrayState Hashtable_table (Hashtable_h k0 (Array_length Hashtable_table))", simp_all)
apply (case_tac "Hashtable_h a (Array_length Hashtable_table) = 
                Hashtable_h k0 (Array_length Hashtable_table)", simp_all)
apply (case_tac "Array_arrayState Hashtable_table (Hashtable_h a (Array_length Hashtable_table)) =
                 Array_arrayState Hashtable_table (Hashtable_h k0 (Array_length Hashtable_table))", simp_all)
apply (case_tac "Hashtable_h a (Array_length Hashtable_table) = 
                Hashtable_h k0 (Array_length Hashtable_table)", simp_all)
apply (case_tac "Array_arrayState Hashtable_table (Hashtable_h a (Array_length Hashtable_table)) =
                 Array_arrayState Hashtable_table (Hashtable_h k0 (Array_length Hashtable_table))", simp_all)
apply force
done

end
