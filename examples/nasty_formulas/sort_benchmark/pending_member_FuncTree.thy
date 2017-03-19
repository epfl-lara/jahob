theory PendingVC = Jahob:

lemma FuncTree_member_4: "([|((fieldRead Pair_data null) = null);
((fieldRead FuncTree_data null) = null);
((fieldRead FuncTree_left null) = null);
((fieldRead FuncTree_right null) = null);
(ALL xObj. (xObj : Object));
((Pair Int FuncTree) = {null});
((Array Int FuncTree) = {null});
((Array Int Pair) = {null});
(null : Object_alloc);
(pointsto FuncTree FuncTree_data Object);
(pointsto FuncTree FuncTree_left FuncTree);
(pointsto FuncTree FuncTree_right FuncTree);
comment ''unalloc_lonely'' (ALL x. ((x ~: Object_alloc) --> ((ALL y. ((fieldRead Pair_data y) ~= x)) & (ALL y. ((fieldRead FuncTree_data y) ~= x)) & (ALL y. ((fieldRead FuncTree_left y) ~= x)) & (ALL y. ((fieldRead FuncTree_right y) ~= x)) & ((fieldRead Pair_data x) = null) & ((fieldRead FuncTree_data x) = null) & ((fieldRead FuncTree_left x) = null) & ((fieldRead FuncTree_right x) = null))));
comment ''FuncTree_PrivateInvcontentDefinitionProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key this), (fieldRead FuncTree_data this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right this))))));
comment ''FuncTree_PrivateInvnullEmptyProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''FuncTree_PrivateInvdataNotNullProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data this) ~= null)));
comment ''FuncTree_PrivateInvleftSmallerProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree)) --> (ALL k. (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_left this))) --> (intless k (fieldRead FuncTree_key this)))))));
comment ''FuncTree_PrivateInvrightBiggerProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree)) --> (ALL k. (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_right this))) --> ((fieldRead FuncTree_key this) < k))))));
comment ''t_type'' (t : FuncTree);
comment ''t_type'' (t : Object_alloc);
comment ''FalseBranch'' (t ~= null);
comment ''FalseBranch'' (k ~= (fieldRead FuncTree_key t));
comment ''FalseBranch'' (~(intless k (fieldRead FuncTree_key t)));
comment ''FuncTree.member_Postcondition'' (tmp_9_164 = (EX v. ((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_right t)))));
comment ''FuncTree.member_Postcondition'' (Object_alloc \<subseteq> Object_alloc_165);
comment ''FuncTree_PrivateInvcontentDefinitionFuncTree.member_Postcondition'' (ALL this. (((this : Object_alloc_165) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key_167 this), (fieldRead FuncTree_data_168 this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left_169 this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right_170 this))))));
comment ''FuncTree_PrivateInvnullEmptyFuncTree.member_Postcondition'' (ALL this. (((this : Object_alloc_165) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''FuncTree_PrivateInvdataNotNullFuncTree.member_Postcondition'' (ALL this. (((this : Object_alloc_165) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data_168 this) ~= null)));
comment ''FuncTree_PrivateInvleftSmallerFuncTree.member_Postcondition'' (ALL this. (((this : Object_alloc_165) & (this : FuncTree)) --> (ALL k__111. (ALL v. (((k__111, v) : (fieldRead FuncTree_content (fieldRead FuncTree_left_169 this))) --> (intless k__111 (fieldRead FuncTree_key_167 this)))))));
comment ''FuncTree_PrivateInvrightBiggerFuncTree.member_Postcondition'' (ALL this. (((this : Object_alloc_165) & (this : FuncTree)) --> (ALL k__112. (ALL v. (((k__112, v) : (fieldRead FuncTree_content (fieldRead FuncTree_right_170 this))) --> ((fieldRead FuncTree_key_167 this) < k__112))))))|] ==>
    comment ''ProcedureEndPostcondition'' (tmp_9_164 = (EX v. ((k, v) : (fieldRead FuncTree_content t)))))"
sorry


end
