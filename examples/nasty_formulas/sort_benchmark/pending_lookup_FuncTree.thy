theory PendingVC = Jahob:

lemma FuncTree_lookup_4: "([|((fieldRead Pair_data null) = null);
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
comment ''FuncTree.lookup_Postcondition'' (((tmp_10_202 ~= null) & ((k, tmp_10_202) : (fieldRead FuncTree_content (fieldRead FuncTree_right t)))) | ((tmp_10_202 = null) & (ALL v. ((k, v) ~: (fieldRead FuncTree_content (fieldRead FuncTree_right t))))));
comment ''FuncTree.lookup_Postcondition'' (Object_alloc \<subseteq> Object_alloc_203);
comment ''FuncTree_PrivateInvcontentDefinitionFuncTree.lookup_Postcondition'' (ALL this. (((this : Object_alloc_203) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key_205 this), (fieldRead FuncTree_data_206 this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left_207 this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right_208 this))))));
comment ''FuncTree_PrivateInvnullEmptyFuncTree.lookup_Postcondition'' (ALL this. (((this : Object_alloc_203) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''FuncTree_PrivateInvdataNotNullFuncTree.lookup_Postcondition'' (ALL this. (((this : Object_alloc_203) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data_206 this) ~= null)));
comment ''FuncTree_PrivateInvleftSmallerFuncTree.lookup_Postcondition'' (ALL this. (((this : Object_alloc_203) & (this : FuncTree)) --> (ALL k__167. (ALL v. (((k__167, v) : (fieldRead FuncTree_content (fieldRead FuncTree_left_207 this))) --> (intless k__167 (fieldRead FuncTree_key_205 this)))))));
comment ''FuncTree_PrivateInvrightBiggerFuncTree.lookup_Postcondition'' (ALL this. (((this : Object_alloc_203) & (this : FuncTree)) --> (ALL k__168. (ALL v. (((k__168, v) : (fieldRead FuncTree_content (fieldRead FuncTree_right_208 this))) --> ((fieldRead FuncTree_key_205 this) < k__168))))));
comment ''tmp_10_type'' (tmp_10_202 : Object);
comment ''tmp_10_type'' (tmp_10_202 : Object_alloc_203)|] ==>
    comment ''ProcedureEndPostcondition'' (((tmp_10_202 ~= null) & ((k, tmp_10_202) : (fieldRead FuncTree_content t))) | ((tmp_10_202 = null) & (ALL v. ((k, v) ~: (fieldRead FuncTree_content t))))))"
sorry


end
