theory PendingVC = Jahob:

lemma FuncTree_lookup1_7: "([|((fieldRead Pair_data null) = null);
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
comment ''FuncTree.lookup1_Postcondition'' ((tmp_10_240 ~= null) --> ((k, tmp_10_240) : (fieldRead FuncTree_content (fieldRead FuncTree_right t))));
comment ''FuncTree.lookup1_Postcondition'' ((tmp_10_240 = null) --> (ALL v. ((k, v) ~: (fieldRead FuncTree_content (fieldRead FuncTree_right t)))));
comment ''FuncTree.lookup1_Postcondition'' (Object_alloc \<subseteq> Object_alloc_241);
comment ''FuncTree_PrivateInvcontentDefinitionFuncTree.lookup1_Postcondition'' (ALL this. (((this : Object_alloc_241) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key_243 this), (fieldRead FuncTree_data_244 this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left_245 this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right_246 this))))));
comment ''FuncTree_PrivateInvnullEmptyFuncTree.lookup1_Postcondition'' (ALL this. (((this : Object_alloc_241) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''FuncTree_PrivateInvdataNotNullFuncTree.lookup1_Postcondition'' (ALL this. (((this : Object_alloc_241) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data_244 this) ~= null)));
comment ''FuncTree_PrivateInvleftSmallerFuncTree.lookup1_Postcondition'' (ALL this. (((this : Object_alloc_241) & (this : FuncTree)) --> (ALL k__187. (ALL v. (((k__187, v) : (fieldRead FuncTree_content (fieldRead FuncTree_left_245 this))) --> (intless k__187 (fieldRead FuncTree_key_243 this)))))));
comment ''FuncTree_PrivateInvrightBiggerFuncTree.lookup1_Postcondition'' (ALL this. (((this : Object_alloc_241) & (this : FuncTree)) --> (ALL k__188. (ALL v. (((k__188, v) : (fieldRead FuncTree_content (fieldRead FuncTree_right_246 this))) --> ((fieldRead FuncTree_key_243 this) < k__188))))));
comment ''tmp_10_type'' (tmp_10_240 : Object);
comment ''tmp_10_type'' (tmp_10_240 : Object_alloc_241);
(tmp_10_240 = null)|] ==>
    comment ''ProcedureEndPostcondition'' ((k, v_bv10487) ~: (fieldRead FuncTree_content t)))"
sorry


end
