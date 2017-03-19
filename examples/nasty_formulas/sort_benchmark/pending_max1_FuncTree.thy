theory PendingVC = Jahob:

lemma FuncTree_max1_22: "([|((fieldRead Pair_data null) = null);
((fieldRead FuncTree_data null) = null);
((fieldRead FuncTree_left null) = null);
((fieldRead FuncTree_right null) = null);
(ALL xObj. (xObj : Object));
((Pair Int FuncTree) = {null});
((Array Int FuncTree) = {null});
((Array Int Pair) = {null});
(null : Object_alloc);
(pointsto Pair Pair_data Object);
(pointsto FuncTree FuncTree_data Object);
(pointsto FuncTree FuncTree_left FuncTree);
(pointsto FuncTree FuncTree_right FuncTree);
comment ''unalloc_lonely'' (ALL x. ((x ~: Object_alloc) --> ((ALL y. ((fieldRead Pair_data y) ~= x)) & (ALL y. ((fieldRead FuncTree_data y) ~= x)) & (ALL y. ((fieldRead FuncTree_left y) ~= x)) & (ALL y. ((fieldRead FuncTree_right y) ~= x)) & ((fieldRead Pair_data x) = null) & ((fieldRead FuncTree_data x) = null) & ((fieldRead FuncTree_left x) = null) & ((fieldRead FuncTree_right x) = null))));
comment ''contentDefinitionProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key this), (fieldRead FuncTree_data this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right this))))));
comment ''nullEmptyProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''dataNotNullProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data this) ~= null)));
comment ''leftSmallerProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree)) --> (ALL k. (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_left this))) --> (intless k (fieldRead FuncTree_key this)))))));
comment ''rightBiggerProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree)) --> (ALL k. (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_right this))) --> ((fieldRead FuncTree_key this) < k))))));
comment ''ProcedurePrecondition'' ((fieldRead FuncTree_content t) ~= {});
comment ''t_type'' (t : FuncTree);
comment ''t_type'' (t : Object_alloc);
comment ''AllocatedObject'' (tmp_1_277 ~= null);
comment ''AllocatedObject'' (tmp_1_277 ~: Object_alloc);
comment ''AllocatedObject'' (tmp_1_277 : Pair);
comment ''AllocatedObject'' (ALL y. ((fieldRead Pair_data y) ~= tmp_1_277));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_data y) ~= tmp_1_277));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_left y) ~= tmp_1_277));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_right y) ~= tmp_1_277));
comment ''AllocatedObject'' ((fieldRead Pair_data tmp_1_277) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_data tmp_1_277) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_left tmp_1_277) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_right tmp_1_277) = null);
comment ''FalseBranch'' ((fieldRead FuncTree_right t) ~= null);
comment ''contentDefinitionFuncTree.max1_Postcondition'' (ALL this. (((this : Object_alloc_270) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key this), (fieldRead FuncTree_data this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right this))))));
comment ''nullEmptyFuncTree.max1_Postcondition'' (ALL this. (((this : Object_alloc_270) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''dataNotNullFuncTree.max1_Postcondition'' (ALL this. (((this : Object_alloc_270) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data this) ~= null)));
comment ''leftSmallerFuncTree.max1_Postcondition'' (ALL this. (((this : Object_alloc_270) & (this : FuncTree)) --> (ALL k. (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_left this))) --> (intless k (fieldRead FuncTree_key this)))))));
comment ''rightBiggerFuncTree.max1_Postcondition'' (ALL this. (((this : Object_alloc_270) & (this : FuncTree)) --> (ALL k. (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_right this))) --> ((fieldRead FuncTree_key this) < k))))));
comment ''FuncTree.max1_Postcondition'' (tmp_7_269 ~= null);
comment ''FuncTree.max1_Postcondition'' ((fieldRead Pair_data tmp_7_269) ~= null);
comment ''FuncTree.max1_Postcondition'' (((fieldRead Pair_key tmp_7_269), (fieldRead Pair_data tmp_7_269)) : (fieldRead FuncTree_content (fieldRead FuncTree_right t)));
comment ''FuncTree.max1_Postcondition'' (ALL k. ((k ~= (fieldRead Pair_key tmp_7_269)) --> (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_right t))) --> (intless k (fieldRead Pair_key tmp_7_269))))));
comment ''FuncTree.max1_Postcondition'' ((Object_alloc Un {tmp_1_277}) \<subseteq> Object_alloc_270);
comment ''tmp_7_type'' (tmp_7_269 : Pair);
comment ''tmp_7_type'' (tmp_7_269 : Object_alloc_270);
(k_bv11183 ~= (fieldRead Pair_key tmp_7_269));
((k_bv11183, v_bv11277) : (fieldRead FuncTree_content t))|] ==>
    comment ''ProcedureEndPostcondition'' (intless k_bv11183 (fieldRead Pair_key tmp_7_269)))"
sorry


end
