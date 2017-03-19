theory PendingVC = Jahob:

lemma FuncTree_update1_9: "([|((fieldRead Pair_data null) = null);
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
comment ''ProcedurePrecondition'' (v ~= null);
comment ''contentDefinitionProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key this), (fieldRead FuncTree_data this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right this))))));
comment ''nullEmptyProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''dataNotNullProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data this) ~= null)));
comment ''leftSmallerProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree)) --> (ALL k. (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_left this))) --> (intless k (fieldRead FuncTree_key this)))))));
comment ''rightBiggerProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree)) --> (ALL k. (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_right this))) --> ((fieldRead FuncTree_key this) < k))))));
comment ''v_type'' (v : Object);
comment ''v_type'' (v : Object_alloc);
comment ''t_type'' (t : FuncTree);
comment ''t_type'' (t : Object_alloc);
comment ''FalseBranch'' (t ~= null);
comment ''TrueBranch'' (intless k (fieldRead FuncTree_key t));
comment ''FuncTree.update1_Postcondition'' ((fieldRead FuncTree_content tmp_5_120) = (((fieldRead FuncTree_content (fieldRead FuncTree_left t)) \<setminus> {p. (EX x y. ((p = (x, y)) & (x = k)))}) Un {(k, v)}));
comment ''contentDefinitionFuncTree.update1_Postcondition'' (ALL this. (((this : Object_alloc_121) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key this), (fieldRead FuncTree_data this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right this))))));
comment ''nullEmptyFuncTree.update1_Postcondition'' (ALL this. (((this : Object_alloc_121) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''dataNotNullFuncTree.update1_Postcondition'' (ALL this. (((this : Object_alloc_121) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data this) ~= null)));
comment ''leftSmallerFuncTree.update1_Postcondition'' (ALL this. (((this : Object_alloc_121) & (this : FuncTree)) --> (ALL k__41. (ALL v__42. (((k__41, v__42) : (fieldRead FuncTree_content (fieldRead FuncTree_left this))) --> (intless k__41 (fieldRead FuncTree_key this)))))));
comment ''rightBiggerFuncTree.update1_Postcondition'' (ALL this. (((this : Object_alloc_121) & (this : FuncTree)) --> (ALL k__43. (ALL v__44. (((k__43, v__44) : (fieldRead FuncTree_content (fieldRead FuncTree_right this))) --> ((fieldRead FuncTree_key this) < k__43))))));
comment ''FuncTree.update1_Postcondition'' (Object_alloc \<subseteq> Object_alloc_121);
comment ''tmp_5_type'' (tmp_5_120 : FuncTree);
comment ''tmp_5_type'' (tmp_5_120 : Object_alloc_121);
comment ''AllocatedObject'' (tmp_18_108 ~= null);
comment ''AllocatedObject'' (tmp_18_108 ~: Object_alloc_121);
comment ''AllocatedObject'' (tmp_18_108 : FuncTree);
comment ''AllocatedObject'' (ALL y. ((fieldRead Pair_data y) ~= tmp_18_108));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_data y) ~= tmp_18_108));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_left y) ~= tmp_18_108));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_right y) ~= tmp_18_108));
comment ''AllocatedObject'' ((fieldRead Pair_data tmp_18_108) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_data tmp_18_108) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_left tmp_18_108) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_right tmp_18_108) = null);
(this_bv8639 : (Object_alloc_121 Un {tmp_18_108}));
(this_bv8639 : FuncTree);
(this_bv8639 ~= null)|] ==>
    comment ''contentDefinition_ProcedureEndPostcondition'' ((fieldRead (fieldWrite FuncTree_content tmp_18_108 (((fieldRead FuncTree_content t) \<setminus> {p. (EX x y. ((p = (x, y)) & (x = k)))}) Un {(k, v)})) this_bv8639) = (({((fieldRead (fieldWrite FuncTree_key tmp_18_108 (fieldRead FuncTree_key t)) this_bv8639), (fieldRead (fieldWrite FuncTree_data tmp_18_108 (fieldRead FuncTree_data t)) this_bv8639))} Un (fieldRead (fieldWrite FuncTree_content tmp_18_108 (((fieldRead FuncTree_content t) \<setminus> {p. (EX x y. ((p = (x, y)) & (x = k)))}) Un {(k, v)})) (fieldRead (fieldWrite FuncTree_left tmp_18_108 tmp_5_120) this_bv8639))) Un (fieldRead (fieldWrite FuncTree_content tmp_18_108 (((fieldRead FuncTree_content t) \<setminus> {p. (EX x y. ((p = (x, y)) & (x = k)))}) Un {(k, v)})) (fieldRead (fieldWrite FuncTree_right tmp_18_108 (fieldRead FuncTree_right t)) this_bv8639)))))"
sorry

lemma FuncTree_update1_16: "([|((fieldRead Pair_data null) = null);
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
comment ''ProcedurePrecondition'' (v ~= null);
comment ''contentDefinitionProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key this), (fieldRead FuncTree_data this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right this))))));
comment ''nullEmptyProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''dataNotNullProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data this) ~= null)));
comment ''leftSmallerProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree)) --> (ALL k. (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_left this))) --> (intless k (fieldRead FuncTree_key this)))))));
comment ''rightBiggerProcedurePrecondition'' (ALL this. (((this : Object_alloc) & (this : FuncTree)) --> (ALL k. (ALL v. (((k, v) : (fieldRead FuncTree_content (fieldRead FuncTree_right this))) --> ((fieldRead FuncTree_key this) < k))))));
comment ''v_type'' (v : Object);
comment ''v_type'' (v : Object_alloc);
comment ''t_type'' (t : FuncTree);
comment ''t_type'' (t : Object_alloc);
comment ''FalseBranch'' (t ~= null);
comment ''FalseBranch'' (~(intless k (fieldRead FuncTree_key t)));
comment ''TrueBranch'' (intless (fieldRead FuncTree_key t) k);
comment ''FuncTree.update1_Postcondition'' ((fieldRead FuncTree_content tmp_13_129) = (((fieldRead FuncTree_content (fieldRead FuncTree_right t)) \<setminus> {p. (EX x y. ((p = (x, y)) & (x = k)))}) Un {(k, v)}));
comment ''contentDefinitionFuncTree.update1_Postcondition'' (ALL this. (((this : Object_alloc_130) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key this), (fieldRead FuncTree_data this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right this))))));
comment ''nullEmptyFuncTree.update1_Postcondition'' (ALL this. (((this : Object_alloc_130) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''dataNotNullFuncTree.update1_Postcondition'' (ALL this. (((this : Object_alloc_130) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data this) ~= null)));
comment ''leftSmallerFuncTree.update1_Postcondition'' (ALL this. (((this : Object_alloc_130) & (this : FuncTree)) --> (ALL k__49. (ALL v__50. (((k__49, v__50) : (fieldRead FuncTree_content (fieldRead FuncTree_left this))) --> (intless k__49 (fieldRead FuncTree_key this)))))));
comment ''rightBiggerFuncTree.update1_Postcondition'' (ALL this. (((this : Object_alloc_130) & (this : FuncTree)) --> (ALL k__51. (ALL v__52. (((k__51, v__52) : (fieldRead FuncTree_content (fieldRead FuncTree_right this))) --> ((fieldRead FuncTree_key this) < k__51))))));
comment ''FuncTree.update1_Postcondition'' (Object_alloc \<subseteq> Object_alloc_130);
comment ''tmp_13_type'' (tmp_13_129 : FuncTree);
comment ''tmp_13_type'' (tmp_13_129 : Object_alloc_130);
comment ''AllocatedObject'' (tmp_18_108 ~= null);
comment ''AllocatedObject'' (tmp_18_108 ~: Object_alloc_130);
comment ''AllocatedObject'' (tmp_18_108 : FuncTree);
comment ''AllocatedObject'' (ALL y. ((fieldRead Pair_data y) ~= tmp_18_108));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_data y) ~= tmp_18_108));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_left y) ~= tmp_18_108));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_right y) ~= tmp_18_108));
comment ''AllocatedObject'' ((fieldRead Pair_data tmp_18_108) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_data tmp_18_108) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_left tmp_18_108) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_right tmp_18_108) = null);
(this_bv7281 : (Object_alloc_130 Un {tmp_18_108}));
(this_bv7281 : FuncTree);
(this_bv7281 ~= null)|] ==>
    comment ''contentDefinition_ProcedureEndPostcondition'' ((fieldRead (fieldWrite FuncTree_content tmp_18_108 (((fieldRead FuncTree_content t) \<setminus> {p. (EX x y. ((p = (x, y)) & (x = k)))}) Un {(k, v)})) this_bv7281) = (({((fieldRead (fieldWrite FuncTree_key tmp_18_108 (fieldRead FuncTree_key t)) this_bv7281), (fieldRead (fieldWrite FuncTree_data tmp_18_108 (fieldRead FuncTree_data t)) this_bv7281))} Un (fieldRead (fieldWrite FuncTree_content tmp_18_108 (((fieldRead FuncTree_content t) \<setminus> {p. (EX x y. ((p = (x, y)) & (x = k)))}) Un {(k, v)})) (fieldRead (fieldWrite FuncTree_left tmp_18_108 (fieldRead FuncTree_left t)) this_bv7281))) Un (fieldRead (fieldWrite FuncTree_content tmp_18_108 (((fieldRead FuncTree_content t) \<setminus> {p. (EX x y. ((p = (x, y)) & (x = k)))}) Un {(k, v)})) (fieldRead (fieldWrite FuncTree_right tmp_18_108 tmp_13_129) this_bv7281)))))"
sorry


end
