theory PendingVC = Jahob:

lemma FuncTree_add1_10: "([|((fieldRead Pair_data null) = null);
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
comment ''ProcedurePrecondition'' (ALL y. ((k, y) ~: (fieldRead FuncTree_content t)));
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
comment ''FuncTree.add1_Postcondition'' ((fieldRead FuncTree_content tmp_6_82) = ((fieldRead FuncTree_content (fieldRead FuncTree_left t)) Un {(k, v)}));
comment ''contentDefinitionFuncTree.add1_Postcondition'' (ALL this. (((this : Object_alloc_83) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key this), (fieldRead FuncTree_data this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right this))))));
comment ''nullEmptyFuncTree.add1_Postcondition'' (ALL this. (((this : Object_alloc_83) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''dataNotNullFuncTree.add1_Postcondition'' (ALL this. (((this : Object_alloc_83) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data this) ~= null)));
comment ''leftSmallerFuncTree.add1_Postcondition'' (ALL this. (((this : Object_alloc_83) & (this : FuncTree)) --> (ALL k__17. (ALL v__18. (((k__17, v__18) : (fieldRead FuncTree_content (fieldRead FuncTree_left this))) --> (intless k__17 (fieldRead FuncTree_key this)))))));
comment ''rightBiggerFuncTree.add1_Postcondition'' (ALL this. (((this : Object_alloc_83) & (this : FuncTree)) --> (ALL k__19. (ALL v__20. (((k__19, v__20) : (fieldRead FuncTree_content (fieldRead FuncTree_right this))) --> ((fieldRead FuncTree_key this) < k__19))))));
comment ''FuncTree.add1_Postcondition'' (Object_alloc \<subseteq> Object_alloc_83);
comment ''tmp_6_type'' (tmp_6_82 : FuncTree);
comment ''tmp_6_type'' (tmp_6_82 : Object_alloc_83);
comment ''AllocatedObject'' (tmp_11_78 ~= null);
comment ''AllocatedObject'' (tmp_11_78 ~: Object_alloc_83);
comment ''AllocatedObject'' (tmp_11_78 : FuncTree);
comment ''AllocatedObject'' (ALL y. ((fieldRead Pair_data y) ~= tmp_11_78));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_data y) ~= tmp_11_78));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_left y) ~= tmp_11_78));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_right y) ~= tmp_11_78));
comment ''AllocatedObject'' ((fieldRead Pair_data tmp_11_78) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_data tmp_11_78) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_left tmp_11_78) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_right tmp_11_78) = null);
(this_bv3451 : (Object_alloc_83 Un {tmp_11_78}));
(this_bv3451 : FuncTree);
(this_bv3451 ~= null)|] ==>
    comment ''contentDefinition_ProcedureEndPostcondition'' ((fieldRead (fieldWrite FuncTree_content tmp_11_78 ((fieldRead FuncTree_content t) Un {(k, v)})) this_bv3451) = (({((fieldRead (fieldWrite FuncTree_key tmp_11_78 (fieldRead FuncTree_key t)) this_bv3451), (fieldRead (fieldWrite FuncTree_data tmp_11_78 (fieldRead FuncTree_data t)) this_bv3451))} Un (fieldRead (fieldWrite FuncTree_content tmp_11_78 ((fieldRead FuncTree_content t) Un {(k, v)})) (fieldRead (fieldWrite FuncTree_left tmp_11_78 tmp_6_82) this_bv3451))) Un (fieldRead (fieldWrite FuncTree_content tmp_11_78 ((fieldRead FuncTree_content t) Un {(k, v)})) (fieldRead (fieldWrite FuncTree_right tmp_11_78 (fieldRead FuncTree_right t)) this_bv3451)))))"
sorry

lemma FuncTree_add1_19: "([|((fieldRead Pair_data null) = null);
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
comment ''ProcedurePrecondition'' (ALL y. ((k, y) ~: (fieldRead FuncTree_content t)));
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
comment ''FuncTree.add1_Postcondition'' ((fieldRead FuncTree_content tmp_10_87) = ((fieldRead FuncTree_content (fieldRead FuncTree_right t)) Un {(k, v)}));
comment ''contentDefinitionFuncTree.add1_Postcondition'' (ALL this. (((this : Object_alloc_88) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_content this) = (({((fieldRead FuncTree_key this), (fieldRead FuncTree_data this))} Un (fieldRead FuncTree_content (fieldRead FuncTree_left this))) Un (fieldRead FuncTree_content (fieldRead FuncTree_right this))))));
comment ''nullEmptyFuncTree.add1_Postcondition'' (ALL this. (((this : Object_alloc_88) & (this : FuncTree) & (this = null)) --> ((fieldRead FuncTree_content this) = {})));
comment ''dataNotNullFuncTree.add1_Postcondition'' (ALL this. (((this : Object_alloc_88) & (this : FuncTree) & (this ~= null)) --> ((fieldRead FuncTree_data this) ~= null)));
comment ''leftSmallerFuncTree.add1_Postcondition'' (ALL this. (((this : Object_alloc_88) & (this : FuncTree)) --> (ALL k__25. (ALL v__26. (((k__25, v__26) : (fieldRead FuncTree_content (fieldRead FuncTree_left this))) --> (intless k__25 (fieldRead FuncTree_key this)))))));
comment ''rightBiggerFuncTree.add1_Postcondition'' (ALL this. (((this : Object_alloc_88) & (this : FuncTree)) --> (ALL k__27. (ALL v__28. (((k__27, v__28) : (fieldRead FuncTree_content (fieldRead FuncTree_right this))) --> ((fieldRead FuncTree_key this) < k__27))))));
comment ''FuncTree.add1_Postcondition'' (Object_alloc \<subseteq> Object_alloc_88);
comment ''tmp_10_type'' (tmp_10_87 : FuncTree);
comment ''tmp_10_type'' (tmp_10_87 : Object_alloc_88);
comment ''AllocatedObject'' (tmp_11_78 ~= null);
comment ''AllocatedObject'' (tmp_11_78 ~: Object_alloc_88);
comment ''AllocatedObject'' (tmp_11_78 : FuncTree);
comment ''AllocatedObject'' (ALL y. ((fieldRead Pair_data y) ~= tmp_11_78));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_data y) ~= tmp_11_78));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_left y) ~= tmp_11_78));
comment ''AllocatedObject'' (ALL y. ((fieldRead FuncTree_right y) ~= tmp_11_78));
comment ''AllocatedObject'' ((fieldRead Pair_data tmp_11_78) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_data tmp_11_78) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_left tmp_11_78) = null);
comment ''AllocatedObject'' ((fieldRead FuncTree_right tmp_11_78) = null);
(this_bv2036 : (Object_alloc_88 Un {tmp_11_78}));
(this_bv2036 : FuncTree);
(this_bv2036 ~= null)|] ==>
    comment ''contentDefinition_ProcedureEndPostcondition'' ((fieldRead (fieldWrite FuncTree_content tmp_11_78 ((fieldRead FuncTree_content t) Un {(k, v)})) this_bv2036) = (({((fieldRead (fieldWrite FuncTree_key tmp_11_78 (fieldRead FuncTree_key t)) this_bv2036), (fieldRead (fieldWrite FuncTree_data tmp_11_78 (fieldRead FuncTree_data t)) this_bv2036))} Un (fieldRead (fieldWrite FuncTree_content tmp_11_78 ((fieldRead FuncTree_content t) Un {(k, v)})) (fieldRead (fieldWrite FuncTree_left tmp_11_78 (fieldRead FuncTree_left t)) this_bv2036))) Un (fieldRead (fieldWrite FuncTree_content tmp_11_78 ((fieldRead FuncTree_content t) Un {(k, v)})) (fieldRead (fieldWrite FuncTree_right tmp_11_78 tmp_10_87) this_bv2036)))))"
sorry


end
