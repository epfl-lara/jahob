([|(List_content = (% this. (fieldRead Node_con (fieldRead List_first this))));
(List_edge = (% x y. (((x : Node) & (y = (fieldRead Node_next x))) | ((x : List) & (y = (fieldRead List_first x))))));
((fieldRead Node_data null) = null);
((fieldRead Node_next null) = null);
((fieldRead List_first null) = null);
(ALL xObj. (xObj : Object));
((Node Int List) = {null});
((Array Int List) = {null});
((Array Int Node) = {null});
(null : Object_alloc);
(pointsto Node Node_data Object);
(pointsto Node Node_next Node);
(pointsto List List_first Node);
comment ''unalloc_lonely_Object'' (ALL x. (((x : Object) & (x ~: Object_alloc)) --> ((ALL y. ((fieldRead Node_data y) ~= x)) & (ALL y. ((fieldRead Node_next y) ~= x)) & (ALL y. ((fieldRead List_first y) ~= x)) & ((fieldRead Node_data x) = null) & ((fieldRead Node_next x) = null) & ((fieldRead List_first x) = null))));
comment ''unalloc_lonely_Array'' (ALL x. (((x : Array) & (x ~: Object_alloc)) --> ((ALL y. ((fieldRead Node_data y) ~= x)) & (ALL y. ((fieldRead Node_next y) ~= x)) & (ALL y. ((fieldRead List_first y) ~= x)) & ((fieldRead Node_data x) = null) & ((fieldRead Node_next x) = null) & ((fieldRead List_first x) = null))));
comment ''unalloc_lonely_Node'' (ALL x. (((x : Node) & (x ~: Object_alloc)) --> ((ALL y. ((fieldRead Node_data y) ~= x)) & (ALL y. ((fieldRead Node_next y) ~= x)) & (ALL y. ((fieldRead List_first y) ~= x)) & ((fieldRead Node_data x) = null) & ((fieldRead Node_next x) = null) & ((fieldRead List_first x) = null))));
comment ''unalloc_lonely_List'' (ALL x. (((x : List) & (x ~: Object_alloc)) --> ((ALL y. ((fieldRead Node_data y) ~= x)) & (ALL y. ((fieldRead Node_next y) ~= x)) & (ALL y. ((fieldRead List_first y) ~= x)) & ((fieldRead Node_data x) = null) & ((fieldRead Node_next x) = null) & ((fieldRead List_first x) = null))));
comment ''List_PrivateInv InjProcedurePrecondition'' (ALL x1 x2 y. (((y ~= null) & (List_edge x1 y) & (List_edge x2 y)) --> (x1 = x2)));
comment ''WhileIn_List_OutsidePublicInvOf_Node ConNullProcedurePrecondition'' (ALL this__7. (((this__7 : Object_alloc) & (this__7 : Node) & (this__7 = null)) --> ((fieldRead Node_con this__7) = {})));
comment ''WhileIn_List_OutsidePublicInvOf_Node ConDefProcedurePrecondition'' (ALL this__8. (((this__8 : Object_alloc) & (this__8 : Node) & (this__8 ~= null)) --> (((fieldRead Node_con this__8) = ({(fieldRead Node_data this__8)} Un (fieldRead Node_con (fieldRead Node_next this__8)))) & ((fieldRead Node_data this__8) ~: (fieldRead Node_con (fieldRead Node_next this__8))))));
comment ''thisNotNull'' (this ~= null);
comment ''thisType'' (this : List);
comment ''thisType'' (this : Object_alloc);
comment ''o1_type'' (o1 : Object);
comment ''o1_type'' (o1 : Object_alloc);
comment ''tmp_12_type'' (tmp_12 : Node);
comment ''tmp_12_type'' (tmp_12 : Object_alloc);
comment ''nxt_type'' (nxt : Node);
comment ''nxt_type'' (nxt : Object_alloc);
comment ''tmp_11_type'' (tmp_11 : Node);
comment ''tmp_11_type'' (tmp_11 : Object_alloc);
comment ''tmp_9_type'' (tmp_9 : Object);
comment ''tmp_9_type'' (tmp_9 : Object_alloc);
comment ''tmp_8_type'' (tmp_8 : Node);
comment ''tmp_8_type'' (tmp_8 : Object_alloc);
comment ''current_type'' (current : Node);
comment ''current_type'' (current : Object_alloc);
comment ''tmp_7_type'' (tmp_7 : Node);
comment ''tmp_7_type'' (tmp_7 : Object_alloc);
comment ''prev_type'' (prev : Node);
comment ''prev_type'' (prev : Object_alloc);
comment ''tmp_5_type'' (tmp_5 : Node);
comment ''tmp_5_type'' (tmp_5 : Object_alloc);
comment ''second_type'' (second : Node);
comment ''second_type'' (second : Object_alloc);
comment ''tmp_3_type'' (tmp_3 : Object);
comment ''tmp_3_type'' (tmp_3 : Object_alloc);
comment ''tmp_2_type'' (tmp_2 : Node);
comment ''tmp_2_type'' (tmp_2 : Object_alloc);
comment ''f_type'' (f : Node);
comment ''f_type'' (f : Object_alloc);
comment ''List.member_Postcondition'' (tmp_1_25 = (o1 : (fieldRead List_content this)));
comment ''List.member_Postcondition'' (Object_alloc \<subseteq> Object_alloc_26);
comment ''List_PrivateInv InjList.member_Postcondition'' (ALL x1 x2 y. (((y ~= null) & (List_edge x1 y) & (List_edge x2 y)) --> (x1 = x2)));
comment ''WhileIn_List_OutsidePublicInvOf_Node ConNullList.member_Postcondition'' (ALL this__11. (((this__11 : Object_alloc_26) & (this__11 : Node) & (this__11 = null)) --> ((fieldRead Node_con this__11) = {})));
comment ''WhileIn_List_OutsidePublicInvOf_Node ConDefList.member_Postcondition'' (ALL this__12. (((this__12 : Object_alloc_26) & (this__12 : Node) & (this__12 ~= null)) --> (((fieldRead Node_con this__12) = ({(fieldRead Node_data this__12)} Un (fieldRead Node_con (fieldRead Node_next this__12)))) & ((fieldRead Node_data this__12) ~: (fieldRead Node_con (fieldRead Node_next this__12))))));
comment ''TrueBranch'' tmp_1_25;
((fieldRead List_first this) ~= null);
comment ''wonder1'' ((fieldRead Node_con (fieldRead Node_next (fieldRead List_first this))) = ((fieldRead Node_con (fieldRead List_first this)) \<setminus> {(fieldRead Node_data (fieldRead List_first this))}));
comment ''FalseBranch'' ((fieldRead Node_data (fieldRead List_first this)) ~= o1);
(List_content_17 = (% this__5. (fieldRead (fieldWrite Node_con (fieldRead List_first this) ((fieldRead Node_con (fieldRead List_first this)) \<setminus> {o1})) (fieldRead List_first this__5))));
comment ''LoopConditionFalse'' (~((fieldRead Node_data (fieldRead Node_next (fieldRead List_first this))) ~= o1));
comment ''injectiveStill'' (ALL x1 x2 y. (((y ~= null) & (List_edge x1 y) & (List_edge x2 y)) --> (x1 = x2)));
comment ''FalseBranch'' ((fieldRead Node_next (fieldRead Node_next (fieldRead List_first this))) ~= null);
(List_edge_8 = (% x y. (((x : Node) & (y = (fieldRead (fieldWrite Node_next (fieldRead List_first this) null) x))) | ((x : List) & (y = (fieldRead List_first x))))));
(List_edge_6 = (% x y. (((x : Node) & (y = (fieldRead (fieldWrite (fieldWrite Node_next (fieldRead List_first this) null) (fieldRead Node_next (fieldRead List_first this)) null) x))) | ((x : List) & (y = (fieldRead List_first x))))));
(ALL n. (~(List_edge_6 n (fieldRead Node_next (fieldRead List_first this)))));
(ALL n. (~(List_edge_6 n (fieldRead Node_next (fieldRead Node_next (fieldRead List_first this))))));
comment ''injectiveStill2'' (ALL x1 x2 y. (((y ~= null) & (List_edge_6 x1 y) & (List_edge_6 x2 y)) --> (x1 = x2)));
(List_edge_4 = (% x y. (((x : Node) & (y = (fieldRead (fieldWrite (fieldWrite (fieldWrite Node_next (fieldRead List_first this) null) (fieldRead Node_next (fieldRead List_first this)) null) (fieldRead List_first this) (fieldRead Node_next (fieldRead Node_next (fieldRead List_first this)))) x))) | ((x : List) & (y = (fieldRead List_first x))))));
(List_content_2 = (% this__6. (fieldRead (fieldWrite (fieldWrite Node_con (fieldRead List_first this) ((fieldRead Node_con (fieldRead List_first this)) \<setminus> {o1})) (fieldRead Node_next (fieldRead List_first this)) {(fieldRead Node_data (fieldRead Node_next (fieldRead List_first this)))}) (fieldRead List_first this__6))));
(y ~= null);
(List_edge_4 x1 y);
(List_edge_4 x2 y)|] ==>
    comment ''injectiveFinally'' (x1 = x2))