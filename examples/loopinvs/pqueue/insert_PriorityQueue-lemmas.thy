theory insert_PriorityQueue_lemmas = Jahob:

lemma PriorityQueue_insert_36: "([|comment ''RelToIAssumingLoopInv'' ((intless (intplus (intplus i_32 i_32) 1) (intplus PriorityQueue_length 1)) --> (intless (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState_33 PriorityQueue_queue (intplus (intplus i_32 i_32) 1))) (fieldRead PriorityQueueElement_key e)));
comment ''RelToIAssumingLoopInv'' ((intless (intplus (intplus i_32 i_32) 2) (intplus PriorityQueue_length 1)) --> (intless (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState_33 PriorityQueue_queue (intplus (intplus i_32 i_32) 2))) (fieldRead PriorityQueueElement_key e)));
comment ''OrderedSkipLoopAssumingLoopInv'' ((i_32 = PriorityQueue_length) --> (ALL j k. (((0 <= j) & (intless j PriorityQueue_length) & (0 <= k) & (intless k PriorityQueue_length) & ((k = (intplus (intplus j j) 1)) | (k = (intplus (intplus j j) 2)))) --> ((fieldRead PriorityQueueElement_key (arrayRead Array_arrayState_33 PriorityQueue_queue k)) <= (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState_33 PriorityQueue_queue j))))));
comment ''OrderedPostLoopAssumingLoopInv'' ((i_32 ~= PriorityQueue_length) --> (ALL j k. (((0 <= j) & (intless j (intplus PriorityQueue_length 1)) & (0 <= k) & (intless k (intplus PriorityQueue_length 1)) & ((k = (intplus (intplus j j) 1)) | (k = (intplus (intplus j j) 2)))) --> ((fieldRead PriorityQueueElement_key (arrayRead Array_arrayState_33 PriorityQueue_queue k)) <= (fieldRead PriorityQueueElement_key (arrayRead Array_arrayState_33 PriorityQueue_queue j))))));
comment ''LoopExitCond'' ((intless 0 i_32) --> (ALL x. (((i_32 = (intplus (intplus x x) 1)) | (i_32 = (intplus (intplus x x) 2))) --> ((fieldRead PriorityQueueElement_key e) <= (fieldRead PriorityQueueElement_key (arrayRead (arrayWrite Array_arrayState_33 PriorityQueue_queue i_32 e) PriorityQueue_queue x))))));
comment ''OrderedInv_OrderedFinal'' PriorityQueue_init;
comment ''OrderedInv_OrderedFinal'' (0 <= i__8_bv262);
comment ''OrderedInv_OrderedFinal'' (intless i__8_bv262 (intplus PriorityQueue_length 1));
comment ''OrderedInv_OrderedFinal'' (0 <= j_bv292);
comment ''OrderedInv_OrderedFinal'' (intless j_bv292 (intplus PriorityQueue_length 1));
comment ''OrderedInv_OrderedFinal'' ((j_bv292 = (intplus (intplus i__8_bv262 i__8_bv262) 1)) | (j_bv292 = (intplus (intplus i__8_bv262 i__8_bv262) 2)))|] ==>
    comment ''OrderedInv_OrderedFinal'' ((fieldRead PriorityQueueElement_key (arrayRead (arrayWrite Array_arrayState_33 PriorityQueue_queue i_32 e) PriorityQueue_queue j_bv292)) <= (fieldRead PriorityQueueElement_key (arrayRead (arrayWrite Array_arrayState_33 PriorityQueue_queue i_32 e) PriorityQueue_queue i__8_bv262))))"
apply (unfold comment_def)
apply simp
apply (case_tac "j_bv292 ~= i_32", simp_all)
apply (case_tac "i__8_bv262 ~= i_32", simp_all)
apply (case_tac "i_32 = PriorityQueue_length", simp_all)
apply (case_tac "j_bv292 = 2 * i_32 + 1", simp_all)
apply (case_tac "i_32 = 2 * i__8_bv262 + 1", simp_all)
done

end
