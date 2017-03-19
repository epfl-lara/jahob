theory containsKey0_Hashtable_lemmas = Jahob:

lemma Hashtable_containsKey0_2: "([|comment ''ElementInjInvoldElemInj'' (ALL this. (((this : Object_alloc) & (this : Hashtable) & (fieldRead Hashtable_init this)) --> (ALL i j h1 h2. (((0 <= i) & (intless i (fieldRead Array_length (fieldRead Hashtable_table h1))) & (0 <= j) & (intless j (fieldRead Array_length (fieldRead Hashtable_table h2))) & ((arrayRead Array_arrayState (fieldRead Hashtable_table h1) i) ~= null) & ((arrayRead Array_arrayState (fieldRead Hashtable_table h1) i) = (arrayRead Array_arrayState (fieldRead Hashtable_table h2) j))) --> ((i = j) & (h1 = h2))))));
comment ''allocSame'' (Object_alloc_10 = Object_alloc);
comment ''ElementInjInv_newElemInj'' (this_bv3109 : Object_alloc_10);
comment ''ElementInjInv_newElemInj'' (this_bv3109 : Hashtable);
comment ''ElementInjInv_newElemInj'' (fieldRead Hashtable_init this_bv3109);
comment ''ElementInjInv_newElemInj'' (0 <= i_bv3110);
comment ''ElementInjInv_newElemInj'' (intless i_bv3110 (fieldRead Array_length (fieldRead Hashtable_table h1_bv3112)));
comment ''ElementInjInv_newElemInj'' (0 <= j_bv3111);
comment ''ElementInjInv_newElemInj'' (intless j_bv3111 (fieldRead Array_length (fieldRead Hashtable_table h2_bv3163)));
comment ''ElementInjInv_newElemInj'' ((arrayRead Array_arrayState (fieldRead Hashtable_table h1_bv3112) i_bv3110) ~= null);
comment ''ElementInjInv_newElemInj'' ((arrayRead Array_arrayState (fieldRead Hashtable_table h1_bv3112) i_bv3110) = (arrayRead Array_arrayState (fieldRead Hashtable_table h2_bv3163) j_bv3111))|] ==>
    comment ''ElementInjInv_newElemInj'' (i_bv3110 = j_bv3111))"
apply (unfold comment_def)
apply (erule_tac x="this_bv3109" in allE)
apply safe
apply (erule_tac x="i_bv3110" in allE)
apply (erule_tac x="j_bv3111" in allE)
apply (erule_tac x="h1_bv3112" in allE)
apply (erule_tac x="h2_bv3163" in allE)
apply safe
done

lemma Hashtable_containsKey0_3: "([|comment ''ElementInjInvoldElemInj'' (ALL this. (((this : Object_alloc) & (this : Hashtable) & (fieldRead Hashtable_init this)) --> (ALL i j h1 h2. (((0 <= i) & (intless i (fieldRead Array_length (fieldRead Hashtable_table h1))) & (0 <= j) & (intless j (fieldRead Array_length (fieldRead Hashtable_table h2))) & ((arrayRead Array_arrayState (fieldRead Hashtable_table h1) i) ~= null) & ((arrayRead Array_arrayState (fieldRead Hashtable_table h1) i) = (arrayRead Array_arrayState (fieldRead Hashtable_table h2) j))) --> ((i = j) & (h1 = h2))))));
comment ''allocSame'' (Object_alloc_10 = Object_alloc);
comment ''ElementInjInv_newElemInj'' (this_bv3109 : Object_alloc_10);
comment ''ElementInjInv_newElemInj'' (this_bv3109 : Hashtable);
comment ''ElementInjInv_newElemInj'' (fieldRead Hashtable_init this_bv3109);
comment ''ElementInjInv_newElemInj'' (0 <= i_bv3110);
comment ''ElementInjInv_newElemInj'' (intless i_bv3110 (fieldRead Array_length (fieldRead Hashtable_table h1_bv3112)));
comment ''ElementInjInv_newElemInj'' (0 <= j_bv3111);
comment ''ElementInjInv_newElemInj'' (intless j_bv3111 (fieldRead Array_length (fieldRead Hashtable_table h2_bv3163)));
comment ''ElementInjInv_newElemInj'' ((arrayRead Array_arrayState (fieldRead Hashtable_table h1_bv3112) i_bv3110) ~= null);
comment ''ElementInjInv_newElemInj'' ((arrayRead Array_arrayState (fieldRead Hashtable_table h1_bv3112) i_bv3110) = (arrayRead Array_arrayState (fieldRead Hashtable_table h2_bv3163) j_bv3111))|] ==>
    comment ''ElementInjInv_newElemInj'' (h1_bv3112 = h2_bv3163))"
apply (unfold comment_def)
apply (erule_tac x="this_bv3109" in allE)
apply safe
apply (erule_tac x="i_bv3110" in allE)
apply (erule_tac x="j_bv3111" in allE)
apply (erule_tac x="h1_bv3112" in allE)
apply (erule_tac x="h2_bv3163" in allE)
apply safe
done

end
