theory "testinv1_Hashtable-lemmas" = Jahob:

lemma preserving: "[|
comment ''previouslyHad'' ((fieldRead Hashtable_content this) \<subseteq> ((fieldRead Hashtable_content_10 this) Un {p. (EX k v. ((p = (k, v)) & (EX j. ((i_11 <= j) & (intless j (fieldRead Array_length tmp_1_9)) & ((k, v) : (fieldRead AssocList_content (arrayRead Array_arrayState tmp_1_9 j)))))))}));
comment ''Hashtable.rehash_bucket_PostconditionInCall'' ((fieldRead Hashtable_content_4 this) = ((fieldRead Hashtable_content_10 this) Un (fieldRead AssocList_content (arrayRead Array_arrayState tmp_1_9 i_11))));
comment ''breakdown2'' ({p. (EX j. ((i_11 <= j) & (intless j (fieldRead Array_length tmp_1_9)) & (p : (fieldRead AssocList_content (arrayRead Array_arrayState tmp_1_9 j)))))} \<subseteq> ((fieldRead AssocList_content (arrayRead Array_arrayState tmp_1_9 i_11)) Un {p. (EX j. (((intplus i_11 1) <= j) & (intless j (fieldRead Array_length tmp_1_9)) & (p : (fieldRead AssocList_content (arrayRead Array_arrayState tmp_1_9 j)))))}))
|] ==>
    ((fieldRead Hashtable_content this) \<subseteq> ((fieldRead Hashtable_content_4 this) Un {p. (EX k v. ((p = (k, v)) & (EX j. (((intplus i_11 1) <= j) & (intless j (fieldRead Array_length tmp_1_9)) & ((k, v) : (fieldRead AssocList_content (arrayRead Array_arrayState tmp_1_9 j)))))))}))"
sorry (* needs Spass *)

end
