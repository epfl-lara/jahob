(* proved by CVLC and Spass easily and and E after some time *)
[|
comment ''wonder1'' ((fieldRead Node_con (fieldRead Node_next (fieldRead List_first this))) = ((fieldRead Node_con (fieldRead List_first this)) \<setminus> {(fieldRead Node_data (fieldRead List_first this))}));
comment ''TrueBranch'' ((fieldRead Node_data (fieldRead List_first this)) = o1);
((fieldRead Node_next (fieldRead List_first this)) ~= (fieldRead List_first this));
(List_edge_7 = (% x y. (((x : Node) & (y = (fieldRead (fieldWrite Node_next (fieldRead List_first this) null) x))) | ((x : List) & (y = (fieldRead List_first x))))));
comment ''wonder2'' ((fieldRead Node_con (fieldRead Node_next (fieldRead List_first this))) = ((fieldRead List_content this) \<setminus> {o1}));
(List_content_5 = (% this__6. (fieldRead (fieldWrite Node_con (fieldRead List_first this) {(fieldRead Node_data (fieldRead List_first this))}) (fieldRead List_first this__6))));
(List_content_3 = (% this__5. (fieldRead (fieldWrite Node_con (fieldRead List_first this) {(fieldRead Node_data (fieldRead List_first this))}) (fieldRead (fieldWrite List_first this (fieldRead Node_next (fieldRead List_first this))) this__5))));
(List_edge_2 = (% x y. (((x : Node) & (y = (fieldRead (fieldWrite Node_next (fieldRead List_first this) null) x))) | ((x : List) & (y = (fieldRead (fieldWrite List_first this (fieldRead Node_next (fieldRead List_first this))) x))))))|] ==>
    ((fieldRead List_content_3 this) = ((fieldRead List_content this) \<setminus> {o1}))