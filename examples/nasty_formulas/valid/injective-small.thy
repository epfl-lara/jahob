[|
(List_edge = (% x y. (((x : Node) & (y = (fieldRead Node_next x))) | ((x : List) & (y = (fieldRead List_first x))))));
comment ''injectiveStill'' (ALL x1 x2 y. (((y ~= null) & (List_edge x1 y) & (List_edge x2 y)) --> (x1 = x2)));
(List_edge_6 = (% x y. (((x : Node) & (y = (fieldRead (fieldWrite (fieldWrite Node_next (fieldRead List_first this) null) (fieldRead Node_next (fieldRead List_first this)) null) x))) | ((x : List) & (y = (fieldRead List_first x))))));
(ALL n. (~(List_edge_6 n (fieldRead Node_next (fieldRead List_first this)))));
(ALL n. (~(List_edge_6 n (fieldRead Node_next (fieldRead Node_next (fieldRead List_first this))))));
(y ~= null);
(List_edge_6 x1 y);
(List_edge_6 x2 y)|] ==>
    comment ''injectiveStill2'' (x1 = x2)