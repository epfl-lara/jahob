(benchmark vc1.smt
  :source {
	([|((ArrayList_csize :: int) = (ArrayList_size :: int));
	((ArrayList_content :: ((int * obj)) set) = (\{p__6. (EX (i::int) (n::obj). (((p__6 :: (int * obj)) = ((i, n) :: (int * obj))) & (((0 :: int) <= (i :: int)) & (intless i (ArrayList_size :: int)) & ((n :: obj) = ((arrayRead (Array_arrayState :: (obj => (int => obj))) (ArrayList_elementData :: obj) i) :: obj)))))\} :: ((int * obj)) set));
	((ArrayList_init :: bool) = (((ArrayList_elementData :: obj) ~= (null :: obj)) :: bool));
	(ArrayList_init :: bool);
	((~(ArrayList_init :: bool)) --> (((ArrayList_size :: int) = (0 :: int)) & ((ArrayList_elementData :: obj) = (null :: obj)) & ((ArrayList_hidden :: obj set) = (\{\} :: obj set))));
	((ArrayList_init :: bool) --> (((0 :: int) <= (ArrayList_size :: int)) & ((ArrayList_size :: int) <= ((fieldRead (Array_length :: (obj => int)) (ArrayList_elementData :: obj)) :: int))));
	((ArrayList_init :: bool) --> ((ArrayList_elementData :: obj) : (ArrayList_hidden :: obj set)));
	((ArrayList_init :: bool) --> (ALL (i::int). ((((0 :: int) <= (i :: int)) & (intless i (ArrayList_size :: int))) --> (((arrayRead (Array_arrayState :: (obj => (int => obj))) (ArrayList_elementData :: obj) i) :: obj) ~: (ArrayList_hidden :: obj set)))));
	((ArrayList_init :: bool) --> (ALL (i::int). ((((0 :: int) <= (i :: int)) & (intless i (ArrayList_size :: int))) --> (((arrayRead (Array_arrayState :: (obj => (int => obj))) (ArrayList_elementData :: obj) i) :: obj) : (Object_alloc :: obj set)))));
	((elem :: obj) : (Object :: obj set));
	((elem :: obj) : (Object_alloc :: obj set));
	((elem :: obj) ~: (ArrayList_hidden :: obj set));
	((-1 :: int) <= (tmp_1_5 :: int));
	(intless (tmp_1_5 :: int) (ArrayList_csize :: int));
	(((tmp_1_5 :: int) ~= (-1 :: int)) --> ((((tmp_1_5 :: int), (elem :: obj)) :: (int * obj)) : (ArrayList_content :: ((int * obj)) set)));
	(((tmp_1_5 :: int) ~= (-1 :: int)) --> (~(EX (i::int). ((intless i (tmp_1_5 :: int)) & (((i, (elem :: obj)) :: (int * obj)) : (ArrayList_content :: ((int * obj)) set))))));
	(((tmp_1_5 :: int) = (-1 :: int)) --> (~(EX (i::int). (((i, (elem :: obj)) :: (int * obj)) : (ArrayList_content :: ((int * obj)) set)))));
	((ArrayList_init :: bool) --> (ALL (i::int). ((((0 :: int) <= (i :: int)) & (intless i (ArrayList_size :: int))) --> (((arrayRead (Array_arrayState :: (obj => (int => obj))) (ArrayList_elementData :: obj) i) :: obj) : (Object_alloc_6 :: obj set)))));
	((Object_alloc :: obj set) \<subseteq> (Object_alloc_6 :: obj set));
	(~(((0 :: int) <= (tmp_1_5 :: int)) :: bool))|] ==>
	    (~(EX (i::int). (((i, (elem :: obj)) :: (int * obj)) : (ArrayList_content :: ((int * obj)) set)))))
   }
  :logic AUFLIA

  :extrasorts (Obj)
  :extrasorts (globalArrayObj)
  :extrafuns ((arrayArrayState globalArrayObj))
  :extrafuns ((arrayRead globalArrayObj Obj Int Obj))
  :extrafuns ((null Obj))
  :extrafuns ((v_1001Sk_smt_4 Int))
  :extrafuns ((iSk_smt_5 Int))
  :extrafuns ((arrayLength Obj Int))
  :extrapreds ((object Obj))
  :extrapreds ((arrayListHidden Obj))
  :extrafuns ((arrayListSize Int))
  :extrafuns ((tmp_1_5 Int))
  :extrafuns ((arrayListElementData Obj))
  :extrapreds ((objectAlloc Obj))
  :extrapreds ((objectAlloc_6 Obj))
  :extrafuns ((elem Obj))
  :extrafuns ((iSk_smt_6 Int))

  :assumption (not (= arrayListElementData null))
  :assumption (or (not (= arrayListElementData null)) (and (= arrayListSize 0) (= arrayListElementData null) (forall (?v_1002 Obj) (not (arrayListHidden ?v_1002)))))
  :assumption (or (= arrayListElementData null) (and (<= 0 arrayListSize) (<= arrayListSize (arrayLength arrayListElementData))))
  :assumption (or (= arrayListElementData null) (arrayListHidden arrayListElementData))
  :assumption (or (= arrayListElementData null) (forall (?i Int) (or (< ?i 0) (<= arrayListSize ?i) (not (arrayListHidden (arrayRead arrayArrayState arrayListElementData ?i))))))
  :assumption (or (= arrayListElementData null) (forall (?i Int) (or (< ?i 0) (<= arrayListSize ?i) (objectAlloc (arrayRead arrayArrayState arrayListElementData ?i)))))
  :assumption (object elem)
  :assumption (objectAlloc elem)
  :assumption (not (arrayListHidden elem))
  :assumption (<= (~ 1) tmp_1_5)
  :assumption (< tmp_1_5 arrayListSize)
  :assumption (or (= tmp_1_5 (~ 1)) (and (= tmp_1_5 iSk_smt_6) (= elem (arrayRead arrayArrayState arrayListElementData iSk_smt_6)) (<= 0 iSk_smt_6) (< iSk_smt_6 arrayListSize)))
  :assumption (or (= tmp_1_5 (~ 1)) (forall (?i Int) (or (<= tmp_1_5 ?i) (forall (?v_999 Int) (or (not (= ?i ?v_999)) (not (= elem (arrayRead arrayArrayState arrayListElementData ?v_999))) (< ?v_999 0) (<= arrayListSize ?v_999))))))
  :assumption (or (not (= tmp_1_5 (~ 1))) (forall (?v_1000 Int) (forall (?i Int) (or (not (= ?i ?v_1000)) (not (= elem (arrayRead arrayArrayState arrayListElementData ?v_1000))) (< ?v_1000 0) (<= arrayListSize ?v_1000)))))
  :assumption (or (= arrayListElementData null) (forall (?i Int) (or (< ?i 0) (<= arrayListSize ?i) (objectAlloc_6 (arrayRead arrayArrayState arrayListElementData ?i)))))
  :assumption (forall (?v_1016 Obj) (or (not (objectAlloc ?v_1016)) (objectAlloc_6 ?v_1016)))
  :assumption (< tmp_1_5 0)

  :formula    (and (= iSk_smt_5 v_1001Sk_smt_4) (= elem (arrayRead arrayArrayState arrayListElementData v_1001Sk_smt_4)) (<= 0 v_1001Sk_smt_4) (< v_1001Sk_smt_4 arrayListSize))

  :status     unknown
)