(benchmark vc0.smt
  :source {
	(
          (ALL (anyArray::obj) (indexI::int). (
             (((anyArray :: obj) ~= (arrayX :: obj)) & ((indexI :: int) ~= (indexJ :: int))) --> 
             (((arrayRead (arrayWrite Array_arrayState arrayX indexJ valueX) anyArray indexI) :: obj) = 
              ((arrayRead (Array_arrayState :: (obj => ((int => obj)))) anyArray indexI) :: obj))))
          ==>
	    (arrayRead (arrayWrite Array_arrayState arrayX indexJ valueX) arrayY indexK) = valueX
        )
   }
  :logic AUFLIA

  :extrasorts (Obj)
  :extrasorts (globalArrayObj)
  :extrafuns ((array_arrayState globalArrayObj))
  :extrafuns ((arrayRead globalArrayObj Obj Int Obj))
  :extrafuns ((valueX Obj))
  :extrafuns ((arrayY Obj))
  :extrafuns ((arrayX Obj))
  :extrafuns ((indexK Int))
  :extrafuns ((arrayRead__smt_2 Obj))
  :extrafuns ((arrayRead__smt_1 Obj))
  :extrafuns ((indexJ Int))

  :assumption (or (not (= arrayX arrayY)) (not (= indexJ indexK)) (= arrayRead__smt_2 valueX))
  :assumption (or (and (= arrayX arrayY) (= indexJ indexK)) (= arrayRead__smt_2 (arrayRead array_arrayState arrayY indexK)))
  :assumption (forall (?indexI Int) (forall (?anyArray Obj) 
                (and (or (= ?anyArray arrayX) (= ?indexI indexJ) (= arrayRead__smt_1 (arrayRead array_arrayState ?anyArray ?indexI))) 
                     (or (not (= arrayX ?anyArray)) (not (= indexJ ?indexI)) (= arrayRead__smt_1 valueX)) 
                     (or (and (= arrayX ?anyArray) (= indexJ ?indexI)) (= arrayRead__smt_1 (arrayRead array_arrayState ?anyArray ?indexI))))))

  :formula    (not (= arrayRead__smt_2 valueX))

  :status     unknown
)