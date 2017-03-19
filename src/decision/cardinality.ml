(** Simple Cardinality Prover **)
open Form
open FormUtil

let is_useful_dp _ ((assumptions, goal) : sequent) : bool =
  let rec contains_card (f : form) : bool =
    match f with
      | Const Card | Const Cardeq | Const Cardleq | Const Cardgeq -> true
      | App(f', fs) -> contains_card f' || List.exists contains_card fs
      | Binder(_, _, f')
      | TypedForm(f', _) -> contains_card f'
      | _ -> false
  in
    List.exists contains_card assumptions || contains_card goal

let clean ((assumptions, goal) : sequent) : sequent =
  let rec normalize (f : form) : form =
    match f with
      | App(Const Eq, [f1; App(Const Card, _) as f2])
      | App(Const Eq, [f1; TypedForm(App(Const Card, _) as f2, _)]) ->
	  let f1 = normalize f1 in
	  let f2 = normalize f2 in
	    (match f1 with
	       | App(Const Card, _) -> 
		   (** Prevent infinite loops *)
		   App(Const Eq, [f1; f2])
	       | _ -> App(Const Eq, [f2; f1]))
      | App(Const Comment, [_; f'])
      | TypedForm(f', _) ->
	  normalize f'
      | App(f', fs) ->
	  App(normalize f', List.map normalize fs)
      | Binder(b, t, f') ->
	  Binder(b, t, normalize f')
      | _ -> f
  in
  let rec simplify (f : form) : form =
    match f with
      | App(Const FieldRead, [App(Const FieldWrite, [f1; f2; f3]); f4])
	  when (f2 = f4) -> 
	  simplify f3
      | App(f, fs) ->
	  App(simplify f, List.map simplify fs)
      | Binder(b, t, f') ->
	  Binder(b, t, simplify f')
      | _ -> f
  in
  let rec iter (f : form) : form =
    let f' = simplify (normalize f) in
      if f' = f then f'
      else iter f'
  in
    (List.map iter assumptions, iter goal)

let rec find_def (f : form) (fs : form list) : form option =
  match fs with
    | [] -> None
    | hd :: tl ->
	match hd with
	  | App(Const Eq, [f1; f2]) when (f = f1) ->
	      Some f2
	  | App(Const Eq, [f1; f2]) when (f = f2) -> 
	      Some f1
	  | _ -> find_def f tl

let rec find_pair
    (finder : form -> (form * form) option) 
    (fs : form list) : (form * form) option =
  match fs with
    | [] -> None
    | hd :: tl ->
	let result = finder hd in
	  match result with
	    | Some _ -> result
	    | _ -> find_pair finder tl

let find_x_e_minus (y : form) (fs : form list) : (form * form) option =
  let minus_finder (f : form) : (form * form) option =
    match f with
      | App(Const Eq, 
	    [App(Const Minus, [y1; App(Const FiniteSetConst, [e])]); x])
      | App(Const Eq, 
	    [x; App(Const Minus, [y1; App(Const FiniteSetConst, [e])])])
	  when (y = y1) ->
	  Some (x, e)
      | _ -> None
  in
    find_pair minus_finder fs

let find_x_e_union (y : form) (fs : form list) : (form * form) option =
  let plus_finder (f : form) : (form * form) option =
    match f with
      | App(Const Eq, 
	    [App(Const Cup, [App(Const FiniteSetConst, [e]); y1]); x])
      | App(Const Eq, 
	    [App(Const Cup, [y1; App(Const FiniteSetConst, [e])]); x])
      | App(Const Eq, 
	    [x; App(Const Cup, [App(Const FiniteSetConst, [e]); y1])])
      | App(Const Eq, 
	    [x; App(Const Cup, [y1; App(Const FiniteSetConst, [e])])])
	  when (y = y1) ->
	  Some (x, e)
      | _ -> None
  in
    find_pair plus_finder fs

let find_card (f : form) (fs : form list) : form option =
  let rec find (fs : form list) : form option =
    match fs with
      | [] -> None
      | hd :: tl ->
	  match hd with
	    | App(Const Eq, [App(Const Card, [f1]); f2]) ->
		Some f2
	    | _ -> find tl
  in
    find fs

let card_X_is_c_minus_1 (x : form) (c : form) (assumptions : form list) : bool =
  (** 
      [| card Y = c;
         X = Y - {e};
         e : Y        |] ==> card X = c - 1
  **)
  match find_def x assumptions with
    | Some xdef ->
	(match xdef with
	   | App(Const Minus, [y; App(Const FiniteSetConst, [e])]) ->
	       List.mem (mk_eq (mk_card y, c)) assumptions &&
		 List.mem (mk_elem (e, y)) assumptions
	   | _ -> false) 
    | None -> false

let card_Y_is_c_minus_1 (y : form) (c : form) (assumptions : form list) : bool =
  (** 
      [| card X = c;
         X = Y Un {e};
         e ~: Y        |] ==> card Y = c - 1
  **)
  match find_x_e_union y assumptions with
    | Some (x, e) ->
	List.mem (mk_eq (mk_card x, c)) assumptions &&
	  List.mem (mk_not (mk_elem (e, y))) assumptions
    | None -> false

let card_X_is_c_plus_1 (x : form) (c : form) (assumptions : form list) : bool =
  (** 
      [| card Y = c;
         X = Y \<setunion> {e};
         e ~: Y                 |] ==> card X = c + 1
  **)
  match find_def x assumptions with
    | Some xdef ->
	(match xdef with
	   | App(Const Cup, [App(Const FiniteSetConst, [e]); y])
	   | App(Const Cup, [y; App(Const FiniteSetConst, [e])]) ->
	       List.mem (mk_eq (mk_card y, c)) assumptions &&
		 List.mem (mk_not (mk_elem (e, y))) assumptions
	   | _ -> false) 
    | None -> false
	
let card_Y_is_c_plus_1 (y : form) (c : form) (assumptions : form list) : bool =
  (** 
      [| card X = c;
         X = Y - {e};
         e : Y        |] ==> card Y = c + 1
  **)
  match find_x_e_minus y assumptions with
    | Some (x, e) ->
	List.mem (mk_eq (mk_card x, c)) assumptions &&
	  List.mem (mk_elem (e, y)) assumptions
    | None -> false

let card_Y_is_c_union (y : form) (c : form) (assumptions : form list) : bool =
  (** 
      [| card X = c + 1;
         X = Y Un {e};
         e ~: Y          |] ==> card Y = c
  **)
  match find_x_e_union y assumptions with
    | Some (x, e) ->
	List.mem (mk_eq (mk_card x, mk_plus (c, mk_int 1))) assumptions && 
	  List.mem (mk_not (mk_elem (e, y))) assumptions
    | _ -> false

let card_X_is_c_union (x : form) (c : form) (assumptions : form list) :  bool =
  (** 
      [| card Y = c - 1;
         X = Y Un {e};
         e ~: Y          |] ==> card X = c
  **)
  match find_def x assumptions with
    | Some xdef ->
	(match xdef with
	   | App(Const Cup, [App(Const FiniteSetConst, [e]); y])
	   | App(Const Cup, [y; App(Const FiniteSetConst, [e])]) ->
	       List.mem (mk_eq (mk_card y, (mk_minus (c, mk_int 1))))
		 assumptions &&
		 List.mem (mk_not (mk_elem (e, y))) assumptions
	   | _ -> false)
    | _ -> false

let card_Y_is_c_minus (y : form) (c : form) (assumptions : form list) : bool =
  (** 
      [| card X = c - 1;
         X = Y - {e};
         e : Y           |] ==> card Y = c
  **)
  match find_x_e_minus y assumptions with
    | Some (x, e) ->
	List.mem (mk_eq (mk_card x, mk_minus (c, mk_int 1))) assumptions && 
	  List.mem (mk_elem (e, y)) assumptions
    | _ -> false

let card_X_is_c_minus (x : form) (c : form) (assumptions : form list) : bool =
  (** 
      [| card Y = c + 1;
         X = Y - {e};
         e : Y           |] ==> card X = c
  **)
  match find_def x assumptions with
    | Some xdef ->
	(match xdef with
	   | App(Const Minus, [y; App(Const FiniteSetConst, [e])]) ->
	       List.mem (mk_eq (mk_card y, mk_plus (c, mk_int 1))) 
		 assumptions && 
		 List.mem (mk_elem (e, y)) assumptions
	   | _ -> false)
    | _ -> false

let e_in_Y_card_Y (x : form) (y : form) (assumptions : form list) : bool =
  (** 
      [| card Y = c;
         X = Y - {e};
         card X = c - 1 |] ==> e : Y
  **)
  match find_card y assumptions with
    | Some c ->
	List.mem (mk_eq (mk_card x, mk_minus (c, mk_int 1))) assumptions
    | _ -> false

let e_in_Y_card_X (x : form) (y : form) (assumptions : form list) : bool =
  (** 
      [| card X = c;
         X = Y - {e};
         card Y = c + 1 |] ==> e : Y
  **)
  match find_card x assumptions with
    | Some c ->
	List.mem (mk_eq (mk_card y, mk_plus (c, mk_int 1))) assumptions
    | _ -> false

let e_not_in_Y_card_Y (x : form) (y : form) (assumptions : form list) : bool =
  (** 
      [| card Y = c;
         X = Y Un {e};
         card X = c + 1 |] ==> e ~: Y
  **)
  match find_card y assumptions with
    | Some c ->
	List.mem (mk_eq (mk_card x, mk_plus (c, mk_int 1))) assumptions
    | _ -> false

let e_not_in_Y_card_X (x : form) (y : form) (assumptions : form list) : bool =
  (** 
      [| card X = c;
         X = Y Un {e};
         card Y = c - 1 |] ==> e ~: Y
  **)
  match find_card x assumptions with
    | Some c ->
	List.mem (mk_eq (mk_card y, mk_minus (c, mk_int 1))) assumptions
    | _ -> false

let decide_sq (s : sequent) : bool option =
  let decide ((assumptions, goal) : sequent) : bool =
    match goal with
      | App(Const Eq, [App(Const Card, [x]); Const (IntConst 0)]) ->
	  (** card X = 0 **)
	  (x = Const EmptysetConst) ||
	    List.mem (mk_eq (x, mk_emptyset)) assumptions
      | App(Const Eq, [x; Const EmptysetConst]) ->
	  (** X = {} **)
	  List.mem (mk_eq (mk_card x, mk_int 0)) assumptions
      | App(Const Eq, [App(Const Card, [f]); 
		       App(Const Minus, [c; Const (IntConst 1)])]) ->
	  (** card f = c - 1 **)
	  (card_X_is_c_minus_1 f c assumptions || 
	     card_Y_is_c_minus_1 f c assumptions)
      | App(Const Eq, [App(Const Card, [f]); 
		       App(Const Plus, [Const (IntConst 1); c])])
      | App(Const Eq, [App(Const Card, [f]); 
		       App(Const Plus, [c; Const (IntConst 1)])]) ->
	  (** card f = c + 1 **)
	  (card_X_is_c_plus_1 f c assumptions || 
	     card_Y_is_c_plus_1 f c assumptions)
      | App(Const Eq, [App(Const Card, [f]) as c1; c2]) ->
	  (** card f = c **)
	  (c1 = c2 ||
	      card_Y_is_c_union f c2 assumptions ||
	      card_X_is_c_union f c2 assumptions ||
	      card_Y_is_c_minus f c2 assumptions || 
	      card_X_is_c_minus f c2 assumptions)
      | App(Const Elem, [e; y]) ->
	  (** e : Y **)
	  (match find_x_e_minus y assumptions with
	     | Some (x, e1) when (e = e1) ->
		 (** X = Y - {e} **)
		 (e_in_Y_card_Y x y assumptions ||
		    e_in_Y_card_X x y assumptions)
	     | _ -> false)
      | App(Const Not, [App(Const Elem, [e; y])]) ->
	  (** e ~: Y **)
	  (match find_x_e_union y assumptions with
	     | Some (x, e1) when (e = e1) ->
		 (** X = Y Un {e} **)
		 (e_not_in_Y_card_Y x y assumptions ||
		    e_not_in_Y_card_X x y assumptions)
	     | _ -> false)
      | _ -> false
  in
  let result = decide (clean s) in
    if result then Some result else None
    
