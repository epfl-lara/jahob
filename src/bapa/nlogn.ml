
let _ = print_string "Here we go!\n"

(** Check if 2^n <= (n+1)^d by taking log of both sides *)
let small_n (d : int) (n : int) : bool =
  let d1 = float_of_int d in
  let n1 = float_of_int n in
    n1 *. log 2.0 <= d1 *. log (n1 +. 1.0)

(** compute the largest n such that small_n d n  *)
let n_over_logn_inv (d : int) : int = 
  let rec search a b =
    (* pre "a <= b & 
            small_n d a";
    *)
    if b <= a + 1 then
      if small_n d b then b 
      else a
    else 
      let c = (a + b) / 2 in
	if small_n d c then search c b
	else search a c
  in
  let d1 = float_of_int d in
  let a0 = d1 *. log d1 in
  let b0 = 2.0 *. d1 *. (1.0 +. log d1) in
    search (int_of_float 0.0) (int_of_float b0)

(** Check if 2^n <= (n-1)*n^(d-1) by taking log of both sides *)
let small_n2 (d : int) (n : int) : bool =
  let d1 = float_of_int d in
  let n1 = float_of_int n in
    n1 *. log 2.0 <= log (n1 -. 1.0) +. (d1 -. 1.0) *. log n1

(** compute the largest n such that small_n2 d n   *)
let n_over_logn_inv2 (d : int) : int = 
  let rec search a b =
    (* pre "a <= b & 
            small_n d a";
    *)
    if b <= a + 1 then
      if small_n2 d b then b 
      else a
    else 
      let c = (a + b) / 2 in
	if small_n2 d c then search c b
	else search a c
  in
  let d1 = float_of_int d in
  let a0 = d1 *. log d1 in
  let b0 = 2.0 *. d1 *. (1.0 +. log d1) in
    search (int_of_float 0.0) (int_of_float b0)

let find_sparseness_bound (d : int) =
  if d <= 3 then d
  else 
    n_over_logn_inv d

let find_sparseness_bound2 (d : int) =
  if d <= 3 then d
  else if d = 4 then 5
  else if d = 5 then 7
  else if d = 6 then 9
  else n_over_logn_inv2 d

(*
let rec print_bound (a : int) (b : int) = 
  if (a > b) then ()
  else 
    let n0 = find_sparseness_bound a in
    let n = find_sparseness_bound2 a in
    let _ = print_int a in
    let _ = print_string ", " in
    let _ = print_int n0 in
    let _ = print_string ", " in
    let _ = print_int n in
    let _ = print_string (if n < n0 then " <-- " else "") in
    let _ = print_string "\n" in
      print_bound (a+1) b

let _ = print_bound 1 100
*)
