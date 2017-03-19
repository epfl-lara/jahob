(** Common Jahob definitions *)


(** String used for padding by all Jahob printing. Identation mamagement is
    left free to each implementation. *)
let padding_string = ref ""

(** Set the value of the padding string. Be careful since it can mess up
    the identation management of printing modules. *)
let set_pad s = padding_string := s

(** Set parseall to true if you want all methods in the given files to be
    parsed . *)
let parseall = ref false

type analysis_task = {
  task_lemmas : (string * string) list; (* (class,ident) list of lemmas *)
  task_methods : (string * string) list; (* (class,ident) list of methods *)
  task_classes : string list;
}

type source_pos = {
  pos_class : string;
  pos_method : string;
  pos_place : string;
}

let string_of_pos (pos : source_pos) : string =
  "[" ^ pos.pos_class ^ "." ^ pos.pos_method ^ ", " ^ pos.pos_place ^ "]"

let identlike_pos (pos : source_pos) : string =
  let add s = if s="" then "" else "_" ^ s in
    pos.pos_class ^ "_" ^ pos.pos_method ^ add pos.pos_place

(** The unknown position: unknown class, method and empty place. *)
let unknown_pos = {
  pos_class = "UnknownClass";
  pos_method = "UnknownMethod";
  pos_place = "";
}

(** The empty task. *)
let task_is_empty (task : analysis_task) : bool =
  task.task_lemmas = [] &&
  task.task_methods = [] &&
  task.task_classes = []

let method_is_relevant 
    ((cname,mname) : string * string)
    (task : analysis_task) : bool =
  !parseall ||
  List.mem (cname,mname) task.task_methods ||
  List.mem cname task.task_classes

let class_is_relevant
    (cname : string)
    (task : analysis_task) : bool = 
  List.mem cname task.task_classes

(** {6 These are useful to deal with command-line options} *)

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type options_t = string StringMap.t

(** [merge_opts default provided] merges the two mappings [default] and
    [provided]. When a key appears in both [default] and [provided], the
    associated value in the result is the value found in [provided]. *)
let merge_opts (default:options_t) (provided:options_t) : options_t = 
  StringMap.fold (fun key value oldmap -> StringMap.add key value oldmap) provided default

(** transforms a list of [(a1, b1);(a2, b2);...] in a maping [a1 => b1 ; a2 => b2 ; ....] *)
let map_of_list : (string*string) list -> options_t = 
  ListLabels.fold_left ~f:(fun m (a,b) -> StringMap.add a b m) ~init:StringMap.empty

(** [glag_positive ~o flag] is [true] iff [flag] appear as a key in [o], with an associated value different from "no". *)
let flag_positive ~(o:options_t) (flag:string) : bool = 
  try 
    not (StringMap.find flag o = "no")
  with
    | Not_found -> false

let get_option (options : options_t) (option_name : string) : string = 
  StringMap.find option_name options

let string_of_options (o:options_t) : string = 
 String.concat ":" (StringMap.fold (fun key value s -> (key ^ "=" ^ value) :: s) o [])

let split_equal (o:options_t) (s:string) = 
  match Str.split (Str.regexp "=") s with
    | [a] -> StringMap.add a "" o
    | [a;b] -> StringMap.add a b o
    | _ -> failwith "expected : opt or opt=value"

let options_of_string (opt_string : string) : options_t = 
  ListLabels.fold_left ~f:split_equal ~init:(StringMap.empty) 
    (Str.split (Str.regexp ":") opt_string)


let rec n_first n = function
  | [] -> []
  | l when n=0 -> []
  | x::suite -> x::(n_first (n-1) suite)

