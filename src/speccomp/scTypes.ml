type expr = 
            | Int of string
            | Str of string
            | Null of string
            | Field of expr * expr
            | Arr_elm of expr * expr
            | Method of expr * expr * expr list 
            | StaticM of expr * expr list
            | Filter of expr * expr * expr * expr 
            | Reach of expr * expr * expr * expr list
            | BinOp of expr * string * expr
            | Imp of expr * string * expr
            | Not of expr
            | Forall of expr * expr * expr * expr
            | Exists of expr * expr * expr * expr
            | Range of expr * expr * string * expr * expr * expr
            | Map of expr * expr * expr * expr 
