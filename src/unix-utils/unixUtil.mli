open Unix

val create_process_with_pgid :
  string -> string array -> (unit -> unit) -> (unit -> unit) -> file_descr -> file_descr -> file_descr -> int

val fork_in_out : 
    unit -> int * in_channel * out_channel
