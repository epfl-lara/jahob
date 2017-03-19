external fork_with_pgid : unit -> int = "unix_fork_with_pgid"

open Unix

let rec safe_dup fd =
  let new_fd = dup fd in
  if new_fd <> stdin && new_fd <> stdout && new_fd <> stderr then
    new_fd
  else begin
    let res = safe_dup fd in
    close new_fd;
    res
  end

let safe_close fd =
  try close fd with Unix_error(_,_,_) -> ()

let perform_redirections new_stdin new_stdout new_stderr =
  let newnewstdin = safe_dup new_stdin in
  let newnewstdout = safe_dup new_stdout in
  let newnewstderr = safe_dup new_stderr in
  safe_close new_stdin;
  safe_close new_stdout;
  safe_close new_stderr;
  dup2 newnewstdin stdin; close newnewstdin;
  dup2 newnewstdout stdout; close newnewstdout;
  dup2 newnewstderr stderr; close newnewstderr

let create_process_with_pgid cmd args clean_child clean_parent new_stdin new_stdout new_stderr =
  match fork_with_pgid() with
    0 ->
      begin try
        perform_redirections new_stdin new_stdout new_stderr;
	clean_child ();
        execvp cmd args
      with _ ->
        exit 127
      end
  | id -> clean_parent (); id


let fork_in_out () =
  let in_read, in_write = pipe () in
  let out_read, out_write = pipe () in
  let _ = flush_all () in
  let pid = fork () in
  let inchan, outchan, toclose = 
    match pid with
    | 0 -> 
	in_channel_of_descr out_read,
	out_channel_of_descr in_write,
	[in_read; out_write]
    | pid ->
	in_channel_of_descr in_read,
	out_channel_of_descr out_write,
	[out_read; in_write]
  in 
  List.iter close toclose;
  pid, inchan, outchan

