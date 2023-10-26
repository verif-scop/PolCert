(*
(* path to log file as a relative path from "vpl2" *)
let relative_record = "exp/record"
let relative_logfile =  "log"
let relative_tracerunner_input = "tracerunner_input"

let find_record() =
  (* get_root searches for directory [relative_record] in directory [root]
     otherwise, into parent directories...*)
  let rec get_root root =
    Sys.chdir root;
    try
      if (Sys.is_directory relative_record) then
        Sys.getcwd()
      else
        raise (Sys_error "")
    with
      Sys_error _ -> get_root (Filename.parent_dir_name)
  in let root = get_root (Filename.dirname Sys.executable_name) in
     Filename.concat root relative_record;;

let record = find_record()    
let log_file = Filename.concat relative_record relative_logfile
let tracerunner_input = Filename.concat relative_record relative_tracerunner_input;;

*)

let log_file = ref "/tmp/vpl.log"

let mail_sender = "/usr/sbin/sendmail"

let sage_log = "/tmp/vpl_sage.sage"
