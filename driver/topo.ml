(* *****************************************************************)
(*                                                                 *)
(*               Verified polyhedral AST generation                *)
(*                                                                 *)
(*                 Nathanaël Courant, Inria Paris                  *)
(*                                                                 *)
(*  Copyright Inria. All rights reserved. This file is distributed *)
(*  under the terms of the GNU Lesser General Public License as    *)
(*  published by the Free Software Foundation, either version 2.1  *)
(*  of the License, or (at your option) any later version.         *)
(*                                                                 *)
(* *****************************************************************)

open Conversions

exception HasCycle

let print_bool_array ff a = Array.iter (fun u -> Format.fprintf ff "%d" (if u then 1 else 0)) a
let print_bool_matrix ff a = Array.iter (fun u -> Format.fprintf ff "%a@." print_bool_array u) a
let print_int_array ff a = Array.iter (fun u -> Format.fprintf ff "%d " u) a

let topo_sort t =
  let n = Array.length t in
  (* Format.printf "Sorting length %d@." n; *)
  let res = Array.make n 0 in
  let used = Array.make n false in
  for i = 0 to n - 1 do
    let rec search j =
      if j = n then begin Format.printf "%d@.%a@.@.%a@." i print_bool_array used print_bool_matrix t; raise HasCycle end;
      if used.(j) then search (j + 1) else begin
        let ok = ref true in
        for k = 0 to n - 1 do
          if j <> k && not used.(k) && t.(j).(k) then ok := false
        done;
        if !ok then j else search (j + 1)
      end
    in
    let j = search 0 in
    used.(j) <- true;
    res.(i) <- j
  done;
  (*  Format.printf "%a@.%a@.@.%a@." print_int_array res print_bool_array used print_bool_matrix t; *)
  res

let coq_toposort l =
  let t = Array.of_list (List.map Array.of_list l) in
  let r = topo_sort t in
  List.map int_to_coqnat (Array.to_list r)
