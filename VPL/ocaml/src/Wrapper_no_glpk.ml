type polyhedron

let with_glpk = false

let mk : int -> int -> polyhedron =  fun _ _ -> failwith "GLPK required for C++ raytracing (mk)"

let rm : polyhedron -> unit = fun _ -> failwith "GLPK required for C++ raytracing (rm)"

let set_coeff : polyhedron -> int -> int -> float -> unit = fun _ _ _ _ -> failwith "GLPK required for C++ raytracing (set_coeff)"

let minimize : polyhedron -> unit = fun _ -> failwith "GLPK required for C++ raytracing (minimize)"

let is_empty : polyhedron -> bool = fun _ -> failwith "GLPK required for C++ raytracing (is_empty)"

let is_true : polyhedron -> int -> bool = fun _ _ -> failwith "GLPK required for C++ raytracing (is_true)"

let get_witness_coeff : polyhedron -> int -> int -> float = fun _ _ _ -> failwith "GLPK required for C++ raytracing (get_witness_coeff)"

let set_central_point_coeff: polyhedron -> int -> float -> unit = fun _ _ _ -> failwith "GLPK required for C++ raytracing (set_central_point_coeff)"
