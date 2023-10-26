(** This module allows to tune the algorithms used in the polyhedral operators. *)

(** Type of linear solver for the new minimization.
{ul
	{- [Glpk]: floating point LP binded to the VPL using ocaml-glpk}
	{- [Splx]: rational LP of the VPL}}
*)
type lp = Glpk | Splx

let lp_to_xml : lp -> string
	= function
	| Glpk -> "glpk"
	| Splx -> "splx"

(** Choice of the minimization method.
{ul
	{- [Classic]: classical way that uses LP}
	{- [Raytracing]: New method based on constraint evaluation + LP}}
*)
type min_method = Classic | Raytracing of lp | MHeuristic | Apron (* Apron for tests only *)

(** Choice of the point type.
{ul
	{- [Rat]: Rational points}
	{- [Symbolic]: Rational points with symbolic error}
	{- [Float]: Floating points}}
*)
type scalar = Rat | Symbolic | Float

let scalar_to_string : scalar -> string
	= function
	| Rat -> "Rat"
	| Symbolic -> "Symbolic"
	| Float -> "Float"

let scalar_to_xml : scalar -> string
	= function
	| Rat -> "rat"
	| Symbolic -> "symb"
	| Float -> "float"

(** Choice of the projection method.
{ul
	{- [FM]: classical way that uses the Fourier-Motzkin algorithm}
	{- [Proj_PLP]: method based on Parametric Linear Programming}}
*)
type proj_method = FM | Proj_PLP of scalar | PHeuristic | Proj_Apron

(** Choice of the join method.
{ul
	{- [Baryc]: algorithm based on convex combinations + projection }
	{- [Join_PLP]: method based on Parametric Linear Programming}}
*)
type join_method = Baryc | Join_PLP of scalar | JHeuristic | Join_fromRegions

(** Default choice for minimization. *)
let min : min_method ref = ref (Classic)

let min_to_string : unit -> string
	= fun () ->
	match !min with
	| Classic -> "Classic"
	| Raytracing Glpk -> "Raytracing:Glpk"
	| Raytracing Splx -> "Raytracing:Splx"
	| MHeuristic -> "Heuristic"
	| Apron -> "Apron"

let min_to_xml : unit -> string
	= fun () ->
	match !min with
	| Classic -> "classic"
	| Raytracing _ -> "raytracing"
	| MHeuristic -> "heuristic"
	| Apron -> "apron"

(** Default choice for projection. *)
let proj : proj_method ref = ref (FM)

let proj_to_string : unit -> string
	= fun () ->
	match !proj with
	| FM -> "Fourier_Motzkin"
	| Proj_PLP (scalar) -> "Proj_PLP(" ^ (scalar_to_string scalar) ^ ")"
	| PHeuristic -> "Heuristic"
	| Proj_Apron -> "Proj_Apron"

let proj_to_xml : unit -> string
	= fun () ->
	match !proj with
	| FM -> "fm"
	| Proj_PLP _ -> "plp"
	| PHeuristic -> "heuristic"
	| Proj_Apron -> "apron"

(** Default choice for join. *)
let join : join_method ref = ref (Baryc)

let join_to_string : unit -> string
	= fun () ->
	match !join with
	| Baryc -> "Barycentric"
	| Join_PLP (scalar) -> "Join_PLP(" ^ (scalar_to_string scalar) ^ ")"
	| JHeuristic -> "Heuristic"
	| Join_fromRegions -> "Join_fromRegions"

let join_to_xml : unit -> string
	= fun () ->
	match !join with
	| Baryc -> "barycentric"
	| Join_PLP _ -> "plp"
	| JHeuristic -> "heuristic"
	| Join_fromRegions -> "plp_regions"

(** If set to true, the Handelman linearization will loop, meaning that it will iterate on the last result obtained.
The linearization of polynomial [g] on the starting polyhedron [P] will give
H_0 = linearize(P,g)
H_i = linearize(H_(i-1), g)
*)
let handelman_loop : bool ref = ref false

(** Sets a timeout to the Handelman linearization.
Combined to {!val:handelman_loop}, the linearization returns the last result found. *)
let handelman_timeout : int option ref = ref (Some 10)

(** Sets a normalization constant. If [None], there will be no normalization. *)
let handelman_normalize : Scalar.Rat.t option ref = ref None

(** If set to [Some n], the parametric simplex will be distributed over n processes. *)
let distributed_plp : int option ref = ref None

(** If set to [true], the system of equalities of a polyhedron will be in row echelon form. *)
let row_echelon_equalities : bool ref = ref true

(** *)
type plp_method = Adj_Raytracing | Adj_Raytracing_min | Greedy

let plp : plp_method ref = ref Adj_Raytracing

let plp_to_string : unit -> string
	= fun () ->
	match !plp with
	| Adj_Raytracing -> "Raytracing"
	| Adj_Raytracing_min -> "Raytracing with minimal adjacency test"
	| Greedy -> "Greedy"

let plp_to_xml : unit -> string
	= fun () ->
	match !plp with
	| Adj_Raytracing -> "raytracing"
	| Adj_Raytracing_min -> "raytracing_min"
	| Greedy -> "greedy"

(** Enabling of log traces. *)
let log_trace : bool ref = ref true

(** If [true], put sum lambda = 1 as normalization constraint in the projection via PLP. *)
let sum_lambda_1 : bool ref = ref false
