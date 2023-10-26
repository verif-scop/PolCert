open Vpl;;
open Calculator;;
open Notations;;

(*****************************)
(****** Using operators ******)
(*****************************)
(* Parsing a polyhedron: constraints are separated by ','. *)
let p1 = parse "x >= 0, x <= 1, y >= -10, x + y <= 3, x + y < 25, z > 2y , z <= 35";;

(* Printing the minimized representation. *)
print p1;;

(* If Sage is installed and the polyhedron has <= 3 dimensions, you can plot it. (EXPERIMENTAL) *)
show p1;;

(* Adding a constraint to p1.
&& is a notation for operator meet. *)
let p2 = p1 && (parse "x - 2y <= 2");;

(* Projecting variable z from p2.
|- is a notation for operator proj. *)
let p3 = p2 |- "z" ;;

print p3;;

(* When showing a polyhedron, you can specify which variables you want to see. It will project others. *)
show ~vars:"x;y" p2;;

(* The previous plot should give the same result as the following (maybe with a change of variables). *)
show p3;;

(* Another polyhedron *)
let p4 = parse "x + 2y <= 7, 2y >= x + 1, 3x >= y + 1";;

(* Convex hull of p3 and p4
|| is a notation for operator join *)
let p5 = p3 || p4;;

print p5;;
show p5;;

(*****************************)
(**** Selecting Algorithm ****)
(*****************************)

(* You can specify the algorithm you want for operators (see src/Flags.ml)
For instance, to use Parametric Linear Programming (PLP) for the convex hull: *)
Flags.join := Flags.Join_PLP (Flags.Float);;
(* Flags.Float indicates that the points used along the PLP algorithm are floating points. *)

(* Let's run the same convex hull, with PLP: *)
let p6 = p3 || p4;;

(* We test that p5 = p6.
VPL.leq is tests inclusion. *)
VPL.leq p5 p6;;
VPL.leq p6 p5;;
(* Hopefully, the result should be true in both cases. *)

(*****************************)
(******* Using Traces ********)
(*****************************)

(* Traces may be printed during execution (see src/misc/Debug.ml). 
They can be enabled separatly in several modules. 
The level of details can also be tuned (chosen from [MOutput ; MInput ; Title ; Normal ; Detail].
For instance, to enable the traces in module PLPCore, without details : *)
Join.Debug.enable DebugTypes.([MOutput ; MInput ; Title]);;
PLPCore.Debug.enable DebugTypes.([MOutput ; MInput ; Title]);;

(* By default, traces are stored in a file. To print them on the fly, type *)
Debug.print_enable();;
Debug.set_colors();;

(* Let us do a convex hull, with traces enabled: *)
p3 || p4;;
(* It gives for instance the input PLP tableau, the partition in regions. *)

(* Again, with more detailed traces: *)
Join.Debug.enable DebugTypes.([MOutput ; MInput ; Title ; Normal]);;
PLPCore.Debug.enable DebugTypes.([MOutput ; MInput ; Title ; Normal ; Detail]);;
p3 || p4;;

(* Traces for projection *)
Pol.Debug.enable DebugTypes.([MOutput ; MInput ; Title ; Normal ; Detail]);;
Proj.Debug.enable DebugTypes.([MOutput ; MInput ; Title ; Normal ; Detail]);;
Flags.proj := Flags.Proj_PLP (Flags.Float);;

let p3 = p2 |- "z" ;;

