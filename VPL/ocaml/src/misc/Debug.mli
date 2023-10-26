(** This module handles debug traces for all other modules.
The level of details in traces can be tuned independantly for each module, during execution (see {val!DebugTypes.levelT}).
For instance, if you want to see only the [Title] level for module [Proj], type [Proj.Debug.enable [Title]].

For readability, each module is associated to a color, available only in on-the-fly mode.*)

(** Enables debug traces for all modules. *)
val enable : unit -> unit

(** Disables debug traces for all modules. *)
val disable : unit -> unit

(** Set colors for each module*)
val set_colors : unit -> unit

(** Prints traces on-the-fly. *)
val print_enable : unit -> unit

(** Disable on-the-fly mode.*)
val print_disable : unit -> unit

val get_trace : unit -> string list

val reset_trace : unit -> unit
