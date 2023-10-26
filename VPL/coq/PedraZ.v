(** This module offers an abstract domain of polyhedra on integers. *)

Require PedraQ.
Require DomainFunctors.
Require Import ASCond.
Require Import ZNoneItv.

Module FullDom <: FullItvAbstractDomain ZNum ZCond ZNItv
 := DomainFunctors.MakeZ PedraQ.BasicD PedraQ.CstrD PedraQ.AffItvD PedraQ.Rename PedraQ.BasicD.
