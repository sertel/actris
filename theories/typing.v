From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From stdpp Require Import gmap.
From iris.base_logic Require Import invariants.
Require Import FunctionalExtensionality.

Section typing.

  (* Sides *)
  Inductive side : Set :=
  | Left
  | Right.

  (* Session Types *)
  Inductive stype :=
  | TEnd
  | TSend (P : heap_lang.val → Prop) (sτ : heap_lang.val → stype)
  | TRecv (P : heap_lang.val → Prop) (sτ : heap_lang.val → stype).

  Fixpoint dual_stype (sτ :stype) :=
    match sτ with
    | TEnd => TEnd
    | TSend P sτ => TRecv P (λ v, dual_stype (sτ v))
    | TRecv P sτ => TSend P (λ v, dual_stype (sτ v))
    end.

End typing.