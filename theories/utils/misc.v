From iris.heap_lang Require Import notation.
Set Default Proof Using "Type".

(** MOVE TO IRIS *)
Global Instance fst_atomic a v1 v2 : Atomic a (Fst (v1,v2)%V).
Proof.
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].
Qed.
