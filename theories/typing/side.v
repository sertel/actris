From iris.heap_lang Require Import proofmode notation.
From osiris.typing Require Export involutive.

Inductive side := Left | Right.
Instance side_inhabited : Inhabited side := populate Left.
Definition dual_side (s : side) : side :=
  match s with Left => Right | Right => Left end.
Instance dual_side_involutive : Involutive (=) dual_side.
Proof. by intros []. Qed.