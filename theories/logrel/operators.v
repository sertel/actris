(** This file defines semantic typing judgments and typing lemmas for the
operators of the language. The typing judgments for operators are expressed
using type classes, so they can easily be solved automatically. *)
From actris.logrel Require Export term_types.
From iris.heap_lang Require Import proofmode.

(** Semantic operator typing *)
Class LTyUnboxed {Σ} (A : ltty Σ) :=
  lty_unboxed v :
    ltty_car A v -∗ ⌜ val_is_unboxed v ⌝.

Class LTyUnOp {Σ} (op : un_op) (A B : ltty Σ) :=
  lty_un_op v :
    ltty_car A v -∗ ∃ w, ⌜ un_op_eval op v = Some w ⌝ ∧ ltty_car B w.

Class LTyBinOp {Σ} (op : bin_op) (A1 A2 B : ltty Σ) :=
  lty_bin_op v1 v2 :
    ltty_car A1 v1 -∗ ltty_car A2 v2 -∗
    ∃ w, ⌜ bin_op_eval op v1 v2 = Some w ⌝ ∧ ltty_car B w.

Section operators.
  Context {Σ : gFunctors}.
  Implicit Types A B : ltty Σ.

  (** Rules for unboxed types *)
  Global Instance lty_unit_unboxed : LTyUnboxed (Σ:=Σ) ().
  Proof. by iIntros (v ->). Qed.
  Global Instance lty_bool_unboxed : LTyUnboxed (Σ:=Σ) lty_bool.
  Proof. iIntros (v). by iDestruct 1 as (b) "->". Qed.
  Global Instance lty_int_unboxed : LTyUnboxed (Σ:=Σ) lty_int.
  Proof. iIntros (v). by iDestruct 1 as (i) "->". Qed.
  Global Instance lty_ref_uniq_unboxed `{heapG Σ} A : LTyUnboxed (ref_uniq A).
  Proof. iIntros (v). by iDestruct 1 as (i w ->) "?". Qed.
  Global Instance lty_ref_shr_unboxed `{heapG Σ} A : LTyUnboxed (ref_shr A).
  Proof. iIntros (v). by iDestruct 1 as (l ->) "?". Qed.

  (** Rules for operator typing *)
  Global Instance lty_un_op_int op : LTyUnOp (Σ:=Σ) op lty_int lty_int.
  Proof. iIntros (?). iDestruct 1 as (i) "->". destruct op; eauto. Qed.
  Global Instance lty_un_op_bool : LTyUnOp (Σ:=Σ) NegOp lty_bool lty_bool.
  Proof. iIntros (?). iDestruct 1 as (i) "->". eauto. Qed.

  Global Instance lty_bin_op_eq A : LTyUnboxed A → LTyBinOp EqOp A A lty_bool.
  Proof.
    iIntros (? v1 v2) "A1 _". rewrite /bin_op_eval /ltty_car /=.
    iDestruct (lty_unboxed with "A1") as %Hunb.
    rewrite decide_True; [eauto|solve_vals_compare_safe].
  Qed.
  Global Instance lty_bin_op_arith op :
    TCElemOf op [PlusOp; MinusOp; MultOp; QuotOp; RemOp;
                 AndOp; OrOp; XorOp; ShiftLOp; ShiftROp] →
    LTyBinOp (Σ:=Σ) op lty_int lty_int lty_int.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /ltty_car /=; eauto.
  Qed.
  Global Instance lty_bin_op_compare op :
    TCElemOf op [LeOp; LtOp] →
    LTyBinOp (Σ:=Σ) op lty_int lty_int lty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /ltty_car /=; eauto.
  Qed.
  Global Instance lty_bin_op_bool op :
    TCElemOf op [AndOp; OrOp; XorOp] →
    LTyBinOp (Σ:=Σ) op lty_bool lty_bool lty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /ltty_car /=; eauto.
  Qed.
End operators.
