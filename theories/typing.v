From iris.heap_lang Require Export lang.
Require Import FunctionalExtensionality.


Class Involutive {T} (f : T → T) :=
  involutive : ∀ t : T, t = f (f t).

Inductive side : Set :=
| Left
| Right.

Instance side_inhabited : Inhabited side := populate Left.

Definition dual_side (s : side) : side :=
  match s with Left => Right | Right => Left end.

Instance dual_side_involutive : Involutive dual_side.
Proof. intros s; destruct s; eauto. Qed.

Inductive stype :=
| TEnd
| TSend (P : val → Prop) (st : val → stype)
| TRecv (P : val → Prop) (st : val → stype).

Instance stype_inhabited : Inhabited stype := populate TEnd.

Fixpoint dual_stype (st :stype) :=
  match st with
  | TEnd => TEnd
  | TSend P st => TRecv P (λ v, dual_stype (st v))
  | TRecv P st => TSend P (λ v, dual_stype (st v))
  end.

Instance dual_stype_involutive : Involutive dual_stype.
Proof.
  intros st.
  induction st => //; simpl;
    assert (st = (λ v : val, dual_stype (dual_stype (st v)))) as Heq
        by apply functional_extensionality => //;
    rewrite -Heq => //.
Qed.
