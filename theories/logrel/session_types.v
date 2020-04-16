From actris.logrel Require Export ltyping lsty.
From iris.algebra Require Import gmap.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From actris.channel Require Import proto proofmode.

Section protocols.
  Context `{heapG Σ, protoG Σ}.

  Definition lsty_end : lsty Σ := Lsty END.

  Definition lsty_message (a : action) (A : lty Σ) (S : lsty Σ) : lsty Σ :=
    Lsty (<a> v, MSG v {{ A v }}; lsty_car S).

  Definition lsty_send (A : lty Σ) (S : lsty Σ) : lsty Σ :=
    lsty_message Send A S.
  Definition lsty_recv (A : lty Σ) (S : lsty Σ) : lsty Σ :=
    lsty_message Recv A S.

  Definition lsty_choice (a : action) (Ss : gmap Z (lsty Σ)) : lsty Σ :=
    Lsty (<a> x : Z, MSG #x {{ ⌜is_Some (Ss !! x)⌝ }}; lsty_car (Ss !!! x)).

  Definition lsty_select (Ss : gmap Z (lsty Σ)) : lsty Σ :=
    lsty_choice Send Ss.
  Definition lsty_branch (Ss : gmap Z (lsty Σ)) : lsty Σ :=
    lsty_choice Recv Ss.

  Definition lsty_rec1 (C : lsty Σ → lsty Σ) `{!Contractive C}
    (rec : lsty Σ) : lsty Σ := Lsty (C rec).
  Instance lsty_rec1_contractive C `{!Contractive C} : Contractive (lsty_rec1 C).
  Proof. solve_contractive. Qed.
  Definition lsty_rec (C : lsty Σ → lsty Σ) `{!Contractive C} : lsty Σ :=
    fixpoint (lsty_rec1 C).

  Definition lsty_dual (S : lsty Σ) : lsty Σ :=
    Lsty (iProto_dual S).

  Definition lsty_app (S1 S2 : lsty Σ) : lsty Σ :=
    Lsty (S1 <++> S2).
End protocols.

Section Propers.
  Context `{heapG Σ, protoG Σ}.

  Global Instance lsty_message_ne a : NonExpansive2 (@lsty_message Σ a).
  Proof. intros n A A' ? S S' ?. by apply iProto_message_ne; simpl. Qed.
  Global Instance lsty_message_contractive n a :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lsty_message Σ a).
  Proof.
    intros A A' ? S S' ?.
    apply iProto_message_contractive; simpl; done || by destruct n.
  Qed.

  Global Instance lsty_send_ne : NonExpansive2 (@lsty_send Σ).
  Proof. solve_proper. Qed.
  Global Instance lsty_send_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lsty_send Σ).
  Proof. solve_contractive. Qed.

  Global Instance lsty_recv_ne : NonExpansive2 (@lsty_recv Σ).
  Proof. solve_proper. Qed.
  Global Instance lsty_recv_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lsty_recv Σ).
  Proof. solve_contractive. Qed.

  Global Instance lsty_choice_ne a : NonExpansive (@lsty_choice Σ a).
  Proof.
    intros n Ss1 Ss2 Pseq. apply iProto_message_ne; simpl; solve_proper.
  Qed.
  Global Instance lsty_choice_contractive a : Contractive (@lsty_choice Σ a).
  Proof.
    intros ? Ss1 Ss2 ?.
    apply iProto_message_contractive; destruct n; simpl; done || solve_proper.
  Qed.

  Global Instance lsty_select_ne : NonExpansive (@lsty_select Σ).
  Proof. solve_proper. Qed.
  Global Instance lsty_select_contractive : Contractive (@lsty_select Σ).
  Proof. solve_contractive. Qed.

  Global Instance lsty_branch_ne : NonExpansive (@lsty_branch Σ).
  Proof. solve_proper. Qed.
  Global Instance lsty_branch_contractive : Contractive (@lsty_branch Σ).
  Proof. solve_contractive. Qed.

  Global Instance lsty_dual_ne : NonExpansive (@lsty_dual Σ).
  Proof. solve_proper. Qed.
  Global Instance lsty_app_ne : NonExpansive2 (@lsty_app Σ).
  Proof. solve_proper. Qed.
End Propers.

Notation "'END'" := lsty_end : lsty_scope.
Notation "<!!> A ; S" :=
  (lsty_send A S) (at level 20, A, S at level 200) : lsty_scope.
Notation "<??> A ; S" :=
  (lsty_recv A S) (at level 20, A, S at level 200) : lsty_scope.
Infix "<++>" := lsty_app (at level 60) : lsty_scope.
