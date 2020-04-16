From actris.logrel Require Export ltyping lsty.
From iris.algebra Require Import gmap.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From actris.channel Require Import proto proofmode.

Section protocols.
  Context `{heapG Σ, protoG Σ}.

  Definition lsty_end : lsty Σ := Lsty END.

  Definition lsty_message (a : action) (A : lty Σ) (P : lsty Σ) : lsty Σ :=
    Lsty (<a> v, MSG v {{ A v }}; lsty_car P).

  Definition lsty_send (A : lty Σ) (P : lsty Σ) : lsty Σ :=
    lsty_message Send A P.
  Definition lsty_recv (A : lty Σ) (P : lsty Σ) : lsty Σ :=
    lsty_message Recv A P.

  Definition lsty_choice (a : action) (Ps : gmap Z (lsty Σ)) : lsty Σ :=
    Lsty (<a> x : Z, MSG #x {{ ⌜is_Some (Ps !! x)⌝ }}; lsty_car (Ps !!! x)).

  Definition lsty_select (Ps : gmap Z (lsty Σ)) : lsty Σ :=
    lsty_choice Send Ps.
  Definition lsty_branch (Ps : gmap Z (lsty Σ)) : lsty Σ :=
    lsty_choice Recv Ps.

  Definition lsty_rec1 (C : lsty Σ → lsty Σ) `{!Contractive C}
    (rec : lsty Σ) : lsty Σ := Lsty (C rec).
  Instance lsty_rec1_contractive C `{!Contractive C} : Contractive (lsty_rec1 C).
  Proof. solve_contractive. Qed.
  Definition lsty_rec (C : lsty Σ → lsty Σ) `{!Contractive C} : lsty Σ :=
    fixpoint (lsty_rec1 C).

  Definition lsty_dual (P : lsty Σ) : lsty Σ :=
    Lsty (iProto_dual P).

  Definition lsty_app (P1 P2 : lsty Σ) : lsty Σ :=
    Lsty (P1 <++> P2).
End protocols.

Section Propers.
  Context `{heapG Σ, protoG Σ}.

  Global Instance lsty_message_ne a : NonExpansive2 (@lsty_message Σ a).
  Proof. intros n A A' ? P P' ?. by apply iProto_message_ne; simpl. Qed.
  Global Instance lsty_message_contractive n a :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lsty_message Σ a).
  Proof.
    intros A A' ? P P' ?.
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
    intros n Ps1 Ps2 Pseq. apply iProto_message_ne; simpl; solve_proper.
  Qed.
  Global Instance lsty_choice_contractive a : Contractive (@lsty_choice Σ a).
  Proof.
    intros ? Ps1 Ps2 ?.
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
Notation "<!!> A ; P" :=
  (lsty_send A P) (at level 20, A, P at level 200) : lsty_scope.
Notation "<??> A ; P" :=
  (lsty_recv A P) (at level 20, A, P at level 200) : lsty_scope.
Infix "<++>" := lsty_app (at level 60) : lsty_scope.
