From actris.logrel Require Export ltyping lsty.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From actris.channel Require Import proto proofmode.

Section protocols.
  Context `{heapG Σ, protoG Σ}.

  Definition lsty_end : lsty Σ := Lsty END.

  Definition lsty_send (A : lty Σ) (P : lsty Σ) : lsty Σ :=
    Lsty (<!> v, MSG v {{ A v }}; lsty_car P).
  Definition lsty_recv (A : lty Σ) (P : lsty Σ) : lsty Σ :=
    Lsty (<?> v, MSG v {{ A v }}; lsty_car P).

  Definition lsty_branch (P1 P2 : lsty Σ) : lsty Σ :=
    Lsty (P1 <&> P2).
  Definition lsty_select (P1 P2 : lsty Σ) : lsty Σ :=
    Lsty (P1 <+> P2).

  Definition lsty_rec1 (C : lsty Σ → lsty Σ)
             `{!Contractive C}
             (rec : lsty Σ) : lsty Σ :=
    Lsty (C rec).

  Instance lsty_rec1_contractive C `{!Contractive C} : Contractive (lsty_rec1 C).
  Proof. solve_contractive. Qed.

  Definition lsty_rec (C : lsty Σ → lsty Σ) `{!Contractive C} : lsty Σ :=
    fixpoint (lsty_rec1 C).

  Definition lsty_dual (P : lsty Σ) : lsty Σ :=
    Lsty (iProto_dual P).

  Definition lsty_app (P1 P2 : lsty Σ) : lsty Σ :=
    Lsty (iProto_app P1 P2).

End protocols.

Section Propers.
  Context `{heapG Σ, protoG Σ}.

  Global Instance lsty_send_ne : NonExpansive2 (@lsty_send Σ).
  Proof.
    intros n A A' H1 P P' H2.
    rewrite /lsty_send.
    apply Lsty_ne.
    apply iProto_message_ne; simpl; try done.
  Qed.

  Global Instance lsty_send_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lsty_send Σ).
  Proof.
    intros A A' H1 P P' H2.
    rewrite /lsty_send.
    apply Lsty_ne.
    apply iProto_message_contractive; simpl; try done.
    intros v.
    destruct n as [|n]; try done.
    apply H1.
  Qed.

  Global Instance lsty_recv_ne : NonExpansive2 (@lsty_recv Σ).
  Proof.
    intros n A A' H1 P P' H2.
    rewrite /lsty_recv.
    apply Lsty_ne.
    apply iProto_message_ne; simpl; try done.
  Qed.

  Global Instance lsty_recv_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lsty_recv Σ).
  Proof.
    intros A A' H1 P P' H2.
    rewrite /lsty_recv.
    apply Lsty_ne.
    apply iProto_message_contractive; simpl; try done.
    intros v.
    destruct n as [|n]; try done.
    apply H1.
  Qed.

  Global Instance lsty_branch_ne : NonExpansive2 (@lsty_branch Σ).
  Proof.
    intros n A A' H1 P P' H2.
    rewrite /lsty_branch.
    apply Lsty_ne.
    apply iProto_message_ne; simpl; try done.
    intros v. destruct v; done.
  Qed.

  Global Instance lsty_branch_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lsty_branch Σ).
  Proof.
    intros A A' H1 P P' H2.
    rewrite /lsty_branch.
    apply Lsty_ne.
    apply iProto_message_contractive; simpl; try done.
    intros v.
    destruct v; destruct n as [|n]; try done.
  Qed.

  Global Instance lsty_select_ne : NonExpansive2 (@lsty_select Σ).
  Proof.
    intros n A A' H1 P P' H2.
    rewrite /lsty_select.
    apply Lsty_ne.
    apply iProto_message_ne; simpl; try done.
    intros v. destruct v; done.
  Qed.

  Global Instance lsty_select_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lsty_select Σ).
  Proof.
    intros A A' H1 P P' H2.
    rewrite /lsty_select.
    apply Lsty_ne.
    apply iProto_message_contractive; simpl; try done.
    intros v.
    destruct v; destruct n as [|n]; try done.
  Qed.

  Global Instance lsty_dual_ne : NonExpansive (@lsty_dual Σ).
  Proof.
    intros n P P' HP.
    rewrite /lsty_dual.
    apply Lsty_ne.
    by apply iProto_dual_ne.
  Qed.

  Global Instance lsty_app_ne : NonExpansive2 (@lsty_app Σ).
  Proof.
    intros n P1 P1' H1 P2 P2' H2.
    rewrite /lsty_app.
    apply Lsty_ne.
    by apply iProto_app_ne.
  Qed.

End Propers.

Notation "'END'" := lsty_end : lsty_scope.
Notation "<!!> A ; P" :=
  (lsty_send A P) (at level 20, A, P at level 200) : lsty_scope.
Notation "<??> A ; P" :=
  (lsty_recv A P) (at level 20, A, P at level 200) : lsty_scope.
Infix "<+++>" := lsty_select (at level 60) : lsty_scope.
Infix "<&&&>" := lsty_branch (at level 85) : lsty_scope.
Infix "<++++>" := lsty_app (at level 60) : lsty_scope.
