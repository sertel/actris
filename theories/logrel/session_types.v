From iris.algebra Require Export gmap.
From actris.logrel Require Export model.
From actris.channel Require Export channel.

Definition lmsg Σ := iMsg Σ.
Delimit Scope lmsg_scope with lmsg.
Bind Scope lmsg_scope with lmsg.

Definition lty_msg_exist {Σ} {k} (M : lty Σ k → lmsg Σ) : lmsg Σ :=
  (∃ v, M v)%msg.

Definition lty_msg_base {Σ} (A : ltty Σ) (S : lsty Σ) : lmsg Σ :=
  (∃ v, MSG v {{ ▷ ltty_car A v}} ; (lsty_car S))%msg.

Definition lty_end {Σ} : lsty Σ := Lsty END.

Definition lty_message {Σ} (a : action) (M : lmsg Σ) : lsty Σ :=
  Lsty (<a> M).

Definition lty_choice {Σ} (a : action) (Ss : gmap Z (lsty Σ)) : lsty Σ :=
  Lsty (<a@(x : Z)> MSG #x {{ ⌜is_Some (Ss !! x)⌝ }}; lsty_car (Ss !!! x)).

Definition lty_dual {Σ} (S : lsty Σ) : lsty Σ :=
  Lsty (iProto_dual (lsty_car S)).
Definition lty_app {Σ} (S1 S2 : lsty Σ) : lsty Σ :=
  Lsty (lsty_car S1 <++> lsty_car S2).

Instance: Params (@lty_message) 2 := {}.
Instance: Params (@lty_choice) 2 := {}.
Instance: Params (@lty_dual) 1 := {}.
Instance: Params (@lty_app) 1 := {}.

Notation "'TY' A ; S" := (lty_msg_base A S)
  (at level 200, right associativity,
   format "'TY'  A  ;  S") : lmsg_scope.
Notation "∃ x .. y , m" :=
  (lty_msg_exist (λ x, .. (lty_msg_exist (λ y, m)) ..)%lmsg) : lmsg_scope.

Notation "'END'" := lty_end : lty_scope.
Notation "<!!> M" :=
  (lty_message Send M) (at level 200, M at level 200) : lty_scope.
Notation "<!! x1 .. xn > M" :=
  (lty_message Send (∃ x1, .. (∃ xn, M) ..))
    (at level 200, x1 closed binder, xn closed binder, M at level 200,
     format "<!!  x1  ..  xn >  M") : lty_scope.
Notation "<??> M" :=
  (lty_message Recv M) (at level 200, M at level 200) : lty_scope.
Notation "<?? x1 .. xn > M" :=
  (lty_message Recv (∃ x1, .. (∃ xn, M) ..))
    (at level 200, x1 closed binder, xn closed binder, M at level 200,
     format "<??  x1  ..  xn >  M") : lty_scope.
Notation lty_select := (lty_choice Send).
Notation lty_branch := (lty_choice Recv).
Infix "<++>" := lty_app (at level 60) : lty_scope.
Notation "( S <++>.)" := (lty_app S) (only parsing) : lty_scope.
Notation "(.<++> T )" := (λ S, lty_app S T) (only parsing) : lty_scope.

Section session_types.
  Context {Σ : gFunctors}.

  Global Instance lty_msg_exist_ne k :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (@lty_msg_exist Σ k).
  Proof. solve_proper. Qed.
  Global Instance lty_msg_exist_proper k :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@lty_msg_exist Σ k).
  Proof. solve_proper. Qed.
  Global Instance lty_msg_base_ne : NonExpansive2 (@lty_msg_base Σ).
  Proof. rewrite /lty_msg_base. solve_proper. Qed.
  Global Instance lty_msg_base_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@lty_msg_base Σ).
  Proof. rewrite /lty_msg_base. apply ne_proper_2, _. Qed.
  Global Instance lty_msg_base_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lty_msg_base Σ).
  Proof. solve_contractive. Qed.

  Global Instance lty_message_ne a : NonExpansive (@lty_message Σ a).
  Proof. solve_proper. Qed.
  Global Instance lty_message_proper a :
    Proper ((≡) ==> (≡)) (@lty_message Σ a).
  Proof. apply ne_proper, _. Qed.

  Global Instance lty_choice_ne a : NonExpansive (@lty_choice Σ a).
  Proof. solve_proper. Qed.
  Global Instance lty_choice_proper a : Proper ((≡) ==> (≡)) (@lty_choice Σ a).
  Proof. apply ne_proper, _. Qed.
(* FIXME
  Global Instance lty_choice_contractive a : Contractive (@lty_choice Σ a).
  Proof. solve_contractive. Qed.
*)
  Global Instance lty_dual_ne : NonExpansive (@lty_dual Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_dual_proper : Proper ((≡) ==> (≡)) (@lty_dual Σ).
  Proof. apply ne_proper, _. Qed.

  Global Instance lty_app_ne : NonExpansive2 (@lty_app Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_app_proper : Proper ((≡) ==> (≡) ==> (≡)) (@lty_app Σ).
  Proof. apply ne_proper_2, _. Qed.
End session_types.
