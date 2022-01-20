(** This file defines the semantic interpretations of session types as Actris
protocols. It includes session types for sending and receiving with session
polymorphism, as well as n-ary choice. Recursive protocols are defined in
the [model.v] file. *)
From iris.algebra Require Export gmap.
From actris.logrel Require Export model telescopes.
From actris.channel Require Export proofmode.

Definition lmsg Σ := iMsg Σ.
Declare Scope lmsg_scope.
Delimit Scope lmsg_scope with lmsg.
Bind Scope lmsg_scope with lmsg.

Definition lty_msg_base {Σ} (A : ltty Σ) (S : lsty Σ) : lmsg Σ :=
  (∃ v, MSG v {{ ltty_car A v}} ; (lsty_car S))%msg.

Definition lty_msg_exist {Σ} {k} (M : lty Σ k → lmsg Σ) : lmsg Σ :=
  (∃ X, M X)%msg.

Definition lty_msg_texist {Σ} {kt : ktele Σ} (M : ltys Σ kt → lmsg Σ) : lmsg Σ :=
  ktele_fold (@lty_msg_exist Σ) (λ x, x) (ktele_bind M).
Arguments lty_msg_texist {_ !_} _%lmsg /.

Definition lty_end {Σ} : lsty Σ := Lsty END.

Definition lty_message {Σ} (a : action) (M : lmsg Σ) : lsty Σ :=
  Lsty (<a> M).

Definition lty_choice {Σ} (a : action) (Ss : gmap Z (lsty Σ)) : lsty Σ :=
  Lsty (<a@(x : Z)> MSG #x {{ ⌜is_Some (Ss !! x)⌝ }}; lsty_car (Ss !!! x)).

Definition lty_dual {Σ} (S : lsty Σ) : lsty Σ :=
  Lsty (iProto_dual (lsty_car S)).
Definition lty_app {Σ} (S1 S2 : lsty Σ) : lsty Σ :=
  Lsty (lsty_car S1 <++> lsty_car S2).

Global Instance: Params (@lty_message) 2 := {}.
Global Instance: Params (@lty_choice) 2 := {}.
Global Instance: Params (@lty_dual) 1 := {}.
Global Instance: Params (@lty_app) 1 := {}.

Notation "'TY' A ; S" := (lty_msg_base A S)
  (at level 200, right associativity,
   format "'TY'  A ;  S") : lmsg_scope.
Notation "∃ X .. Y , M" :=
  (lty_msg_exist (λ X, .. (lty_msg_exist (λ Y, M)) ..)%lmsg) : lmsg_scope.
Notation "'∃..' X .. Y , M" :=
  (lty_msg_texist (λ X, .. (lty_msg_texist (λ Y, M)) .. )%lmsg)
  (at level 200, X binder, Y binder, right associativity,
   format "∃..  X  ..  Y ,  M") : lmsg_scope.

Notation "'END'" := lty_end : lty_scope.
Notation "<!!> M" :=
  (lty_message Send M) (at level 200, M at level 200) : lty_scope.
Notation "<!! X .. Y > M" :=
  (<!!> ∃ X, .. (∃ Y, M) ..)%lty
    (at level 200, X closed binder, Y closed binder, M at level 200,
     format "<!!  X  ..  Y >  M") : lty_scope.
Notation "<!!.. X .. Y > M" := (<!!> ∃.. X, .. (∃.. Y, M) ..)%lty
  (at level 200, X closed binder, Y closed binder, M at level 200,
   format "<!!..  X  ..  Y >  M") : lty_scope.

Notation "<??> M" :=
  (lty_message Recv M) (at level 200, M at level 200) : lty_scope.
Notation "<?? X .. Y > M" :=
  (<??> ∃ X, .. (∃ Y, M) ..)%lty
    (at level 200, X closed binder, Y closed binder, M at level 200,
     format "<??  X  ..  Y >  M") : lty_scope.
Notation "<??.. X .. Y > M" := (<??> ∃.. X, .. (∃.. Y, M) ..)%lty
  (at level 200, X closed binder, Y closed binder, M at level 200,
   format "<??..  X  ..  Y >  M") : lty_scope.
Notation lty_select := (lty_choice Send).
Notation lty_branch := (lty_choice Recv).
Infix "<++>" := lty_app (at level 60) : lty_scope.
Notation "( S <++>.)" := (lty_app S) (only parsing) : lty_scope.
Notation "(.<++> T )" := (λ S, lty_app S T) (only parsing) : lty_scope.

Class LtyMsgTele {Σ} {kt : ktele Σ} (M : lmsg Σ)
    (A : kt -k> ltty Σ) (S : kt -k> lsty Σ) :=
  lty_msg_tele : M ≡ (∃.. x, TY ktele_app A x; ktele_app S x)%lmsg.
Global Hint Mode LtyMsgTele ! - ! - - : typeclass_instances.

Section session_types.
  Context {Σ : gFunctors}.

  Global Instance lty_msg_exist_ne k n :
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
    Proper (dist n ==> dist_later n ==> dist n) (@lty_msg_base Σ).
  Proof. solve_contractive. Qed.

  Global Instance lty_message_ne a : NonExpansive (@lty_message Σ a).
  Proof. solve_proper. Qed.
  Global Instance lty_message_proper a : Proper ((≡) ==> (≡)) (@lty_message Σ a).
  Proof. apply ne_proper, _. Qed.

  Global Instance lty_choice_ne a : NonExpansive (@lty_choice Σ a).
  Proof. solve_proper. Qed.
  Global Instance lty_choice_proper a : Proper ((≡) ==> (≡)) (@lty_choice Σ a).
  Proof. apply ne_proper, _. Qed.
  Global Instance lty_choice_contractive a n :
    Proper (map_relation (dist_later n) (λ _, False) (λ _, False) ==> dist n)
           (@lty_choice Σ a).
  Proof.
    intros Ss Ts Heq. rewrite /lty_choice.
    do 2 f_equiv. f_equiv => i.
    rewrite !lookup_total_alt.
    specialize (Heq i).
    destruct (Ss !! i), (Ts !! i);
      [ f_contractive | contradiction | contradiction | done ].
    - f_equiv. split; intros H; eauto.
    - by rewrite Heq.
  Qed.
  Global Instance lty_dual_ne : NonExpansive (@lty_dual Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_dual_proper : Proper ((≡) ==> (≡)) (@lty_dual Σ).
  Proof. apply ne_proper, _. Qed.
  Global Instance lty_dual_involutive : Involutive (≡) (@lty_dual Σ).
  Proof. intros S. rewrite /lty_dual. apply iProto_dual_involutive. Qed.

  Global Instance lty_app_ne : NonExpansive2 (@lty_app Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_app_proper : Proper ((≡) ==> (≡) ==> (≡)) (@lty_app Σ).
  Proof. apply ne_proper_2, _. Qed.

  Global Instance lty_msg_tele_base (A : ltty Σ) (S : lsty Σ) :
    LtyMsgTele (kt:=KTeleO) (TY A ; S) A S.
  Proof. done. Qed.
  Global Instance lty_msg_tele_exist {k} {kt : lty Σ k → ktele Σ}
    (M : lty Σ k → lmsg Σ) A S :
    (∀ x, LtyMsgTele (kt:=kt x) (M x) (A x) (S x)) →
    LtyMsgTele (kt:=KTeleS kt) (∃ x, M x) A S.
  Proof. intros HM. rewrite /LtyMsgTele /=. f_equiv=> x. apply HM. Qed.

  Global Instance lty_app_end_l : LeftId (≡) END%lty (@lty_app Σ).
  Proof. intros S1. rewrite /lty_app. apply iProto_app_end_l. Qed.

  Global Instance lty_app_end_r : RightId (≡) END%lty (@lty_app Σ).
  Proof. intros S1. rewrite /lty_app. apply iProto_app_end_r. Qed.

  Global Instance lty_app_assoc : Assoc (≡) (@lty_app Σ).
  Proof. intros S1 S2 S3. rewrite /lty_app. apply iProto_app_assoc. Qed.

  Lemma lty_app_send (A : ltty Σ) S1 S2 :
    ((<!!> TY A; S1) <++> S2)%lty ≡ ((<!!> TY A; S1 <++> S2))%lty.
  Proof.
    rewrite /lty_message /lty_msg_base !/lty_app iProto_app_message iMsg_app_exist.
    do 4 f_equiv. by rewrite iMsg_app_base.
  Qed.

  Lemma lty_app_recv (A : ltty Σ) S1 S2 :
    ((<??> TY A; S1) <++> S2)%lty ≡ ((<??> TY A; S1 <++> S2))%lty.
  Proof.
    rewrite /lty_message /lty_msg_base !/lty_app iProto_app_message iMsg_app_exist.
    do 4 f_equiv. by rewrite iMsg_app_base.
  Qed.

  Lemma lsty_car_app (S T : lsty Σ) :
    lsty_car (S <++> T) = (lsty_car S <++> lsty_car T)%proto.
  Proof. eauto. Qed.

End session_types.
