From actris.channel Require Import channel proofmode.
From iris.heap_lang.lib Require Import par.

(**
Inspired by the work of Qian et al.
Client-Server Sessions in Linear Logic
*)

(**
Linear Logic / Session-Type correspondence

1 =  ⊥  = END
A ⨂ S   = !A.S
A _&_ S = ?(A^⟂).S
S ⨁ T   = S <+> T
S & T   = S <&> T
*)

Section exponential_prot.
  Context `{heapG Σ, chanG Σ}.

  (** F_A(X) ≜ 1 & A & (X ⨂ X) *)
  Definition iProto_of_course_aux (A : iProto Σ) (rec : iProto Σ) : iProto Σ :=
    (END <&> (A <&> (<!(c:val)> MSG c {{ c ↣ rec }}; rec)))%proto.
  Instance iProto_of_course_aux_contractive A : Contractive (iProto_of_course_aux A).
  Proof. solve_proto_contractive. Qed.
  (** !A ≜ ν X. F_A(X) *)
  Definition iProto_of_course (A : iProto Σ) : iProto Σ :=
    fixpoint (iProto_of_course_aux A).
  Lemma iProto_of_course_unfold A :
    iProto_of_course A ≡ iProto_of_course_aux A (iProto_of_course A).
  Proof.
      by rewrite /iProto_of_course
                 {1}(fixpoint_unfold (iProto_of_course_aux A)).
  Qed.

  (** G_A(X) ≜ ⊥ ⨁ A ⨁ (X _&_ X) *)
  Definition iProto_why_not_aux (A : iProto Σ) (rec : iProto Σ) : iProto Σ :=
    (END <+> (A <+> (<?(c:val)> MSG c {{ c ↣ iProto_dual rec }}; rec)))%proto.
  Instance iProto_why_not_aux_contractive A : Contractive (iProto_why_not_aux A).
  Proof. solve_proto_contractive. Qed.
  (** ?A ≜  μ X. G_A(X) *)
  Definition iProto_why_not (A : iProto Σ) := fixpoint (iProto_why_not_aux A).
  Lemma iProto_why_not_unfold A :
    iProto_why_not A ≡ iProto_why_not_aux A (iProto_why_not A).
  Proof. by rewrite /iProto_why_not {1}(fixpoint_unfold (iProto_why_not_aux A)). Qed.

  (** H_A(X) ≜ ⊥ & A & (X _&_ X) *)
  Definition iProto_server_aux (A : iProto Σ) (rec : iProto Σ) : iProto Σ :=
    (END <&> (A <&> (<?(c:val)> MSG c {{ c ↣ rec }}; rec)))%proto.
  Instance iProto_server_aux_contractive A : Contractive (iProto_server_aux A).
  Proof. solve_proto_contractive. Qed.
  (** _!_A ≜ μ X. H_A(X) *)
  Definition iProto_server (A : iProto Σ) := fixpoint (iProto_server_aux A).
  Lemma iProto_server_unfold A :
    iProto_server A ≡ iProto_server_aux A (iProto_server A).
  Proof. by rewrite /iProto_server {1}(fixpoint_unfold (iProto_server_aux A)). Qed.

  (** K_A(X) ≜ 1 ⨁ A ⨁ (X ⨂ X) *)
  Definition iProto_client_aux (A : iProto Σ) (rec : iProto Σ) : iProto Σ :=
    (END <+> (A <+> (<!(c:val)> MSG c {{ c ↣ iProto_dual rec }}; rec)))%proto.
  Instance iProto_client_aux_contractive A : Contractive (iProto_client_aux A).
  Proof. solve_proto_contractive. Qed.
  (** _?_A ≜ μ X. K_A(X) *)
  Definition iProto_client (A : iProto Σ) := fixpoint (iProto_client_aux A).
  Lemma iProto_client_unfold A :
    iProto_client A ≡ iProto_client_aux A (iProto_client A).
  Proof. by rewrite /iProto_client {1}(fixpoint_unfold (iProto_client_aux A)). Qed.

  (** (?A)^⟂ = !(A^⟂)*)
  Lemma why_not_of_course_dual (A : iProto Σ) :
    iProto_dual (iProto_why_not A) ≡ iProto_of_course (iProto_dual A).
  Proof.
    apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (A).
    iEval (rewrite iProto_why_not_unfold iProto_of_course_unfold).
    rewrite iProto_dual_choice iProto_dual_end.
    iApply iProto_choice_equiv; repeat iSplit; try done.
    rewrite iProto_dual_choice.
    iApply iProto_choice_equiv; repeat iSplit; try done.
    rewrite iProto_dual_message iMsg_dual_exist.
    rewrite iProto_message_equivI; repeat iSplit; try done.
    iIntros (v lp).
    iIntros "!>!>".
    rewrite iMsg_exist_eq.
    iApply prop_ext; iIntros "!>"; iSplit.
    - iDestruct 1 as (x) "H".
      iExists x.
      rewrite iMsg_car_proper; [ | apply iMsg_dual_base | done | done ].
      rewrite iMsg_base_eq.
      simpl. iDestruct "H" as (->) "[Heq H]".
      iRewrite ("IH" $!A) in "H".
      iRewrite ("IH" $!A) in "Heq".
      by iFrame.
    - iDestruct 1 as (x) "H".
      iExists x.
      rewrite (iMsg_car_proper (iMsg_dual _));
        [ | apply iMsg_dual_base | done | done ].
      rewrite iMsg_base_eq.
      iDestruct "H" as (->) "[Heq H]".
      iRewrite -("IH" $!A) in "H".
      iRewrite -("IH" $!A) in "Heq".
      by iFrame.
  Qed.

  (** (_?_A)^⟂ = _!_(A^⟂)*)
  Lemma client_server_dual (A : iProto Σ) :
    iProto_dual (iProto_client A) ≡ iProto_server (iProto_dual A).
  Proof.
    apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (A).
    iEval (rewrite iProto_client_unfold iProto_server_unfold).
    rewrite iProto_dual_choice iProto_dual_end.
    iApply iProto_choice_equiv; repeat iSplit; try done.
    rewrite iProto_dual_choice.
    iApply iProto_choice_equiv; repeat iSplit; try done.
    rewrite iProto_dual_message iMsg_dual_exist.
    rewrite iProto_message_equivI; repeat iSplit; try done.
    iIntros (v lp).
    iIntros "!>!>".
    rewrite iMsg_exist_eq.
    iApply prop_ext; iIntros "!>"; iSplit.
    - iDestruct 1 as (x) "H".
      iExists x.
      rewrite iMsg_car_proper; [ | apply iMsg_dual_base | done | done ].
      rewrite iMsg_base_eq.
      simpl. iDestruct "H" as (->) "[Heq H]".
      iRewrite ("IH" $!A) in "H".
      iRewrite ("IH" $!A) in "Heq".
      by iFrame.
    - iDestruct 1 as (x) "H".
      iExists x.
      rewrite (iMsg_car_proper (iMsg_dual _));
        [ | apply iMsg_dual_base | done | done ].
      rewrite iMsg_base_eq.
      iDestruct "H" as (->) "[Heq H]".
      iRewrite -("IH" $!A) in "H".
      iRewrite -("IH" $!A) in "Heq".
      by iFrame.
  Qed.

End exponential_prot.

Notation "<|¡|> A" := (iProto_server A) (at level 100) : proto_scope.
Notation "<|¿|> A" := (iProto_client A) (at level 100) : proto_scope.
Notation "<|!|> A" := (iProto_of_course A) (at level 100) : proto_scope.
Notation "<|?|> A" := (iProto_why_not A) (at level 100) : proto_scope.

Definition server : val :=
  rec: "go" "c" "f" :=
    if: (recv "c") then #()
    else if: (recv "c") then "f" "c"
    else let: "c'" := recv "c" in
         ("go" "c" "f" ||| "go" "c'" "f");; #().

Definition client_terminate : val :=
  λ: "c", send "c" #true.

Definition client_serve : val :=
  λ: "c", send "c" #false;; send "c" #true.

Definition client_duplicate : val :=
  λ: "c",
    send "c" #false;; send "c" #false;;
    let: "c2" := new_chan #() in
    send "c" (Snd "c2");; (Fst "c2").

Section with_Σ.
  Context `{heapG Σ, chanG Σ, spawnG Σ}.

  Lemma server_spec c (f: val) prot :
    (∀ c', {{{ c' ↣ prot }}} f c' {{{ RET #(); True }}}) -∗
    {{{ c ↣ (<|¡|> prot) }}} server c f {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hfspec !>" (Φ) "Hc HΦ".
    iLöb as "IH" forall (c Φ).
    wp_lam.
    rewrite {2}iProto_server_unfold.
    wp_branch.
    { wp_pures. by iApply "HΦ". }
    wp_branch.
    { wp_pures. by iApply ("Hfspec" with "Hc"). }
    wp_recv (c') as "Hc'".
    wp_apply (wp_par (λ w, True)%I (λ w, True)%I with "[Hc] [Hc']");
      [ by iApply ("IH" with "Hc") | by iApply ("IH" with "Hc'") | ].
    iIntros (v1 v2) "_ !>".
    wp_pures. by iApply "HΦ".
  Qed.

  Lemma client_spec_terminate c prot :
    ⊢ {{{ c ↣ <|¿|> prot }}} client_terminate c {{{ RET #(); c ↣ END }}}.
  Proof.
    iIntros "!>" (Φ) "Hc HΦ".
    rewrite iProto_client_unfold.
    wp_lam. wp_select. by iApply "HΦ".
  Qed.

  Lemma client_spec_serve c prot :
     ⊢ {{{ c ↣ <|¿|> prot }}} client_serve c {{{ RET #(); c ↣ prot }}}.
  Proof.
    iIntros "!>" (Φ) "Hc HΦ".
    rewrite iProto_client_unfold.
    wp_lam. wp_select. wp_select. by iApply "HΦ".
  Qed.

  Lemma client_spec_duplicate c prot :
    ⊢ {{{ c ↣ <|¿|> prot }}}
        client_duplicate c
      {{{ c', RET c'; c ↣ (<|¿|> prot) ∗ c' ↣ (<|¿|> prot) }}}.
  Proof.
    iIntros "!>" (Φ) "Hc HΦ".
    rewrite {1}iProto_client_unfold.
    wp_lam. wp_select. wp_select.
    wp_apply (new_chan_spec (<|¿|> prot)%proto); [ done | ].
    iIntros (c21 c22) "[Hc21 Hc22]".
    wp_send with "[Hc22//]". wp_pures.
    iApply "HΦ".
    iFrame "Hc Hc21".
  Qed.

End with_Σ.
