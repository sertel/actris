From actris.channel Require Import channel.
From actris.channel Require Import proofmode.

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

Section exponentials.
  Context `{heapG Σ, chanG Σ}.

  (** F_A(X) ≜ 1 & A & (X ⨂ X) *)
  Definition of_course_aux (A : iProto Σ) (rec : iProto Σ) : iProto Σ :=
    (END <&> (A <&> (<!(c:val)> MSG c {{ c ↣ rec }}; rec)))%proto.
  Instance of_course_aux_contractive A : Contractive (of_course_aux A).
  Proof. solve_proto_contractive. Qed.
  (** !A ≜ ν X. F_A(X) *)
  Definition of_course (A : iProto Σ) : iProto Σ := fixpoint (of_course_aux A).
  Lemma of_course_unfold A : of_course A ≡ of_course_aux A (of_course A).
  Proof. by rewrite /of_course {1}(fixpoint_unfold (of_course_aux A)). Qed.

  (** G_A(X) ≜ ⊥ ⨁ A ⨁ (X _&_ X) *)
  Definition why_not_aux (A : iProto Σ) (rec : iProto Σ) : iProto Σ :=
    (END <+> (A <+> (<?(c:val)> MSG c {{ c ↣ iProto_dual rec }}; rec)))%proto.
  Instance why_not_aux_contractive A : Contractive (why_not_aux A).
  Proof. solve_proto_contractive. Qed.
  (** ?A ≜  μ X. G_A(X) *)
  Definition why_not (A : iProto Σ) := fixpoint (why_not_aux A).
  Lemma why_not_unfold A : why_not A ≡ why_not_aux A (why_not A).
  Proof. by rewrite /why_not {1}(fixpoint_unfold (why_not_aux A)). Qed.

  (** H_A(X) ≜ ⊥ & A & (X _&_ X) *)
  Definition server_aux (A : iProto Σ) (rec : iProto Σ) : iProto Σ :=
    (END <&> (A <&> (<?(c:val)> MSG c {{ c ↣ rec }}; rec)))%proto.
  Instance server_aux_contractive A : Contractive (server_aux A).
  Proof. solve_proto_contractive. Qed.
  (** _!_A ≜ μ X. H_A(X) *)
  Definition server (A : iProto Σ) := fixpoint (server_aux A).
  Lemma server_unfold A : server A ≡ server_aux A (server A).
  Proof. by rewrite /server {1}(fixpoint_unfold (server_aux A)). Qed.

  (** K_A(X) ≜ 1 ⨁ A ⨁ (X ⨂ X) *)
  Definition client_aux (A : iProto Σ) (rec : iProto Σ) : iProto Σ :=
    (END <+> (A <+> (<!(c:val)> MSG c {{ c ↣ iProto_dual rec }}; rec)))%proto.
  Instance client_aux_contractive A : Contractive (client_aux A).
  Proof. solve_proto_contractive. Qed.
  (** _?_A ≜ μ X. K_A(X) *)
  Definition client (A : iProto Σ) := fixpoint (client_aux A).
  Lemma client_unfold A : client A ≡ client_aux A (client A).
  Proof. by rewrite /client {1}(fixpoint_unfold (client_aux A)). Qed.

  (** (?A)^⟂ = !(A^⟂)*)
  Lemma why_not_of_course_dual (A : iProto Σ) :
    iProto_dual (why_not A) ≡ of_course (iProto_dual A).
  Proof.
    apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (A).
    iEval (rewrite why_not_unfold of_course_unfold).
    rewrite iProto_dual_choice.
    rewrite iProto_dual_end.
    rewrite /server_aux.
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
    iProto_dual (client A) ≡ server (iProto_dual A).
  Proof.
    apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (A).
    iEval (rewrite client_unfold server_unfold).
    rewrite iProto_dual_choice.
    rewrite iProto_dual_end.
    rewrite /server_aux.
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

End exponentials.
