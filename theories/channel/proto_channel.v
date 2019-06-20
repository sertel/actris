From osiris.channel Require Export channel.
From osiris.channel Require Import proto_model.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import auth excl.
From osiris.utils Require Import auth_excl.

(** Camera setup *)
Class proto_chanG Σ := {
  proto_chanG_chanG :> chanG Σ;
  proto_chanG_authG :> auth_exclG (laterO (proto val (iPreProp Σ) (iPreProp Σ))) Σ;
}.

Definition proto_chanΣ := #[
  chanΣ;
  GFunctor (authRF(optionURF (exclRF (laterOF (protoOF val idOF idOF)))))
].
Instance subG_chanΣ {Σ} : subG proto_chanΣ Σ → proto_chanG Σ.
Proof. intros [??%subG_auth_exclG]%subG_inv. constructor; apply _. Qed.

(** Types and constructors *)
Definition iProto Σ := proto val (iProp Σ) (iProp Σ).
Definition iProto_cont Σ X := X -t> val * iProp Σ * iProto Σ.

Delimit Scope proto_scope with proto.
Bind Scope proto_scope with iProto.
Delimit Scope proto_cont_scope with proto_cont.
Bind Scope proto_cont_scope with iProto_cont.

Definition iProto_end {Σ} : iProto Σ := proto_end.
Program Definition iProto_message {Σ X} (a : action) (pc : iProto_cont Σ X) : iProto Σ :=
  proto_message a (λ v, λne f, ∃ x : X,
    ⌜ (tele_app pc x).1.1 = v ⌝ ∗ (tele_app pc x).1.2 ∗ f (Next (tele_app pc x).2))%I.
Next Obligation. solve_proper. Qed.
Arguments iProto_message {_ _} _ _%proto_cont.

Definition proto_exist {Σ A} {X : A → tele}
  (pc : ∀ x : A, iProto_cont Σ (X x)) : iProto_cont Σ (TeleS X) := pc.
Arguments proto_exist {_ _ _} _%proto.
Definition proto_payload {Σ} (w : val) (P : iProp Σ)
  (p : iProto Σ) : iProto_cont Σ TeleO := (w,P,p).
Arguments proto_payload {_} _%V _%I _%proto.

Notation "<!> pc" := (iProto_message Send pc)
  (at level 20, pc at level 200) : proto_scope.
Notation "<?> pc" := (iProto_message Receive pc)
  (at level 20, pc at level 200) : proto_scope.
Notation "∃ x .. y , pc" :=
  (proto_exist (λ x, .. (proto_exist (λ y, pc)) ..)%proto_cont) : proto_cont_scope.

Notation "'MSG' v {{ P }}; p" :=
  (proto_payload v P p) (at level 20, v at level 20, P, p at level 200) : proto_cont_scope.
Notation "'MSG' v ; p" :=
  (proto_payload v True p) (at level 20, v at level 20, p at level 200) : proto_cont_scope.

Definition proto_dual {Σ} (p : iProto Σ) : iProto Σ :=
  proto_map action_dual cid cid p.
Arguments proto_dual {_} _%proto.

Class IsActionDual (a1 a2 : action) :=
  is_action_dual : action_dual a1 = a2.
Instance is_action_dual_default a : IsActionDual a (action_dual a) | 100 := eq_refl.
Instance is_action_dual_Send : IsActionDual Send Receive := eq_refl.
Instance is_action_dual_Receive : IsActionDual Receive Send := eq_refl.

Class IsProtoDual {Σ} (p1 p2 : iProto Σ) :=
  is_dual_proto : proto_dual p1 ≡ p2.
Class IsProtoContDual {Σ X} (pc1 pc2 : iProto_cont Σ X) :=
  is_dual_proto_cont x : prod_map id proto_dual (tele_app pc1 x) ≡ tele_app pc2 x.

(** Invariants *)
Fixpoint proto_eval `{!proto_chanG Σ} (vs : list val) (p1 p2 : iProto Σ) : iProp Σ :=
  match vs with
  | [] => p1 ≡ proto_dual p2
  | v :: vs => ∃ pc p2',
     p2 ≡ (proto_message Receive pc)%proto ∗
     (∀ f : laterO (iProto Σ) -n> iProp Σ, f (Next p2') -∗ pc v f) ∗
     ▷ proto_eval vs p1 p2'
  end%I.
Arguments proto_eval {_ _} _ _%proto _%proto : simpl nomatch.

Record proto_name := ProtName {
  proto_c_name : chan_name;
  proto_l_name : gname;
  proto_r_name : gname
}.

Definition to_proto_auth_excl `{!proto_chanG Σ} (p : iProto Σ) :=
  to_auth_excl (Next (proto_map id iProp_fold iProp_unfold p)).

Definition proto_own_frag `{!proto_chanG Σ} (γ : proto_name) (s : side)
    (p : iProto Σ) : iProp Σ :=
  own (side_elim s proto_l_name proto_r_name γ) (◯ to_proto_auth_excl p)%I.

Definition proto_own_auth `{!proto_chanG Σ} (γ : proto_name) (s : side)
    (p : iProto Σ) : iProp Σ :=
  own (side_elim s proto_l_name proto_r_name γ) (● to_proto_auth_excl p)%I.

Definition proto_inv `{!proto_chanG Σ} (γ : proto_name) : iProp Σ :=
  (∃ l r pl pr,
    chan_own (proto_c_name γ) Left l ∗
    chan_own (proto_c_name γ) Right r ∗
    proto_own_auth γ Left pl ∗
    proto_own_auth γ Right pr ∗
    ▷ ((⌜r = []⌝ ∗ proto_eval l pl pr) ∨
       (⌜l = []⌝ ∗ proto_eval r pr pl)))%I.

Definition proto_interp `{!proto_chanG Σ, !heapG Σ} (N : namespace)
    (c : val) (p : iProto Σ) : iProp Σ :=
  (∃ s (c1 c2 : val) γ,
    ⌜ c = side_elim s c1 c2 ⌝ ∗
    proto_own_frag γ s p ∗ is_chan N (proto_c_name γ) c1 c2 ∗ inv N (proto_inv γ))%I.
Arguments proto_interp {_ _ _} _ _ _%proto.
Instance: Params (@proto_interp) 5 := {}.

Notation "c ↣ p @ N" := (proto_interp N c p)
  (at level 20, N at level 50, format "c  ↣  p  @  N").

Section proto.
  Context `{!proto_chanG Σ, !heapG Σ} (N : namespace).

  Global Instance proto_dual_ne : NonExpansive (@proto_dual Σ).
  Proof. solve_proper. Qed.
  Global Instance proto_dual_proper : Proper ((≡) ==> (≡)) (@proto_dual Σ).
  Proof. apply (ne_proper _). Qed.
  Global Instance proto_dual_involutive : Involutive (≡) (@proto_dual Σ).
  Proof.
    intros p. rewrite /proto_dual -proto_map_compose -{2}(proto_map_id p).
    apply: proto_map_ext=> //. by intros [].
  Qed.
  Lemma proto_dual_end : proto_dual (Σ:=Σ) proto_end ≡ proto_end.
  Proof. by rewrite /proto_dual proto_map_end. Qed.
  Lemma proto_dual_message a pc :
    proto_dual (Σ:=Σ) (proto_message a pc)
    ≡ proto_message (action_dual a) (ofe_morO_map (ofe_morO_map
        (laterO_map (proto_map action_dual cid cid)) cid) cid ∘ pc).
  Proof. by rewrite /proto_dual proto_map_message. Qed.

  Global Instance is_proto_dual_default (p : iProto Σ) :
    IsProtoDual p (proto_dual p) | 100.
  Proof. by rewrite /IsProtoDual. Qed.
  Global Instance is_proto_dual_end : IsProtoDual (@iProto_end Σ) iProto_end.
  Proof. by rewrite /IsProtoDual /iProto_end proto_dual_end. Qed.
  Global Instance is_proto_dual_message {X} a1 a2 (pc1 pc2 : iProto_cont Σ X) :
    IsActionDual a1 a2 →
    IsProtoContDual pc1 pc2 →
    IsProtoDual (iProto_message a1 pc1) (iProto_message a2 pc2).
  Proof.
    rewrite /IsActionDual /IsProtoContDual /IsProtoDual=> <- Hpc.
    rewrite /iProto_message proto_dual_message. f_equiv=> v f /=. f_equiv=> x.
    by destruct (Hpc x) as [[-> ->] <-].
 Qed.

  Global Instance is_proto_cont_dual_payload v P (p1 p2 : iProto Σ) :
    IsProtoDual p1 p2 →
    IsProtoContDual (proto_payload v P p1) (proto_payload v P p2).
  Proof.
    rewrite /IsProtoDual /IsProtoContDual=> Hp.
    apply tforall_forall. by rewrite /= Hp.
  Qed.
  Global Instance is_proto_cont_dual_exist {A} {X : A → tele}
      (pc1 pc2 : ∀ x : A, iProto_cont Σ (X x)) :
    (∀ x, IsProtoContDual (pc1 x) (pc2 x)) →
    IsProtoContDual (proto_exist pc1) (proto_exist pc2).
  Proof.
    rewrite /IsProtoContDual=> Hpc. apply tforall_forall=> /= x'.
    apply tforall_forall. apply Hpc.
  Qed.

  Global Instance proto_eval_ne : NonExpansive2 (proto_eval vs).
  Proof. induction vs; solve_proper. Qed.
  Global Instance proto_eval_proper vs : Proper ((≡) ==> (≡) ==> (≡)) (proto_eval vs).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance to_proto_auth_excl_ne : NonExpansive to_proto_auth_excl.
  Proof. solve_proper. Qed.
  Global Instance proto_own_ne γ s : NonExpansive (proto_own_frag γ s).
  Proof. solve_proper. Qed.
  Global Instance proto_interp_ne c : NonExpansive (proto_interp N c).
  Proof. solve_proper. Qed.
  Global Instance proto_interp_proper c : Proper ((≡) ==> (≡)) (proto_interp N c).
  Proof. apply (ne_proper _). Qed.

  Lemma proto_own_auth_agree γ s p p' :
    proto_own_auth γ s p -∗ proto_own_frag γ s p' -∗ ▷ (p ≡ p').
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
    iDestruct (to_auth_excl_valid with "Hvalid") as "Hvalid".
    iDestruct (bi.later_eq_1 with "Hvalid") as "Hvalid"; iNext.
    assert (∀ p : iProto Σ,
      proto_map id iProp_unfold iProp_fold (proto_map id iProp_fold iProp_unfold p) ≡ p) as help.
    { intros p''. rewrite -proto_map_compose -{2}(proto_map_id p'').
      apply proto_map_ext=> // pc /=; by rewrite iProp_fold_unfold. }
    rewrite -{2}(help p). iRewrite "Hvalid". by rewrite help.
  Qed.

  Lemma proto_own_auth_update γ s p p' p'' :
    proto_own_auth γ s p -∗ proto_own_frag γ s p' ==∗
    proto_own_auth γ s p'' ∗ proto_own_frag γ s p''.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_update_2 with "Hauth Hfrag") as "H".
    { eapply (auth_update _ _ (to_proto_auth_excl p'') (to_proto_auth_excl p'')).
      apply option_local_update. by apply exclusive_local_update. }
    by rewrite own_op.
  Qed.

  Lemma proto_eval_send v vs pc p1 p2 :
    proto_eval vs (proto_message Send pc) p2 -∗
    (∀ f : laterO (iProto Σ) -n> iProp Σ, f (Next p1) -∗ pc v f) -∗
    proto_eval (vs ++ [v]) p1 p2.
  Proof.
    iIntros "Heval Hc". iInduction vs as [|v' vs] "IH" forall (p2); simpl.
    - iDestruct "Heval" as "#Heval".
      iExists _, (proto_dual p1). iSplit.
      { rewrite -{2}(involutive proto_dual p2). iRewrite -"Heval".
        by rewrite proto_dual_message. }
      iSplit.
      { iIntros (f) "Hf /=". by iApply "Hc". }
      by rewrite involutive.
    - iDestruct "Heval" as (pc' p2') "(Heq & Hc' & Heval)".
      iExists pc', p2'. iFrame "Heq Hc'". iNext. iApply ("IH" with "Heval Hc").
  Qed.

  Lemma proto_eval_recv v vs p1 pc :
     proto_eval (v :: vs) p1 (proto_message Receive pc) -∗ ∃ p2,
       (∀ f : laterO (iProto Σ) -n> iProp Σ, f (Next p2) -∗ pc v f) ∗
       ▷ proto_eval vs p1 p2.
  Proof.
    simpl. iDestruct 1 as (pc' p2) "(Heq & Hc & Hp2)". iExists p2. iFrame "Hp2".
    iDestruct (@proto_message_equivI with "Heq") as "[_ Heq]".
    iSpecialize ("Heq" $! v). rewrite bi.ofe_morO_equivI.
    iIntros (f) "Hfp2". iRewrite ("Heq" $! f). by iApply "Hc".
  Qed.

  Lemma proto_eval_False p pc v vs :
    proto_eval (v :: vs) p (proto_message Send pc) -∗ False.
  Proof.
    simpl. iDestruct 1 as (pc' p2') "[Heq _]".
    by iDestruct (@proto_message_equivI with "Heq") as "[% _]".
  Qed.

  Lemma proto_eval_nil p1 p2 : proto_eval [] p1 p2 -∗ p1 ≡ proto_dual p2.
  Proof. done. Qed.

  Arguments proto_eval : simpl never.

  Lemma proto_init E cγ c1 c2 p :
    is_chan N cγ c1 c2 -∗
    chan_own cγ Left [] -∗ chan_own cγ Right [] ={E}=∗
    c1 ↣ p @ N ∗ c2 ↣ proto_dual p @ N.
  Proof.
    iIntros "#Hcctx Hcol Hcor".
    iMod (own_alloc (● (to_proto_auth_excl p) ⋅
                     ◯ (to_proto_auth_excl p))) as (lγ) "[Hlsta Hlstf]".
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● (to_proto_auth_excl (proto_dual p)) ⋅
                     ◯ (to_proto_auth_excl (proto_dual p)))) as (rγ) "[Hrsta Hrstf]".
    { by apply auth_both_valid_2. }
    pose (ProtName cγ lγ rγ) as pγ.
    iMod (inv_alloc N _ (proto_inv pγ) with "[-Hlstf Hrstf Hcctx]") as "#Hinv".
    { iNext. rewrite /proto_inv. eauto 10 with iFrame. }
    iModIntro. iSplitL "Hlstf".
    - iExists Left, c1, c2, pγ; iFrame; auto.
    - iExists Right, c1, c2, pγ; iFrame; auto.
  Qed.

  Lemma proto_send_acc {X} E c (pc : iProto_cont Σ X) :
    ↑N ⊆ E →
    c ↣ <!> pc @ N -∗ ∃ s c1 c2 γ,
      ⌜ c = side_elim s c1 c2 ⌝ ∗
      is_chan N (proto_c_name γ) c1 c2 ∗ |={E,E∖↑N}=> ∃ vs,
        chan_own (proto_c_name γ) s vs ∗
        ▷ ∀ (x : X),
           (tele_app pc x).1.2 -∗
           chan_own (proto_c_name γ) s (vs ++ [(tele_app pc x).1.1]) ={E∖↑N,E}=∗
           c ↣ (tele_app pc x).2 @ N.
  Proof.
    iIntros (?). iDestruct 1 as (s c1 c2 γ ->) "[Hstf #[Hcctx Hinv]]".
    iExists s, c1, c2, γ. iSplit; first done. iFrame "Hcctx".
    iInv N as (l r pl pr) "(>Hclf & >Hcrf & Hstla & Hstra & Hinv')" "Hclose".
    (* TODO: refactor to avoid twice nearly the same proof *)
    iModIntro. destruct s.
    - iExists _.
      iIntros "{$Hclf} !>" (x) "HP Hclf".
      iRename "Hstf" into "Hstlf".
      iDestruct (proto_own_auth_agree with "Hstla Hstlf") as "#Heq".
      iMod (proto_own_auth_update _ _ _ _ (tele_app pc x).2
        with "Hstla Hstlf") as "[Hstla Hstlf]".
      iMod ("Hclose" with "[-Hstlf]") as "_".
      { iNext. iExists _,_,_,_. iFrame "Hcrf Hstra Hstla Hclf". iLeft.
        iRewrite "Heq" in "Hinv'".
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]".
        { iSplit=> //. iApply (proto_eval_send with "Heval [HP]").
          iIntros (f) "Hf /=". iExists x. by iFrame. }
        destruct r as [|vr r]; last first.
        { iDestruct (proto_eval_False with "Heval") as %[]. }
        iSplit; first done; simpl. iRewrite (proto_eval_nil with "Heval").
        iApply (proto_eval_send _ [] with "[] [HP]").
        { by rewrite /proto_eval involutive. }
        iIntros (f) "Hf /=". iExists x. by iFrame. }
      iModIntro. iExists Left, c1, c2, γ. iFrame; auto.
    - iExists _.
      iIntros "{$Hcrf} !>" (x) "HP Hcrf".
      iRename "Hstf" into "Hstrf".
      iDestruct (proto_own_auth_agree with "Hstra Hstrf") as "#Heq".
      iMod (proto_own_auth_update _ _ _ _ (tele_app pc x).2
        with "Hstra Hstrf") as "[Hstra Hstrf]".
      iMod ("Hclose" with "[-Hstrf]") as "_".
      { iNext. iExists _, _, _, _. iFrame "Hcrf Hstra Hstla Hclf". iRight.
        iRewrite "Heq" in "Hinv'".
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]"; last first.
        { iSplit=> //. iApply (proto_eval_send with "Heval [HP]").
          iIntros (f) "Hf /=". iExists x. by iFrame. }
        destruct l as [|vl l]; last first.
        { iDestruct (proto_eval_False with "Heval") as %[]. }
        iSplit; first done; simpl. iRewrite (proto_eval_nil with "Heval").
        iApply (proto_eval_send _ [] with "[] [HP]").
        { by rewrite /proto_eval involutive. }
        iIntros (f) "Hf /=". iExists x. by iFrame. }
      iModIntro. iExists Right, c1, c2, γ. iFrame; auto.
  Qed.

  Lemma proto_recv_acc {X} E c (pc : iProto_cont Σ X) :
    ↑N ⊆ E →
    c ↣ <?> pc @ N -∗ ∃ s c1 c2 γ,
      ⌜ c = side_elim s c2 c1 ⌝ ∗
      is_chan N (proto_c_name γ) c1 c2 ∗ |={E,E∖↑N}=> ∃ vs,
        chan_own (proto_c_name γ) s vs ∗
        ▷ ((chan_own (proto_c_name γ) s vs ={E∖↑N,E}=∗
             c ↣ <?> pc @ N) ∧
           (∀ v vs',
             ⌜ vs = v :: vs' ⌝ -∗
             chan_own (proto_c_name γ) s vs' ={E∖↑N,E}=∗ ▷ ∃ x : X,
             ⌜ v = (tele_app pc x).1.1 ⌝ ∗
             ▷ c ↣ (tele_app pc x).2 @ N ∗
             (tele_app pc x).1.2)).
  Proof.
    iIntros (?). iDestruct 1 as (s c1 c2 γ ->) "[Hstf #[Hcctx Hinv]]".
    iExists (side_elim s Right Left), c1, c2, γ. iSplit; first by destruct s.
    iFrame "Hcctx".
    iInv N as (l r pl pr) "(>Hclf & >Hcrf & Hstla & Hstra & Hinv')" "Hclose".
    iExists (side_elim s r l). iModIntro.
    (* TODO: refactor to avoid twice nearly the same proof *)
    destruct s; simpl.
    - iIntros "{$Hcrf} !>".
      iRename "Hstf" into "Hstlf".
      iDestruct (proto_own_auth_agree with "Hstla Hstlf") as "#Heq".
      iSplit.
      + iIntros "Hown".
        iMod ("Hclose" with "[-Hstlf]") as "_".
        { iNext. iExists l, r, _, _. iFrame. }
        iModIntro. iExists Left, c1, c2, γ. by iFrame "Hcctx ∗ Hinv".
      + iIntros (v vs ->) "Hown".
        iDestruct "Hinv'" as "[[>% _]|[> -> Heval]]"; first done.
        iAssert (▷ proto_eval (v :: vs) pr (<?> pc))%I with "[Heval]" as "Heval".
        { iNext. by iRewrite "Heq" in "Heval". }
        iDestruct (proto_eval_recv with "Heval") as (q) "[Hf Heval]".
        iMod (proto_own_auth_update _ _ _ _ q with "Hstla Hstlf") as "[Hstla Hstlf]".
        iMod ("Hclose" with "[-Hstlf Hf]") as %_.
        { iExists _, _,_ ,_. eauto 10 with iFrame. }
        iIntros "!> !>".
        set (f p := (∃ q, p ≡ Next q ∧ c1 ↣ q @ N)%I).
        assert (NonExpansive f) by solve_proper.
        iDestruct ("Hf" $! (OfeMor f) with "[Hstlf]") as (x <-) "[HP Hf] /=".
        { iExists q. iSplit; first done. iExists Left, c1, c2, γ. iFrame; auto. }
        iExists x. iSplit; first done. iFrame "HP".
        iDestruct "Hf" as (q') "[#Hq Hc]". iModIntro. by iRewrite "Hq".
    - iIntros "{$Hclf} !>".
      iRename "Hstf" into "Hstrf".
      iDestruct (proto_own_auth_agree with "Hstra Hstrf") as "#Heq".
      iSplit.
      + iIntros "Hown".
        iMod ("Hclose" with "[-Hstrf]") as "_".
        { iNext. iExists l, r, _, _. iFrame. }
        iModIntro. iExists Right, c1, c2, γ. by iFrame "Hcctx ∗ Hinv".
      + iIntros (v vs ->) "Hown".
        iDestruct "Hinv'" as "[[>-> Heval]|[>% _]]"; last done.
        iAssert (▷ proto_eval (v :: vs) pl (<?> pc))%I with "[Heval]" as "Heval".
        { iNext. by iRewrite "Heq" in "Heval". }
        iDestruct (proto_eval_recv with "Heval") as (q) "[Hf Heval]".
        iMod (proto_own_auth_update _ _ _ _ q with "Hstra Hstrf") as "[Hstra Hstrf]".
        iMod ("Hclose" with "[-Hstrf Hf]") as %_.
        { iExists _, _, _, _. eauto 10 with iFrame. }
        iIntros "!> !>".
        set (f p := (∃ q, p ≡ Next q ∧ c2 ↣ q @ N)%I).
        assert (NonExpansive f) by solve_proper.
        iDestruct ("Hf" $! (OfeMor f) with "[Hstrf]") as (x <-) "[HP Hf] /=".
        { iExists q. iSplit; first done. iExists Right, c1, c2, γ. iFrame; auto. }
        iExists x. iSplit; first done. iFrame "HP".
        iDestruct "Hf" as (q') "[#Hq Hc]". iModIntro. by iRewrite "Hq".
  Qed.

  Lemma new_chan_proto_spec p1 p2 :
    IsProtoDual p1 p2 →
    {{{ True }}}
      new_chan #()
    {{{ c1 c2, RET (c1,c2); c1 ↣ p1 @ N ∗ c2 ↣ p2 @ N }}}.
  Proof.
    rewrite /IsProtoDual.
    iIntros (Hp2 Ψ _) "HΨ". iApply wp_fupd. wp_apply new_chan_spec=> //.
    iIntros (c1 c2 γ) "(Hc & Hl & Hr)".
    iMod (proto_init ⊤ γ c1 c2 p1 with "Hc Hl Hr") as "[Hp Hdp]".
    iApply "HΨ". rewrite -Hp2. by iFrame.
  Qed.

  Lemma send_proto_spec_packed {X} c (pc : iProto_cont Σ X) (x : X) :
    {{{ c ↣ <!> pc @ N ∗ (tele_app pc x).1.2 }}}
      send c (tele_app pc x).1.1
    {{{ RET #(); c ↣ (tele_app pc x).2 @ N }}}.
  Proof.
    iIntros (Ψ) "[Hp Hf] HΨ".
    iDestruct (proto_send_acc ⊤ with "Hp") as (γ s c1 c2 ->) "[#Hc Hvs]"; first done.
    iApply (send_spec with "[$]"). iMod "Hvs" as (vs) "[Hch H]".
    iModIntro. iExists vs. iFrame "Hch".
    iIntros "!> Hvs". iApply "HΨ".
    iMod ("H" $! x with "Hf Hvs"); auto.
  Qed.

  Lemma send_proto_spec {X} Ψ c v (pc : iProto_cont Σ X) :
    c ↣ <!> pc @ N -∗
    (∃.. x : X,
      ⌜ v = (tele_app pc x).1.1 ⌝ ∗
      (tele_app pc x).1.2 ∗
      (c ↣ (tele_app pc x).2 @ N -∗ Ψ #())) -∗
    WP send c v {{ Ψ }}.
  Proof.
    iIntros "Hc H". iDestruct (bi_texist_exist with "H") as (x ->) "[HP HΨ]".
    by iApply (send_proto_spec_packed with "[$]").
  Qed.

  Lemma try_recv_proto_spec_packed {X} c (pc : iProto_cont Σ X) :
    {{{ c ↣ <?> pc @ N }}}
      try_recv c
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ c ↣ <?> pc @ N) ∨
                  (∃ x : X, ⌜v = SOMEV ((tele_app pc x).1.1)⌝ ∗
                            c ↣ (tele_app pc x).2 @ N ∗ (tele_app pc x).1.2) }}}.
  Proof.
    iIntros (Ψ) "Hp HΨ".
    iDestruct (proto_recv_acc ⊤ with "Hp") as (γ s c1 c2 ->) "[#Hc Hvs]"; first done.
    wp_apply (try_recv_spec with "[$]"). iSplit.
    - iMod "Hvs" as (vs) "[Hch [H _]]".
      iIntros "!> !>". iMod ("H" with "Hch") as "Hch". iApply "HΨ"; auto.
    - iMod "Hvs" as (vs) "[Hch [_ H]]".
      iIntros "!>". iExists vs. iIntros "{$Hch} !>" (v vs' ->) "Hch".
      iMod ("H" with "[//] Hch") as "H"; iIntros "!> !>".
      iDestruct "H" as (x ->) "H". iIntros "!>". iApply "HΨ"; auto.
  Qed.

  Lemma recv_proto_spec_packed {X} c (pc : iProto_cont Σ X) :
    {{{ c ↣ <?> pc @ N }}}
      recv c
    {{{ x, RET (tele_app pc x).1.1;
        c ↣ (tele_app pc x).2 @ N ∗ (tele_app pc x).1.2 }}}.
  Proof.
    iIntros (Ψ) "Hp HΨ".
    iDestruct (proto_recv_acc ⊤ with "Hp") as (γ s c1 c2 ->) "[#Hc Hvs]"; first done.
    wp_apply (recv_spec with "[$]"). iMod "Hvs" as (vs) "[Hch [_ H]]".
    iModIntro. iExists vs. iFrame "Hch". iIntros "!>" (v vs' ->) "Hvs'".
    iMod ("H" with "[//] Hvs'") as "H"; iIntros "!> !>".
    iDestruct "H" as (x ->) "H". iIntros "!>". by iApply "HΨ".
  Qed.

  Lemma recv_proto_spec {X} Ψ c (pc : iProto_cont Σ X) :
    c ↣ <?> pc @ N -∗
    (∀.. x : X, c ↣ (tele_app pc x).2 @ N -∗
                (tele_app pc x).1.2 -∗ Ψ (tele_app pc x).1.1) -∗
    WP recv c {{ Ψ }}.
  Proof.
    iIntros "Hc H". iApply (recv_proto_spec_packed with "[$]").
    iIntros "!>" (x) "[Hc HP]". iDestruct (bi_tforall_forall with "H") as "H".
    iApply ("H" with "[$] [$]").
  Qed.
End proto. 
