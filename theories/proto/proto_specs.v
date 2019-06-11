From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants.
From osiris.base_logic Require Import auth_excl.
From osiris.proto Require Export proto_def.
From osiris.proto Require Export channel.

Class logrelG A Σ := {
  logrelG_channelG :> chanG Σ;
  logrelG_authG :> auth_exclG (laterC (protoC A (iPreProp Σ))) Σ;
}.

Definition logrelΣ A :=
  #[ chanΣ ; GFunctor (authRF(optionURF (exclRF
                       (laterCF (@protoCF A idCF))))) ].
Instance subG_chanΣ {A Σ} : subG (logrelΣ A) Σ → logrelG A Σ.
Proof. intros [??%subG_auth_exclG]%subG_inv. constructor; apply _. Qed.

Fixpoint prot_eval `{!logrelG val Σ} (vs : list val) (prot1 prot2 : proto val (iProp Σ)) : iProp Σ :=
  match vs with
  | [] => prot1 ≡ dual_proto prot2
  | v::vs => match prot2 with
             | TSR Receive P prot2  => P v ∗ ▷ prot_eval vs prot1 (prot2 v)
             | _ => False
             end
  end%I.
Arguments prot_eval : simpl nomatch.

Record prot_name := ProtName {
  prot_c_name : chan_name;
  prot_l_name : gname;
  prot_r_name : gname
}.

Definition to_proto_auth_excl `{!logrelG val Σ} (prot : proto val (iProp Σ)) :=
  to_auth_excl (Next (proto_map iProp_unfold prot)).

Definition prot_own `{!logrelG val Σ} (γ : prot_name) (s : side)
    (prot : proto val (iProp Σ)) : iProp Σ :=
  own (side_elim s prot_l_name prot_r_name γ) (◯ to_proto_auth_excl prot)%I.

Definition prot_ctx `{!logrelG val Σ} (γ : prot_name) (s : side)
    (prot : proto val (iProp Σ)) : iProp Σ :=
  own (side_elim s prot_l_name prot_r_name γ) (● to_proto_auth_excl prot)%I.

Definition inv_prot `{!logrelG val Σ} (γ : prot_name) (c : val) : iProp Σ :=
  (∃ l r protl protr,
    chan_own (prot_c_name γ) Left l ∗
    chan_own (prot_c_name γ) Right r ∗
    prot_ctx γ Left protl  ∗
    prot_ctx γ Right protr ∗
    ▷ ((⌜r = []⌝ ∗ prot_eval l protl protr) ∨
       (⌜l = []⌝ ∗ prot_eval r protr protl)))%I.

Definition interp_prot `{!logrelG val Σ, !heapG Σ} (N : namespace) (γ : prot_name)
    (c : val) (s : side) (prot : proto val (iProp Σ)) : iProp Σ :=
  (prot_own γ s prot ∗ is_chan N (prot_c_name γ) c ∗ inv N (inv_prot γ c))%I.
Instance: Params (@interp_prot) 7.

Notation "⟦ c @ s : prot ⟧{ N , γ }" := (interp_prot N γ c s prot)
  (at level 10, s at next level, prot at next level, γ at next level,
   format "⟦  c  @  s  :  prot  ⟧{ N , γ }").

Section proto.
  Context `{!logrelG val Σ, !heapG Σ} (N : namespace).

  Global Instance prot_eval_ne : NonExpansive2 (prot_eval vs).
  Proof.
    induction vs as [|v vs IH];
      destruct 2 as [n|[] P1 P2 prot1 prot2|n [] P1 P2 prot1 prot2]=> //=.
    - by repeat f_equiv.
    - f_equiv. done. f_equiv. by constructor.
    - f_equiv. done. f_equiv. by constructor.
    - f_equiv. done. f_equiv. by constructor.
    - f_equiv. done. f_equiv. by constructor.
    - f_equiv. done. by f_contractive.
    - f_equiv. done. f_contractive. apply IH. by apply dist_S. done.
  Qed.
  Global Instance prot_eval_proper vs : Proper ((≡) ==> (≡) ==> (≡)) (prot_eval vs).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance to_proto_auth_excl_ne : NonExpansive to_proto_auth_excl.
  Proof. solve_proper. Qed.
  Global Instance prot_own_ne γ s : NonExpansive (prot_own γ s).
  Proof. solve_proper. Qed.
  Global Instance interp_st_ne γ c s : NonExpansive (interp_prot N γ c s).
  Proof. solve_proper. Qed.
  Global Instance interp_st_proper γ c s : Proper ((≡) ==> (≡)) (interp_prot N γ c s).
  Proof. apply (ne_proper _). Qed.

  Lemma prot_excl_eq γ s prot prot' :
    prot_ctx γ s prot -∗ prot_own γ s prot' -∗ ▷ (prot ≡ prot').
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
    iDestruct (to_auth_excl_valid with "Hvalid") as "Hvalid".
    iDestruct (bi.later_eq_1 with "Hvalid") as "Hvalid"; iNext.
    assert (∀ prot : proto val (iProp Σ),
      proto_map iProp_fold (proto_map iProp_unfold prot) ≡ prot) as help.
    { intros prot''. rewrite -proto_fmap_compose -{2}(proto_fmap_id prot'').
      apply proto_map_ext=> P. by rewrite /= iProp_fold_unfold. }
    rewrite -{2}(help prot). iRewrite "Hvalid". by rewrite help.
  Qed.

  Lemma prot_excl_update γ s prot prot' prot'' :
    prot_ctx γ s prot -∗ prot_own γ s prot' ==∗ prot_ctx γ s prot'' ∗ prot_own γ s prot''.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_update_2 with "Hauth Hfrag") as "H".
    { eapply (auth_update _ _ (to_proto_auth_excl prot'')
                              (to_proto_auth_excl prot'')).
      eapply option_local_update.
      eapply exclusive_local_update. done. }
    by rewrite own_op.
  Qed.

  Lemma prot_eval_send (P : val →iProp Σ) prot vs v protr :
    P v -∗ prot_eval vs (<!> @ P, prot) protr -∗ prot_eval (vs ++ [v]) (prot v) protr.
  Proof.
    iIntros "HP".
    iRevert (protr).
    iInduction vs as [|v' vs] "IH"; iIntros (protr) "Heval".
    - iDestruct (dual_proto_flip with "Heval") as "Heval".
      iRewrite -"Heval"; simpl.
      rewrite dual_proto_involutive.
      by iFrame.
    - destruct protr as [|[] P' protr]=> //=.
      iDestruct "Heval" as "[$ Heval]".
      by iApply ("IH" with "HP").
  Qed.

  Lemma prot_eval_recv (P : val → iProp Σ) prot1 l prot2 v :
     prot_eval (v :: l) prot1 (<?> @ P, prot2) -∗ ▷ prot_eval l prot1 (prot2 v) ∗ P v.
  Proof. iDestruct 1 as "[HP Heval]". iFrame. Qed.

  Lemma new_chan_vs prot E c cγ :
    is_chan N cγ c ∗
    chan_own cγ Left [] ∗
    chan_own cγ Right [] ={E}=∗ ∃ lγ rγ,
      let γ := ProtName cγ lγ rγ in
      ⟦ c @ Left : prot ⟧{N,γ} ∗ ⟦ c @ Right : dual_proto prot ⟧{N,γ}.
  Proof.
    iIntros "[#Hcctx [Hcol Hcor]]".
    iMod (own_alloc (● (to_proto_auth_excl prot) ⋅
                     ◯ (to_proto_auth_excl prot))) as (lγ) "[Hlsta Hlstf]".
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● (to_proto_auth_excl (dual_proto prot)) ⋅
                     ◯ (to_proto_auth_excl (dual_proto prot)))) as (rγ) "[Hrsta Hrstf]".
    { by apply auth_both_valid_2. }
    pose (ProtName cγ lγ rγ) as protγ.
    iMod (inv_alloc N _ (inv_prot protγ c) with "[-Hlstf Hrstf Hcctx]") as "#Hinv".
    { iNext. rewrite /inv_prot. eauto 10 with iFrame. }
    iModIntro.
    iExists _, _.
    iFrame "Hlstf Hrstf Hcctx Hinv".
  Qed.

  Lemma new_chan_st_spec prot1 prot2 :
    IsDualProto prot1 prot2 →
    {{{ True }}}
      new_chan #()
    {{{ c γ, RET c; ⟦ c @ Left : prot1 ⟧{N,γ} ∗ ⟦ c @ Right : prot2 ⟧{N,γ} }}}.
  Proof.
    rewrite /IsDualProto.
    iIntros (Hprot Φ _) "HΦ".
    iApply (wp_fupd).
    iApply (new_chan_spec)=> //.
    iModIntro.
    iIntros (c γ) "[Hc Hctx]".
    iMod (new_chan_vs prot1 ⊤ c γ with "[-HΦ]") as "H".
    { rewrite /is_chan. eauto with iFrame. }
    iDestruct "H" as (lγ rγ) "[Hl Hr]".
    iApply "HΦ".
    rewrite Hprot.
    by iFrame.
  Qed.

  Lemma send_vs c γ s (P : val → iProp Σ) prot E :
    ↑N ⊆ E →
    ⟦ c @ s : TSR Send P prot ⟧{N,γ} ={E,E∖↑N}=∗ ∃ vs,
      chan_own (prot_c_name γ) s vs ∗
      ▷ ∀ v, P v -∗
             chan_own (prot_c_name γ) s (vs ++ [v]) ={E∖↑N,E}=∗
             ⟦ c @ s : prot v ⟧{N,γ}.
  Proof.
    iIntros (Hin) "[Hstf #[Hcctx Hinv]]".
    iInv N as (l r protl protr) "(>Hclf & >Hcrf & Hstla & Hstra & Hinv')" "Hclose".
    iModIntro.
    destruct s.
    - iExists _.
      iIntros "{$Hclf} !>" (v) "HP Hclf".
      iRename "Hstf" into "Hstlf".
      iDestruct (prot_excl_eq with "Hstla Hstlf") as "#Heq".
      iMod (prot_excl_update _ _ _ _ (prot v) with "Hstla Hstlf") as "[Hstla Hstlf]".
      iMod ("Hclose" with "[-Hstlf]") as "_".
      { iNext.
        iExists _,_,_,_. iFrame.
        iLeft.
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]".
        - iSplit=> //.
          iApply (prot_eval_send with "HP").
          by iRewrite "Heq" in "Heval".
        - iRewrite "Heq" in "Heval". destruct r as [|vr r]=> //=.
          iSplit; first done.
          iRewrite "Heval". simpl. iFrame "HP". by rewrite dual_proto_involutive. }
      iModIntro. iFrame. auto.
    - iExists _.
      iIntros "{$Hcrf} !>" (v) "HP Hcrf".
      iRename "Hstf" into "Hstrf".
      iDestruct (prot_excl_eq with "Hstra Hstrf") as "#Heq".
      iMod (prot_excl_update _ _ _ _ (prot v) with "Hstra Hstrf") as "[Hstra Hstrf]".
      iMod ("Hclose" with "[-Hstrf]") as "_".
      { iNext.
        iExists _, _, _, _. iFrame.
        iRight.
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]".
        - iRewrite "Heq" in "Heval". destruct l as [|vl l]=> //.
          iSplit; first done. simpl.
          iRewrite "Heval". simpl. iFrame "HP". by rewrite dual_proto_involutive.
        - iSplit=> //.
          iApply (prot_eval_send with "HP").
          by iRewrite "Heq" in "Heval". }
      iModIntro. iFrame. auto.
  Qed.

  Lemma send_st_spec prot γ c s (P : val → iProp Σ) v :
    {{{ P v ∗ ⟦ c @ s : <!> @ P , prot ⟧{N,γ} }}}
      send c #s v
    {{{ RET #(); ⟦ c @ s : prot v ⟧{N,γ} }}}.
  Proof.
    iIntros (Φ) "[HP Hsend] HΦ".
    iApply (send_spec with "[#]").
    { iDestruct "Hsend" as "[? [$ ?]]". }
    iMod (send_vs with "Hsend") as (vs) "[Hch H]"; first done.
    iModIntro. iExists vs. iFrame "Hch".
    iIntros "!> Hupd". iApply "HΦ".
    iApply ("H" $! v with "HP"). by destruct s.
  Qed.

  Lemma try_recv_vs c γ s (P : val → iProp Σ) prot E :
    ↑N ⊆ E →
    ⟦ c @ s : TSR Receive P prot ⟧{N,γ} ={E,E∖↑N}=∗ ∃ vs,
      chan_own (prot_c_name γ) (dual_side s) vs ∗
      ▷ ((⌜vs = []⌝ -∗
           chan_own (prot_c_name γ) (dual_side s) vs ={E∖↑N,E}=∗
           ⟦ c @ s : TSR Receive P prot ⟧{N,γ}) ∧
         (∀ v vs',
           ⌜vs = v :: vs'⌝ -∗
           chan_own (prot_c_name γ) (dual_side s) vs' ={E∖↑N,E}=∗
           ⟦ c @ s : (prot v) ⟧{N,γ} ∗ ▷ P v)).
  Proof.
    iIntros (Hin) "[Hstf #[Hcctx Hinv]]".
    iInv N as (l r protl protr) "(>Hclf & >Hcrf & Hstla & Hstra & Hinv')" "Hclose".
    iExists (side_elim s r l). iModIntro.
    destruct s; simpl.
    - iIntros "{$Hcrf} !>".
      iRename "Hstf" into "Hstlf".
      iDestruct (prot_excl_eq with "Hstla Hstlf") as "#Heq".
      iSplit.
      + iIntros (->) "Hown".
        iMod ("Hclose" with "[-Hstlf]") as "_".
        { iNext. iExists l, [], _, _. iFrame. }
        iModIntro. iFrame "Hcctx ∗ Hinv".
      + iIntros (v vs ->) "Hown".
        iDestruct "Hinv'" as "[[>% _]|[> -> Heval]]"; first done.
        iMod (prot_excl_update _ _ _ _ (prot v) with "Hstla Hstlf") as "[Hstla Hstlf]".
        iDestruct (proto_later_equiv with "Heq") as ">Hleq".
        iDestruct "Hleq" as (P1 prot1) "(Hsteq & HPeq & Hsteq')".
        iRewrite "Hsteq" in "Heval".
        iDestruct (prot_eval_recv with "Heval") as "[Heval HP]".
        iMod ("Hclose" with "[-Hstlf HP]") as "H".
        { iExists _, _,_ ,_. iFrame. iRight.
          iNext. iSplit=> //. iNext. by iRewrite -("Hsteq'" $! v). }
        iModIntro. iFrame "Hstlf Hcctx Hinv".
        iNext. by iRewrite -("HPeq" $! v).
    - iIntros "{$Hclf} !>".
      iRename "Hstf" into "Hstrf".
      iDestruct (prot_excl_eq with "Hstra Hstrf") as "#Heq".
      iSplit=> //.
      + iIntros (->) "Hown".
        iMod ("Hclose" with "[-Hstrf]") as "_".
        { iNext. iExists [], r, _, _. iFrame. }
        iModIntro. iFrame "Hcctx ∗ Hinv".
      + iIntros (v vs' ->) "Hown".
        iDestruct "Hinv'" as "[[>-> Heval]|[>% Heval]]"; last done.
        iMod (prot_excl_update _ _ _ _ (prot v) with "Hstra Hstrf") as "[Hstra Hstrf]".
        iDestruct (proto_later_equiv with "Heq") as ">Hleq".
        iDestruct "Hleq" as (P1 prot1) "(Hsteq & HPeq & Hsteq')".
        iRewrite "Hsteq" in "Heval".
        iDestruct (prot_eval_recv with "Heval") as "[Heval HP]".
        iMod ("Hclose" with "[-Hstrf HP]") as "_".
        { iExists _, _, _, _. iFrame. iLeft.
          iNext. iSplit=> //. iNext. by iRewrite -("Hsteq'" $! v). }
        iModIntro. iFrame "Hstrf Hcctx Hinv".
        iNext. by iRewrite -("HPeq" $! v).
  Qed.

  Lemma try_recv_st_spec prot γ c s (P : val → iProp Σ) :
    {{{ ⟦ c @ s : <?> @ P , prot ⟧{N,γ} }}}
      try_recv c #s
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⟦ c @ s : <?> @ P, prot ⟧{N,γ}) ∨
                  (∃ w, ⌜v = SOMEV w⌝ ∧ ⟦ c @ s : prot w ⟧{N,γ} ∗ ▷ P w)}}}.
  Proof.
    iIntros (Φ) "Hrecv HΦ".
    iApply (try_recv_spec with "[#]").
    { iDestruct "Hrecv" as "[? [$ ?]]". }
    iMod (try_recv_vs with "Hrecv") as (vs) "[Hch H]"; first done.
    iModIntro. iExists vs. iFrame "Hch".
    iIntros "!>".
    iSplit.
    - iIntros (Hvs) "Hown".
      iDestruct "H" as "[H _]".
      iMod ("H" $!Hvs with "Hown") as "H".
      iModIntro.
      iApply "HΦ"=> //.
      eauto with iFrame.
    - iIntros (v vs' Hvs) "Hown".
      iDestruct "H" as "[_ H]".
      iMod ("H" $!v vs' Hvs with "Hown") as "H".
      iModIntro.
      iApply "HΦ"; eauto with iFrame.
  Qed.

  Lemma recv_st_spec prot γ c s (P : val → iProp Σ) :
    {{{ ⟦ c @ s : <?> @ P ,  prot ⟧{N,γ} }}}
      recv c #s
    {{{ v, RET v; ⟦ c @ s : prot v ⟧{N,γ} ∗ P v }}}.
  Proof.
    iIntros (Φ) "Hrecv HΦ".
    iLöb as "IH". wp_rec.
    wp_apply (try_recv_st_spec with "Hrecv").
    iIntros (v) "H".
    iDestruct "H" as "[[-> H]| H]".
    - wp_pures. by iApply ("IH" with "[H]").
    - iDestruct "H" as (w ->) "[H HP]".
      wp_pures. iApply "HΦ". iFrame.
  Qed.
End proto. 
