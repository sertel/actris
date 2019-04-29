From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants.
From osiris.typing Require Export stype.
From osiris.encodings Require Import auth_excl.
From osiris.encodings Require Export channel.

Class logrelG A Σ := {
  logrelG_channelG :> chanG Σ;
  logrelG_authG :> auth_exclG (laterC (stypeC A (iPreProp Σ))) Σ;
}.

Definition logrelΣ A :=
  #[ chanΣ ; GFunctor (authRF(optionURF (exclRF
                       (laterCF (@stypeCF A idCF))))) ].
Instance subG_chanΣ {A Σ} : subG (logrelΣ A) Σ → logrelG A Σ.
Proof. intros [??%subG_auth_exclG]%subG_inv. constructor; apply _. Qed.

Section stype_interp.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG val Σ}.

  Record st_name := SessionType_name {
    st_c_name : chan_name;
    st_l_name : gname;
    st_r_name : gname
  }.

  Definition to_stype_auth_excl (st : stype val (iProp Σ)) :=
    to_auth_excl (Next (stype_map iProp_unfold st)).

  Definition st_own (γ : st_name) (s : side)
             (st : stype val (iProp Σ)) : iProp Σ :=
    own (side_elim s st_l_name st_r_name γ)
        (◯ to_stype_auth_excl st)%I.

  Definition st_ctx (γ : st_name) (s : side)
             (st : stype val (iProp Σ)) : iProp Σ :=
    own (side_elim s st_l_name st_r_name γ)
        (● to_stype_auth_excl st)%I.

  Lemma st_excl_eq γ s st st' :
    st_ctx γ s st -∗ st_own γ s st' -∗ ▷ (st ≡ st').
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
    iDestruct (to_auth_excl_valid with "Hvalid") as "Hvalid".
    iDestruct (bi.later_eq_1 with "Hvalid") as "Hvalid"; iNext.
    assert (∀ st : stype val (iProp Σ),
      stype_map iProp_fold (stype_map iProp_unfold st) ≡ st) as help.
    { intros st''. rewrite -stype_fmap_compose -{2}(stype_fmap_id st'').
      apply stype_map_ext=> P. by rewrite /= iProp_fold_unfold. }
    rewrite -{2}(help st). iRewrite "Hvalid". by rewrite help.
  Qed.

  Lemma st_excl_update γ s st st' st'' :
    st_ctx γ s st -∗ st_own γ s st' ==∗
    st_ctx γ s st'' ∗ st_own γ s st''.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_update_2 with "Hauth Hfrag") as "H".
    { eapply (auth_update _ _ (to_stype_auth_excl st'')
                              (to_stype_auth_excl st'')).
      eapply option_local_update.
      eapply exclusive_local_update. done. }
    rewrite own_op.
    done.
  Qed.

  Fixpoint st_eval (vs : list val) (st1 st2 : stype val (iProp Σ)) : iProp Σ :=
    match vs with
    | [] => st1 ≡ dual_stype st2
    | v::vs => match st2 with
               | TReceive P st2  => P v ∗ st_eval vs st1 (st2 v)
               | _ => False
               end
    end%I.
  Arguments st_eval : simpl nomatch.

  Lemma st_later_eq a P2 (st : stype val (iProp Σ)) st2 :
    (▷ (st ≡ TSR a P2 st2) -∗
         ◇ (∃ P1 st1, st ≡ TSR a P1 st1 ∗
                       ▷ ((∀ v, P1 v ≡ P2 v)) ∗
                       ▷ ((∀ v, st1 v ≡ st2 v))) : iProp Σ).
  Proof.
    destruct st.
    - iIntros "Heq".
      iDestruct (stype_equivI with "Heq") as ">Heq".
      done.
    - iIntros "Heq".
      iDestruct (stype_equivI with "Heq") as "Heq".
      iDestruct ("Heq") as "[>Haeq [HPeq Hsteq]]".
      iDestruct "Haeq" as %Haeq.
      subst.
      iExists P, st.
      iSplit=> //.
      by iSplitL "HPeq".
  Qed.

  Global Instance st_eval_ne : NonExpansive2 (st_eval vs).
  Proof.
    intros vs n. induction vs as [|v vs IH]; [solve_proper|].
    destruct 2 as [|[] ????? Hst]=> //=. f_equiv. solve_proper.
    by apply IH, Hst.
  Qed.

  Lemma st_eval_send (P : val -> iProp Σ) st l str v :
    P v -∗ st_eval l (TSend P st) str -∗ st_eval (l ++ [v]) (st v) str.
  Proof.
    iIntros "HP".
    iRevert (str).
    iInduction l as [|l] "IH"; iIntros (str) "Heval".
    - simpl.
      iDestruct (dual_stype_flip with "Heval") as "Heval".
      iRewrite -"Heval". simpl.
      rewrite dual_stype_involutive.
      by iFrame.
    - simpl.
      destruct str; auto.
      destruct a; auto.
      iDestruct "Heval" as "[HP0 Heval]".
      iFrame.
      by iApply ("IH" with "HP").
  Qed.

  Lemma st_eval_recv (P : val → iProp Σ) st1 l st2 v :
     st_eval (v :: l) st1 (TReceive P st2) -∗ st_eval l st1 (st2 v) ∗ P v.
  Proof. iDestruct 1 as "[HP Heval]". iFrame. Qed.

  Definition inv_st (γ : st_name) (c : val) : iProp Σ :=
    (∃ l r stl str,
      chan_own (st_c_name γ) Left l ∗
      chan_own (st_c_name γ) Right r ∗
      st_ctx γ Left stl  ∗
      st_ctx γ Right str ∗
      ((⌜r = []⌝ ∗ st_eval l stl str) ∨
       (⌜l = []⌝ ∗ st_eval r str stl)))%I.

  Definition is_st (γ : st_name) (st : stype val (iProp Σ))
      (c : val) : iProp Σ :=
    (is_chan N (st_c_name γ) c ∗ inv N (inv_st γ c))%I.

  Definition interp_st (γ : st_name) (st : stype val (iProp Σ))
      (c : val) (s : side) : iProp Σ :=
    (st_own γ s st ∗ is_st γ st c)%I.

  Global Instance interp_st_proper γ : Proper ((≡) ==> (=) ==> (=) ==> (≡)) (interp_st γ).
  Proof.
    intros st1 st2 Heq v1 v2 <- s1 s2 <-.
    iSplit;
    iIntros "[Hown Hctx]";
    iFrame;
    unfold st_own;
    iApply (own_mono with "Hown");
    apply (auth_frag_mono);
    apply Some_included;
    left;
    f_equiv;
    f_equiv;
    apply stype_map_equiv=> //.
  Qed.

  Notation "⟦ c @ s : sτ ⟧{ γ }" := (interp_st γ sτ c s)
    (at level 10, s at next level, sτ at next level, γ at next level,
     format "⟦  c  @  s  :  sτ  ⟧{ γ }").

  Lemma new_chan_vs st E c cγ :
    is_chan N cγ c ∗
    chan_own cγ Left [] ∗
    chan_own cγ Right []
    ={E}=∗
      ∃ lγ rγ,
        let γ := SessionType_name cγ lγ rγ in
        ⟦ c @ Left : st ⟧{γ} ∗ ⟦ c @ Right : dual_stype st ⟧{γ}.
  Proof.
    iIntros "[#Hcctx [Hcol Hcor]]".
    iMod (own_alloc (● (to_stype_auth_excl st) ⋅
                     ◯ (to_stype_auth_excl st)))
      as (lγ) "[Hlsta Hlstf]"; first done.
    iMod (own_alloc (● (to_stype_auth_excl (dual_stype st)) ⋅
                     ◯ (to_stype_auth_excl (dual_stype st))))
      as (rγ) "[Hrsta Hrstf]"; first done.
    pose (SessionType_name cγ lγ rγ) as stγ.
    iMod (inv_alloc N _ (inv_st stγ c) with "[-Hlstf Hrstf Hcctx]") as "#Hinv".
    { iNext. rewrite /inv_st. eauto 10 with iFrame. }
    iModIntro.
    iExists _, _.
    iFrame "Hlstf Hrstf Hcctx Hinv".
  Qed.

  Lemma new_chan_st_spec st1 st2 :
    IsDualStype st1 st2 →
    {{{ True }}}
      new_chan #()
    {{{ c γ, RET c;  ⟦ c @ Left : st1 ⟧{γ} ∗
                     ⟦ c @ Right : st2 ⟧{γ} }}}.
  Proof.
    rewrite /IsDualStype.
    iIntros (Hst Φ _) "HΦ".
    iApply (wp_fupd).
    iApply (new_chan_spec)=> //.
    iModIntro.
    iIntros (c γ) "[Hc Hctx]".
    iMod (new_chan_vs st1 ⊤ c γ with "[-HΦ]") as "H".
    { rewrite /is_chan. eauto with iFrame. }
    iDestruct "H" as (lγ rγ) "[Hl Hr]".
    iApply "HΦ".
    rewrite Hst.
    by iFrame.        
  Qed.

  Lemma send_vs c γ s (P : val → iProp Σ) st E :
    ↑N ⊆ E →
    ⟦ c @ s : TSend P st ⟧{γ} ={E,E∖↑N}=∗
      ∃ vs, chan_own (st_c_name γ) s vs ∗
      ▷ (∀ v, P v -∗
              chan_own (st_c_name γ) s (vs ++ [v])
              ={E∖ ↑N,E}=∗ ⟦ c @ s : st v ⟧{γ}).
  Proof.
    iIntros (Hin) "[Hstf #[Hcctx Hinv]]".
    iMod (inv_open with "Hinv") as "Hinv'"=> //.
    iDestruct "Hinv'" as "[Hinv' Hinvstep]".
    iDestruct "Hinv'" as
        (l r stl str) "(>Hclf & >Hcrf & Hstla & Hstra & Hinv')".
    iModIntro.
    destruct s.
    - iExists _.
      iIntros "{$Hclf} !>" (v) "HP Hclf".
      iRename "Hstf" into "Hstlf".
      iDestruct (st_excl_eq with "Hstla Hstlf") as "#Heq".
      iMod (st_excl_update _ _ _ _ (st v) with "Hstla Hstlf")
        as "[Hstla Hstlf]".
      iMod ("Hinvstep" with "[-Hstlf]") as "_".
      {
        iNext.
        iExists _,_,_,_. iFrame.
        iLeft.
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]".
        - iSplit=> //.
          iApply (st_eval_send with "HP").
          by iRewrite -"Heq".
        - iRewrite "Heq" in "Heval". destruct r as [|vr r]=> //.
          iSplit; first done. simpl.
          iRewrite "Heval". simpl. iFrame "HP". by rewrite involutive.
      }
      iModIntro. iFrame. rewrite /is_st. auto.
    - iExists _.
      iIntros "{$Hcrf} !>" (v) "HP Hcrf".
      iRename "Hstf" into "Hstrf".
      iDestruct (st_excl_eq with "Hstra Hstrf") as "#Heq".
      iMod (st_excl_update _ _ _ _ (st v) with "Hstra Hstrf")
        as "[Hstra Hstrf]".
      iMod ("Hinvstep" with "[-Hstrf]") as "_".
      {
        iNext.
        iExists _,_,_,_. iFrame.
        iRight.
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]".
        - iRewrite "Heq" in "Heval". destruct l as [|vl l]=> //.
          iSplit; first done. simpl.
          iRewrite "Heval". simpl. iFrame "HP". by rewrite involutive.
        - iSplit=> //.
          iApply (st_eval_send with "HP").
            by iRewrite -"Heq".
      }
      iModIntro. iFrame. rewrite /is_st. auto.
  Qed.

  Lemma send_st_spec st γ c s (P : val → iProp Σ) v :
    {{{ P v ∗ ⟦ c @ s : TSend P st ⟧{γ} }}}
      send c #s v
    {{{ RET #(); ⟦ c @ s : st v ⟧{γ} }}}.
  Proof.
    iIntros (Φ) "[HP Hsend] HΦ".
    iApply (send_spec with "[#]").
    { iDestruct "Hsend" as "[? [$ ?]]". }
    iMod (send_vs with "Hsend") as (vs) "[Hch H]"; first done.
    iModIntro. iExists vs. iFrame "Hch".
    iIntros "!> Hupd". iApply "HΦ".
    iApply ("H" $! v with "HP"). by destruct s.
  Qed.

  Lemma try_recv_vs c γ s (P : val → iProp Σ) st E :
    ↑N ⊆ E →
    ⟦ c @ s : TReceive P st ⟧{γ}
    ={E,E∖↑N}=∗
      ∃ vs, chan_own (st_c_name γ) (dual_side s) vs ∗
      (▷ ((⌜vs = []⌝ -∗ chan_own (st_c_name γ) (dual_side s) vs ={E∖↑N,E}=∗
           ⟦ c @ s : TReceive P st ⟧{γ}) ∧
          (∀ v vs', ⌜vs = v :: vs'⌝ -∗
               chan_own (st_c_name γ) (dual_side s) vs' -∗ |={E∖↑N,E}=>
               ⟦ c @ s : (st v) ⟧{γ} ∗ ▷  P v))).
  Proof.
    iIntros (Hin) "[Hstf #[Hcctx Hinv]]".
    iMod (inv_open with "Hinv") as "Hinv'"=> //.
    iDestruct "Hinv'" as "[Hinv' Hinvstep]".
    iDestruct "Hinv'" as
        (l r stl str) "(>Hclf & >Hcrf & Hstla & Hstra & Hinv')".
    iExists (side_elim s r l). iModIntro.
    destruct s.
    - simpl. iIntros "{$Hcrf} !>".
      iRename "Hstf" into "Hstlf".
      iDestruct (st_excl_eq with "Hstla Hstlf") as "#Heq".
      iSplit=> //.
      + iIntros "Hvs Hown".
        iMod ("Hinvstep" with "[-Hstlf]") as "_".
        { iNext. iExists l,r,_,_. iFrame. }
        iModIntro. iFrame "Hcctx ∗ Hinv".
      + iIntros (v vs Hvs) "Hown".
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]"; first inversion Hvs.
        iMod (st_excl_update _ _ _ _ (st v) with "Hstla Hstlf")
          as "[Hstla Hstlf]".
        subst.
        iDestruct (st_later_eq with "Heq") as ">Hleq".
        iDestruct "Hleq" as (P1 st1) "[Hsteq [HPeq Hsteq']]".
        iSpecialize ("HPeq" $!v).
        iSpecialize ("Hsteq'" $!v).
        iRewrite "Hsteq" in "Heval".
        subst.
        iDestruct (st_eval_recv with "Heval") as "[Heval HP]".
        iMod ("Hinvstep" with "[-Hstlf HP]") as "H".
        { iExists _,_,_,_. iFrame. iRight=> //.
          iNext. iSplit=> //. by iRewrite -"Hsteq'". }
        iModIntro.
        iSplitR "HP".
        * iFrame "Hstlf Hcctx Hinv".
        * iNext. by iRewrite -"HPeq".
    - simpl. iIntros "{$Hclf} !>".
      iRename "Hstf" into "Hstrf".
      iDestruct (st_excl_eq with "Hstra Hstrf") as "#Heq".
      iSplit=> //.
      + iIntros "Hvs Hown".
        iMod ("Hinvstep" with "[-Hstrf]") as "_".
        { iNext. iExists l,r,_,_. iFrame. }
        iModIntro. iFrame "Hcctx ∗ Hinv".
      + iIntros (v vs' Hvs) "Hown".
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]"; last inversion Hvs.
        iMod (st_excl_update _ _ _ _ (st v) with "Hstra Hstrf")
          as "[Hstra Hstrf]".
        subst.
        iDestruct (st_later_eq with "Heq") as ">Hleq".
        iDestruct "Hleq" as (P1 st1) "[Hsteq [HPeq Hsteq']]".
        iSpecialize ("HPeq" $!v).
        iSpecialize ("Hsteq'" $!v).
        iRewrite "Hsteq" in "Heval".
        iDestruct (st_eval_recv with "Heval") as "[Heval HP]".
        iMod ("Hinvstep" with "[-Hstrf HP]") as "_".
        { iExists _,_,_,_. iFrame. iLeft=> //.
            iNext. iSplit=> //. by iRewrite -"Hsteq'". }
        iModIntro.
        iSplitR "HP".
        * iFrame "Hstrf Hcctx Hinv".
        * iNext. by iRewrite -"HPeq".
  Qed.

  Lemma try_recv_st_spec st γ c s (P : val → iProp Σ) :
    {{{ ⟦ c @ s : TReceive P st ⟧{γ} }}}
      try_recv c #s
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⟦ c @ s : TReceive P st ⟧{γ}) ∨
                  (∃ w, ⌜v = SOMEV w⌝ ∧ ⟦ c @ s : st w ⟧{γ} ∗ ▷ P w)}}}.
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
      iSpecialize ("H" $!Hvs).
      iMod ("H" with "Hown") as "H".
      iModIntro.
      iApply "HΦ"=> //.
      eauto with iFrame.
    - iIntros (v vs' Hvs) "Hown".
      iDestruct "H" as "[_ H]".
      iSpecialize ("H" $!v vs' Hvs).
      iMod ("H" with "Hown") as "H".
      iModIntro.
      iApply "HΦ"=> //.
      eauto with iFrame.
  Qed.

  Lemma recv_st_spec st γ c s (P : val → iProp Σ) :
    {{{ ⟦ c @ s : TReceive P st ⟧{γ} }}}
      recv c #s
    {{{ v, RET v; ⟦ c @ s : st v ⟧{γ} ∗ P v}}}.
  Proof.
    iIntros (Φ) "Hrecv HΦ".
    iLöb as "IH". wp_rec.
    wp_apply (try_recv_st_spec with "Hrecv").
    iIntros (v) "H".
    iDestruct "H" as "[H | H]".
    - iDestruct "H" as "[Hv H]".
      iDestruct "Hv" as %->.
      wp_pures.
      iApply ("IH" with "[H]")=> //.
    - iDestruct "H" as (w) "[Hv [H HP]]".
      iDestruct "Hv" as %->.
      wp_pures.
      iApply "HΦ".
      iFrame.
  Qed.

End stype_interp.