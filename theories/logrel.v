From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From osiris Require Import typing auth_excl channel.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants.

Section logrel.
  Context `{!heapG Σ, !lockG Σ} (N : namespace).
  Context `{!auth_exclG (list val) Σ}.
  Context `{!auth_exclG stype Σ}.

  Record st_name := SessionType_name {
    st_c_name : chan_name;
    st_l_name : gname;
    st_r_name : gname
  }.

  Definition stmapsto_frag γ (st : stype) s : iProp Σ :=
    let γ :=
        match s with
        | Left  => st_l_name γ
        | Right => st_r_name γ
        end in
    own γ (◯  to_auth_excl st)%I.

  Definition stmapsto_full γ (st : stype) s : iProp Σ :=
    let γ :=
        match s with
        | Left  => st_l_name γ
        | Right => st_r_name γ
        end in
    own γ (● to_auth_excl st)%I.

  Fixpoint st_eval (vs : list val) (st1 st2 : stype) : Prop :=
    match vs with
    | [] => st1 = dual_stype st2
    | v::vs => match st2 with
               | TRecv P st2 => P v ∧ st_eval vs st1 (st2 v)
               | _ => False
               end
    end.

  Lemma st_eval_send (P : val -> Prop) st l str v :
      P v → st_eval l (TSend P st) str → st_eval (l ++ [v]) (st v) str.
  Proof.
    intro HP.
    revert str.
    induction l; intros str.
    - inversion 1. simpl.
      destruct str; inversion H1; subst. eauto.
    - intros. simpl.
      destruct str; inversion H.
      split=> //.
      apply IHl=> //.
  Qed.

  Lemma st_eval_recv (P : val → Prop) st1 l st2 v :
     st_eval (v :: l) st1 (TRecv P st2)  → st_eval l st1 (st2 v) ∧ P v.
  Proof.
    intros Heval.
    generalize dependent st1.
    induction l; intros.
    - inversion Heval; subst. split=> //.
     - inversion Heval; subst. simpl.
      constructor=> //.
  Qed.

  Definition inv_st (γ :st_name) (c : val) : iProp Σ :=
    (∃ l r stl str,
      chan_frag (st_c_name γ) c l r ∗
      stmapsto_full γ stl Left  ∗
      stmapsto_full γ str Right ∗
      ((⌜r = []⌝ ∗ ⌜st_eval l stl str⌝) ∨
       (⌜l = []⌝ ∗ ⌜st_eval r str stl⌝)))%I.

  Definition st_ctx (γ : st_name) (st : stype) (c : val) : iProp Σ :=
    (chan_ctx N (st_c_name γ) c ∗ inv N (inv_st γ c))%I.

  Definition st_frag  (γ : st_name) (st : stype) (s : side) : iProp Σ :=
    stmapsto_frag γ st s.

  Definition interp_st (γ : st_name) (st : stype)
      (c : val) (s : side) : iProp Σ :=
    (st_frag γ st s ∗ st_ctx γ st c)%I.

  Notation "⟦ c @ s : sτ ⟧{ γ }" := (interp_st γ sτ c s)
    (at level 10, s at next level, sτ at next level, γ at next level,
     format "⟦  c  @  s  :  sτ  ⟧{ γ }").

  Lemma new_chan_vs st E c cγ :
    is_chan N cγ c [] [] ={E}=∗
      ∃ lγ rγ,
        let γ := SessionType_name cγ lγ rγ in
        ⟦ c @ Left : st ⟧{γ} ∗ ⟦ c @ Right : dual_stype st ⟧{γ}.
  Proof.
    iIntros "[#Hcctx Hcf]".
    iMod (own_alloc (● (to_auth_excl st) ⋅
                     ◯ (to_auth_excl st)))
      as (lγ) "[Hlsta Hlstf]"; first done.
    iMod (own_alloc (● (to_auth_excl (dual_stype st)) ⋅
                     ◯ (to_auth_excl (dual_stype st))))
      as (rγ) "[Hrsta Hrstf]"; first done.
    pose (SessionType_name cγ lγ rγ) as stγ.
    iMod (inv_alloc N _ (inv_st stγ c) with "[-Hlstf Hrstf Hcctx]") as "#Hinv".
    { iNext. rewrite /inv_st. eauto 10 with iFrame. }
    iModIntro.
    iExists _, _.
    iFrame. simpl.
    repeat iSplitL=> //.
  Qed.

  Lemma new_chan_st_spec st :
    {{{ True }}}
      new_chan #()
    {{{ c γ, RET c;  ⟦ c @ Left : st ⟧{γ} ∗
                     ⟦ c @ Right : dual_stype st ⟧{γ} }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    iApply (wp_fupd).
    iApply (new_chan_spec)=> //.
    iModIntro.
    iIntros (c γ) "[Hc Hctx]".
    iMod (new_chan_vs st ⊤ c γ with "[-HΦ]") as "H".
    { rewrite /is_chan. eauto with iFrame. }
    iDestruct "H" as (lγ rγ) "[Hl Hr]".
    iApply "HΦ".
    iModIntro.
    iFrame.
  Qed.

  Coercion side_to_side (s : side) : channel.side :=
    match s with Left => channel.Left | Right => channel.Right end.

  Lemma send_vs c γ s (P : val → Prop) st E :
    ↑N ⊆ E →
    ⟦ c @ s : TSend P st ⟧{γ} ={E,E∖↑N}=∗
      ∃ l r, chan_frag (st_c_name γ) c l r ∗
      ▷ (∀ v, ⌜P v⌝ -∗
               chan_frag_snoc (st_c_name γ) c l r s v
              ={E∖ ↑N,E}=∗ ⟦ c @ s : st v ⟧{γ}).
  Proof.
    iIntros (Hin) "[Hstf #[Hcctx Hinv]]".
    iMod (inv_open with "Hinv") as "Hinv'"=> //.
    iDestruct "Hinv'" as "[Hinv' Hinvstep]".
    iDestruct "Hinv'" as (l r stl str) "(>Hcf & Hstla & Hstra & Hinv')".
    iModIntro.
    rewrite /stmapsto_frag /stmapsto_full.
    iExists l, r.
    iIntros "{$Hcf} !>" (v HP) "Hcf".
    destruct s.
    - iRename "Hstf" into "Hstlf".
      iDestruct (excl_eq with "Hstla Hstlf") as %<-.
      iMod (excl_update _ _ _ (st v) with "Hstla Hstlf") as "[Hstla Hstlf]".
      iMod ("Hinvstep" with "[-Hstlf]") as "_".
      { iNext.
        iExists _,_,_,_. iFrame.
        iLeft.
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]";
          iDestruct "Heval" as %Heval.
        - iSplit=> //.
          iPureIntro.
          by eapply st_eval_send.
        - destruct r; inversion Heval; subst.
          iSplit=> //.
          iPureIntro.
          simpl.
          rewrite (involutive (st v)).
          rewrite -(involutive (dual_stype (st v))).
          split=> //.
      }
      iModIntro. iFrame "Hcctx ∗ Hinv".
    - iRename "Hstf" into "Hstrf".
      iDestruct (excl_eq with "Hstra Hstrf") as %<-.
      iMod (excl_update _ _ _ (st v) with "Hstra Hstrf") as "[Hstra Hstrf]".
      iMod ("Hinvstep" with "[-Hstrf]") as "_".
      { iNext.
        iExists _,_, _, _. iFrame.
        iRight.
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]";
          iDestruct "Heval" as %Heval.
        - destruct l; inversion Heval; subst.
          iSplit=> //.
          iPureIntro.
          simpl.
          rewrite (involutive (st v)).
          rewrite -(involutive (dual_stype (st v))).
          split=> //.
        - iSplit=> //.
          iPureIntro.
          by eapply st_eval_send. }
      iModIntro. iFrame "Hcctx ∗ Hinv".
  Qed.

  Lemma send_st_spec st γ c s (P : val → Prop) v :
    P v →
    {{{ ⟦ c @ s : TSend P st ⟧{γ} }}}
      send c #s v
    {{{ RET #(); ⟦ c @ s : st v ⟧{γ} }}}.
  Proof.
    iIntros (HP Φ) "Hsend HΦ".
    iApply (send_spec with "[#]").
    { iDestruct "Hsend" as "[? [$ ?]]". }
    iMod (send_vs with "Hsend") as (ls lr) "[Hch H]"; first done.
    iModIntro. iExists ls, lr. iFrame "Hch".
    iIntros "!> Hupd". iApply "HΦ".
    iApply ("H" $! v HP with "[Hupd]"). by destruct s.
  Qed.

  Lemma try_recv_vs c γ s (P : val → Prop) st E :
    ↑N ⊆ E →
    ⟦ c @ s : TRecv P st ⟧{γ}
    ={E,E∖↑N}=∗
      ∃ l r, chan_frag (st_c_name γ) c l r ∗
      (▷ ((try_recv_fail (st_c_name γ) c l r s ={E∖↑N,E}=∗
           ⟦ c @ s : TRecv P st ⟧{γ}) ∧
         (∀ v, try_recv_succ (st_c_name γ) c l r s v ={E∖↑N,E}=∗
               ⟦ c @ s : (st v) ⟧{γ} ∗ ⌜P v⌝))).
  Proof.
    iIntros (Hin) "[Hstf #[Hcctx Hinv]]".
    iMod (inv_open with "Hinv") as "Hinv'"=> //.
    iDestruct "Hinv'" as "[Hinv' Hinvstep]".
    iDestruct "Hinv'" as (l r stl str) "(>Hcf & Hstla & Hstra & Hinv')".
    iModIntro.
    rewrite /stmapsto_frag /stmapsto_full.
    iExists l, r.
    iIntros "{$Hcf} !>".
    destruct s.
    - iRename "Hstf" into "Hstlf".
      iDestruct (excl_eq with "Hstla Hstlf") as %<-.
      iSplit=> //.
      + iIntros "[Hfail Hemp]".
        iMod ("Hinvstep" with "[-Hstlf]") as "_".
        { iNext. iExists l,r,_,_. iFrame. }
        iModIntro. iFrame "Hcctx ∗ Hinv".
      + simpl. iIntros (v) "Hsucc".
        rewrite /try_recv_succ. simpl.
        iDestruct "Hsucc" as (r') "[Hsucc Hr]".
        iDestruct "Hr" as %Hr.
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]"; first inversion Hr.
        iMod (excl_update _ _ _ (st v) with "Hstla Hstlf") as "[Hstla Hstlf]".
        subst.
        iDestruct "Heval" as %Heval.
        apply st_eval_recv in Heval as [Heval HP].
        iMod ("Hinvstep" with "[-Hstlf]") as "_".
        { iExists _,_,_,_. iFrame. iRight=> //. }
        by iFrame (HP) "Hcctx Hinv".
    - iRename "Hstf" into "Hstrf".
      iDestruct (excl_eq with "Hstra Hstrf") as %<-.
      iSplit=> //.
      + iIntros "[Hfail Hemp]".
        iMod ("Hinvstep" with "[-Hstrf]") as "_".
        { iNext. iExists l,r,_,_. iFrame. }
        iModIntro. iFrame "Hcctx ∗ Hinv".
      +  simpl. iIntros (v) "Hsucc".
        rewrite /try_recv_succ. simpl.
        iDestruct "Hsucc" as (r') "[Hsucc Hr]".
        iDestruct "Hr" as %Hl.
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]"; last inversion Hl.
        iMod (excl_update _ _ _ (st v) with "Hstra Hstrf") as "[Hstra Hstrf]".
        subst.
        iDestruct "Heval" as %Heval.
        apply st_eval_recv in Heval as [Heval HP].
        iMod ("Hinvstep" with "[-Hstrf]") as "_".
        { iExists _,_,_,_. iFrame. iLeft=> //. }
        by iFrame (HP) "Hcctx Hinv".
  Qed.

  Lemma try_recv_st_spec st γ c s (P : val → Prop) :
    {{{ ⟦ c @ s : TRecv P st ⟧{γ} }}}
      try_recv c #s
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⟦ c @ s : TRecv P st ⟧{γ}) ∨
                  (∃ w, ⌜v = SOMEV w⌝ ∧ ⟦ c @ s : st w ⟧{γ} ∗ ⌜P w⌝)}}}.
  Proof.
    iIntros (Φ) "Hrecv HΦ".
    iApply (try_recv_spec with "[#]").
    { iDestruct "Hrecv" as "[? [$ ?]]". }
    iMod (try_recv_vs with "Hrecv") as (ls lr) "[Hch H]"; first done.
    iModIntro. iExists ls, lr. iFrame "Hch".
    iIntros "!>".
    iSplit.
    - iIntros "Hupd".
      iDestruct "H" as "[H _]".
      iMod ("H" with "Hupd") as "H".
      iModIntro.
      iApply "HΦ"=> //.
      eauto with iFrame.
    - iIntros (v) "Hupd".
      iDestruct "H" as "[_ H]".
      iMod ("H" with "Hupd") as "H".
      iModIntro.
      iApply "HΦ"=> //.
      eauto with iFrame.
  Qed.

  Lemma recv_st_spec st γ c s (P : val → Prop) :
    {{{ ⟦ c @ s : TRecv P st ⟧{γ} }}}
      recv c #s
    {{{ v, RET v; ⟦ c @ s : st v ⟧{γ} ∗ ⌜P v⌝}}}.
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
    - iDestruct "H" as (w) "[Hv H]".
      iDestruct "Hv" as %->.
      wp_pures.
      iApply "HΦ".
      iFrame.
  Qed.

End logrel.
