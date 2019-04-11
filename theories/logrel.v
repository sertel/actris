From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import lock.
From iris.heap_lang.lib Require Import spin_lock.
From osiris Require Import typing auth_excl channel.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants auth saved_prop.
Require Import FunctionalExtensionality.

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

  Inductive st_eval : list val -> stype -> stype -> Prop :=
    | st_eval_nil st : st_eval [] st (dual_stype st)
    | st_eval_cons (P:val -> Prop) v vs st1 st2 :
        P v -> st_eval vs st1 (st2 v) ->
        st_eval (v::vs) st1 (TRecv P st2).
  Hint Constructors st_eval.

  Lemma st_eval_send :
    ∀ (P : val → Prop) (st : val → stype) (l : list val) (str : stype) (v : val),
      P v → st_eval l (TSend P st) str → st_eval (l ++ [v]) (st v) str.
  Proof.
    intros P st l str v HP Heval.
    generalize dependent str.
    induction l; intros.
    - inversion Heval; by constructor.
    - inversion Heval; subst. simpl.
      constructor=> //.
      apply IHl=> //.
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

  Definition interp_st (γ : st_name) (st : stype) (c : val) (s : side) : iProp Σ :=
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
    iMod (own_alloc (Auth (Excl' (to_auth_excl st)) (to_auth_excl st))) as (lγ) "Hlst"; first done.
    iMod (own_alloc (Auth (Excl' (to_auth_excl (dual_stype st))) (to_auth_excl (dual_stype st)))) as (rγ) "Hrst"; first done.
    rewrite (auth_both_op (to_auth_excl st)). 
    rewrite (auth_both_op (to_auth_excl (dual_stype st))). 
    rewrite own_op own_op.
    iDestruct "Hlst" as "[Hlsta Hlstf]".
    iDestruct "Hrst" as "[Hrsta Hrstf]".
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
    {{{ c γ, RET c;  ⟦ c @ Left : st ⟧{γ} ∗ ⟦ c @ Right : dual_stype st ⟧{γ} }}}.
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

Lemma send_vs c γ s (P : val → Prop) st E :
    ↑N ⊆ E →
    ⟦ c @ s : TSend P st ⟧{γ} ={E,E∖↑N}=∗
      ∃ l r, chan_frag (st_c_name γ) c l r ∗
      ▷ (∀ v, ⌜P v⌝ -∗ 
              match s with 
              | Left  => chan_frag (st_c_name γ) c (l ++ [v]) r
              | Right => chan_frag (st_c_name γ) c l (r ++ [v])
              end ={E∖ ↑N,E}=∗ ⟦ c @ s : st v ⟧{γ}).
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
        - inversion Heval; subst.
          iSplit=> //.
          iPureIntro.
          destruct str; inversion H2.
          apply st_eval_cons=> //. subst.
          rewrite (involutive (st0 v)).
          rewrite -(involutive (dual_stype (st0 v))).
          constructor. }
      iModIntro. iFrame "Hcctx ∗ Hinv".
    - iRename "Hstf" into "Hstrf".
      iDestruct (excl_eq with "Hstra Hstrf") as %<-.
      iMod (excl_update _ _ _ (st v) with "Hstra Hstrf") as "[Hstra Hstrf]".
      iMod ("Hinvstep" with "[-Hstrf]") as "_".
      { iNext.
        iExists _,_. iFrame.
        iExists _,_. iFrame.
        iRight.
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]";
          iDestruct "Heval" as %Heval.
        - inversion Heval; subst.
          iSplit=> //.
          iPureIntro.
          destruct stl; inversion H2.
          apply st_eval_cons=> //. subst.
          rewrite (involutive (st0 v)).
          rewrite -(involutive (dual_stype (st0 v))).
          constructor.
        - iSplit=> //.
          iPureIntro.
          by eapply st_eval_send. }
      iModIntro. iFrame "Hcctx ∗ Hinv".
  Qed.

  Definition to_side s :=
    match s with
    | Left  => #true
    | Right => #false
    end.

  Lemma send_st_spec st γ c s (P : val → Prop) v :
    P v →
    {{{ ⟦ c @ s : TSend P st ⟧{γ} }}}
      send c (to_side s) v
    {{{ RET #(); ⟦ c @ s : st v ⟧{γ} }}}.
  Proof.
    iIntros (HP Φ) "Hsend HΦ".
    iApply (send_spec with "[#]").
    { destruct s. by left. by right. }
    { iDestruct "Hsend" as "[? [$ ?]]". }
    iMod (send_vs with "Hsend") as (ls lr) "[Hch H]"; first done.
    iModIntro. iExists ls, lr. iFrame "Hch".
    iIntros "!> Hupd". iApply "HΦ".
    iApply ("H" $! v HP with "[Hupd]"). by destruct s.
  Qed.

End logrel.