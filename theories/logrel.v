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
Import uPred.

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

  Definition inv_st (γ :st_name) (c : val) : iProp Σ :=
    (∃ l r stl str,
      is_chan N (st_c_name γ) c l r ∗
      stmapsto_full γ stl Left  ∗
      stmapsto_full γ str Right ∗
      ((⌜r = []⌝ ∗ ⌜st_eval r stl str⌝) ∨ 
       (⌜l = []⌝ ∗ ⌜st_eval l stl str⌝)))%I.

  Definition interp_st (γ : st_name) (st : stype) c s : iProp Σ :=
    (stmapsto_frag γ st s ∗ inv N (inv_st γ c))%I.

  Notation "⟦ ep : sτ ⟧{ γ }" :=
  (interp_st γ sτ (ep.1) (ep.2))
    (ep at level 99).

  Lemma new_chan_vs st E c cγ :
    is_chan N cγ c [] [] ={E}=∗
      ∃ lγ rγ, 
        let γ := SessionType_name cγ lγ rγ in
        ⟦ (c,Left) : st ⟧{γ} ∗ ⟦ (c,Right) : (dual_stype st) ⟧{γ}.
  Proof.
    iIntros "Hc".
    iMod (own_alloc (Auth (Excl' (to_auth_excl st)) (to_auth_excl st))) as (lγ) "Hlst"; first done.
    iMod (own_alloc (Auth (Excl' (to_auth_excl (dual_stype st))) (to_auth_excl (dual_stype st)))) as (rγ) "Hrst"; first done.
    rewrite (auth_both_op (to_auth_excl st)). 
    rewrite (auth_both_op (to_auth_excl (dual_stype st))). 
    rewrite own_op own_op.
    iDestruct "Hlst" as "[Hlsta Hlstf]".
    iDestruct "Hrst" as "[Hrsta Hrstf]".
    pose (SessionType_name cγ lγ rγ) as stγ.
    iMod (inv_alloc N _ (inv_st stγ c) with "[-Hlstf Hrstf]") as "#Hinv".
    { iNext. rewrite /inv_st. eauto 10 with iFrame. }
    eauto 10 with iFrame.
  Qed.
  
  Lemma new_chan_st_spec st :
    {{{ True }}}
      new_chan #()
    {{{ c γ, RET c; ⟦ (c,Left) : st ⟧{γ} ∗ ⟦ (c,Right) : dual_stype st ⟧{γ} }}}.
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

End logrel.