From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl auth.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang.lib Require Import lock.
From iris.heap_lang.lib Require Import spin_lock.
From osiris Require Import list.
From osiris Require Import buffer.
Set Default Proof Using "Type".


Definition new_list : val :=
  λ: <>, lnil #().

Definition new_chan : val := 
  λ: <>,
     let l := ref new_list #() in
     let r := ref new_list #() in
     let lk := newlock #() in
     ((l,r),lk).

Notation left := (#true) (only parsing).
Notation right := (#false) (only parsing).

Definition get_buffs c := Fst c.
Definition get_left c := Fst (get_buffs c).
Definition get_right c := Snd (get_buffs c).
Definition get_lock c := Snd c.

Definition dual_side s :=
  (if: s = left then right else left)%E.

Definition get_side c s :=
  (if: s = left then (get_left c) else (get_right c))%E.

Definition send : val :=
  λ: "c" "s" "v",
    let lk := get_lock "c" in
    acquire lk;;
    let l := get_side "c" "s" in
    l <- lsnoc !l "v";;
    release lk.

Definition try_recv : val :=
  λ: "c" "s",
    let lk := get_lock "c" in
    acquire lk;;
    let l := (get_side "c" (dual_side "s")) in
    match: !l with
      SOME "p" => l <- Snd "p";; release lk;; SOME (Fst "p")
    | NONE => release lk;; NONE
    end.

Definition recv : val :=
  rec: "go" "c" "s" :=
    match: try_recv "c" "s" with
      SOME "p" => "p"
    | NONE => "go" "c" "s"
    end.

Section channel.
  Context `{!heapG Σ, !lockG Σ, !buffG Σ} (N : namespace).

  Definition is_list_ref (l : val) (xs : list val) : iProp Σ :=
    (∃ l':loc, ∃ hd : val, ⌜l = #l'⌝ ∧ l' ↦ hd ∗ ⌜is_list hd xs⌝)%I.

  Definition is_side (s : val) : Prop :=
    s = left ∨ s = right.
  
  Definition is_chan (lkγ lsγ rsγ : gname) (c : val) (ls rs : list val) : iProp Σ :=
    (∃ l r lk : val, ⌜c = ((l, r), lk)%V⌝ ∧
                     own lsγ (◯  to_buff ls) ∗ own rsγ (◯  to_buff rs) ∗
                     is_lock N lkγ lk
                       (∃ ls rs, 
                           is_list_ref l ls ∗ own lsγ (● to_buff ls) ∗
                           is_list_ref r rs ∗ own rsγ (● to_buff rs)))%I.

  Lemma new_chan_spec :
    {{{ True }}}
      new_chan #()
    {{{ c lkγ lsγ rsγ, RET c; is_chan lkγ lsγ rsγ c [] [] }}}.
  Proof. 
    iIntros (Φ) "_ HΦ". rewrite -wp_fupd /newlock /new_list /=.
    repeat wp_lam. wp_alloc lk as "Hlk".
    repeat wp_lam. wp_alloc r as "Hr".
    repeat wp_lam. wp_alloc l as "Hl".
    wp_pures.
    iMod (own_alloc (Excl ())) as (lkγ) "Hγlk"; first done.
    iMod (own_alloc (Auth (Excl' (to_buff [])) (to_buff []))) as (lsγ) "Hls"; first done.
    iMod (own_alloc (Auth (Excl' (to_buff [])) (to_buff []))) as (rsγ) "Hrs"; first done.
    rewrite auth_both_op.
    rewrite own_op. rewrite own_op.
    iDestruct "Hls" as "[Hlsa Hlsf]".
    iDestruct "Hrs" as "[Hrsa Hrsf]".
    iMod (inv_alloc N _ (lock_inv lkγ lk (∃ (ls rs : list val), is_list_ref #l ls ∗ own lsγ (● to_buff ls) ∗ is_list_ref #r rs ∗ own rsγ (● to_buff rs)))%I with "[Hlk Hγlk Hr Hl Hlsa Hrsa]") as "Hlk".
    {
      iNext. iExists _. iFrame. iFrame.
      iExists [], []. iFrame.
      iSplitL "Hl"=> //; iExists _, _; iSplit=> //; iFrame=> //. 
    }
    iModIntro.
    iApply "HΦ".
    iExists _, _, _.
    iFrame "Hlsf Hrsf".
    iSplit=> //.
    unfold is_lock. iExists _. iSplit=> //.
  Qed.

  Definition send_upd lkγ lsγ rsγ c ls rs s v : iProp Σ :=
    match s with
    | left  => is_chan lkγ lsγ rsγ c (ls ++ [v]) rs
    | right => is_chan lkγ lsγ rsγ c ls (rs ++ [v])
    | _ => ⌜False⌝%I
    end.

  Lemma send_spec (lkγ lsγ rsγ : gname) (c v s : val) (ls rs : list val) :
    {{{ is_chan lkγ lsγ rsγ c ls rs ∗ ⌜is_side s⌝%I }}}
      send c s v
    {{{ RET #(); send_upd lkγ lsγ rsγ c ls rs s v }}}.
  Proof.
    iIntros (Φ) "[Hc #Hs] HΦ". 
    iRevert "Hs". iIntros (Hs).
    rewrite -wp_fupd /send /=.
    iDestruct "Hc" as (l r lk Hc) "[Hlsf [Hrsf #Hlk]]".
    wp_lam.
    wp_pures.
    subst.
    wp_bind (Snd _). 
    wp_pures.
    wp_bind (acquire lk).
    iApply acquire_spec=> //.
    iNext.
    iIntros "[Hlocked Hl]".
    iDestruct "Hl" as (ls' rs') "[Hls [Hlsa [Hrs Hrsa]]]".    
    iDestruct (excl_eq with "Hlsa Hlsf") as %Heqls. rewrite -(Heqls).
    iDestruct (excl_eq with "Hrsa Hrsf") as %Heqrs. rewrite -(Heqrs).
    wp_seq.
    wp_pures.    
    inversion Hs.
    - iDestruct "Hls" as (lb Hb bhd) "[Hl #Hbhd]".
      iDestruct (excl_update _ _ _ (ls ++ [v]) with "Hlsa Hlsf") as ">[Hlsa Hlsf]".
      subst.
      wp_pures.
      wp_bind (lsnoc (Load #lb) v).
      wp_load.
      iApply lsnoc_spec=> //.
      iIntros (hd' Hhd').
      iNext.
      wp_store.
      wp_pures.
      eauto.
      iApply (release_spec N lkγ lk with "[Hlocked Hl Hlsa Hrsa Hrs]") => //.
      {
        iFrame; eauto.
        iSplitR. iApply "Hlk".
        iFrame. iExists _, _. iFrame.
        iExists _, _. iSplit=> //. iFrame. iPureIntro => //.
      }
      iModIntro.
      iIntros (_).
      iModIntro.
      iApply "HΦ".
      iExists _, _, _.
      iSplitR=> //.
      iSplitL "Hlsf"=> //.
      iSplitL "Hrsf"=> //.
    - iDestruct "Hrs" as (lb Hb bhd) "[Hr #Hbhd]".
      iDestruct (excl_update _ _ _ (rs ++ [v]) with "Hrsa Hrsf") as ">[Hrsa Hrsf]".
      subst.
      wp_pures.
      wp_bind (lsnoc (Load #lb) v).
      wp_load.
      iApply lsnoc_spec=> //.
      iIntros (hd' Hhd').
      iNext.
      wp_store.
      wp_pures.
      eauto.
      iApply (release_spec N lkγ lk with "[Hlocked Hr Hlsa Hrsa Hls]") => //.
      {
        iFrame; eauto.
        iSplitR. iApply "Hlk".
        iFrame. iExists _, _. iFrame.
        iExists _, _. iSplit=> //. iFrame. iPureIntro => //.
      } 
      iModIntro.
      iIntros (_).
      iModIntro.
      iApply "HΦ".
      iExists _, _, _.
      iSplitR=> //.
      iSplitL "Hlsf"=> //.
      iSplitL "Hrsf"=> //.
  Qed.

  Definition try_recv_upd  lkγ lsγ rsγ c ls rs s v : iProp Σ :=
    match s with
    | left => match v with
              | NONEV => (is_chan lkγ lsγ rsγ c ls rs ∧ ⌜rs = []⌝)%I
              | SOMEV w => (∃ rs', is_chan  lkγ lsγ rsγ c ls rs' ∧ ⌜rs = w::rs'⌝)%I
              | _ => ⌜False⌝%I
              end
    | right => match v with
               | NONEV => (is_chan  lkγ lsγ rsγ c ls rs ∧ ⌜ls = []⌝)%I
               | SOMEV w => (∃ ls', is_chan  lkγ lsγ rsγ c ls' rs ∧ ⌜ls = w::ls'⌝)%I
               | _ => ⌜False⌝%I
               end 
    | _ => ⌜False⌝%I
    end.

  Lemma try_recv_spec ( lkγ lsγ rsγ : gname) (c v s : val) (ls rs : list val) :
    {{{ is_chan lkγ lsγ rsγ c ls rs ∗ ⌜is_side s⌝%I }}}
      try_recv c s
    {{{ v, RET v;  try_recv_upd  lkγ lsγ rsγ c ls rs s v }}}.
  Proof.
    iIntros (Φ) "[Hc #Hs] HΦ". 
    iRevert "Hs". iIntros (Hs).
    rewrite -wp_fupd /send /=.
    iDestruct "Hc" as (l r lk Hc) "[Hlsf [Hrsf #Hlk]]".
    subst.
    wp_lam.
    wp_pures.
    wp_bind (acquire _).
    iApply acquire_spec=> //.
    iNext.
    iIntros "[Hlocked Hl]".
    iDestruct "Hl" as (ls' rs') "[Hls [Hlsa [Hrs Hrsa]]]".
    iDestruct (excl_eq with "Hlsa Hlsf") as %Heqls. rewrite -(Heqls).
    iDestruct (excl_eq with "Hrsa Hrsf") as %Heqrs. rewrite -(Heqrs).
    wp_seq.
    wp_pures.
    inversion Hs; subst.
    - wp_pures.
      iDestruct "Hrs" as (rl Hr rhd) "[Hrs #Hrhd]".
      wp_pures.
      subst.
      wp_load.
      iRevert "Hrhd". iIntros (Hrhd).
      unfold is_list in Hrhd.
      destruct rs'.
      + subst.
        wp_pures.
        wp_bind (release _).
        wp_pures.
        iApply (release_spec N lkγ lk with "[Hlocked Hls Hrs Hlsa Hrsa]") => //.
        {
          iFrame; eauto.
          iSplitR. iApply "Hlk".
          iFrame. iExists _, _. iFrame.
          iExists _, _. iFrame=> //.
        }
        iNext. iIntros (_).
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iSplit=> //.
        iExists _, _, _.
        iSplit=> //.
        iFrame.
        iApply "Hlk".
      + subst.
        destruct Hrhd as [hd' [Hrhd Hrhd']].
        subst.
        wp_pures.
        wp_store. wp_pures. 
        iDestruct (excl_update _ _ _ (rs') with "Hrsa Hrsf") as ">[Hrsa Hrsf]".
        wp_bind (release _).
        wp_pures.
        iApply (release_spec N lkγ lk with "[Hlocked Hls Hrs Hlsa Hrsa]") => //.
        {
          iFrame; eauto.
          iSplitR. iApply "Hlk".
          iFrame. iExists _, _. iFrame.
          iExists _, _. iFrame=> //.
        }
        iNext. iIntros (_).
        wp_pures.
        iApply "HΦ".
        iExists _.
        iModIntro.
        iSplit=> //.
        iExists _, _, _.
        iSplit=> //.
        iFrame.
        iApply "Hlk".
    - wp_pures.
      iDestruct "Hls" as (ls Hl lhd) "[Hls #Hlhd]".
      wp_pures.
      subst.
      wp_load.
      iRevert "Hlhd". iIntros (Hlhd).
      unfold is_list in Hlhd.
      destruct ls'.
      + subst.
        wp_pures.        
        wp_bind (release _).
        wp_pures.
        iApply (release_spec N lkγ lk with "[Hlocked Hls Hrs Hlsa Hrsa]") => //.
        {
          iFrame; eauto.
          iSplitR. iApply "Hlk".
          iFrame. iExists _, _. iFrame.
          iExists _, _. iFrame=> //.
        }
        iNext. iIntros (_).
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iSplit=> //.
        iExists _, _, _.
        iSplit=> //.
        iFrame.
        iApply "Hlk".
      + subst.
        destruct Hlhd as [hd' [Hlhd Hlhd']].
        subst.
        wp_pures.
        wp_store. wp_pures. 
        iDestruct (excl_update _ _ _ (ls') with "Hlsa Hlsf") as ">[Hlsa Hlsf]".
        wp_bind (release _).
        wp_pures.
        iApply (release_spec N lkγ lk with "[Hlocked Hls Hrs Hlsa Hrsa]") => //.
        {
          iFrame; eauto.
          iSplitR. iApply "Hlk".
          iFrame. iExists _, _. iFrame.
          iExists _, _. iFrame=> //.
        }
        iNext. iIntros (_).
        wp_pures.
        iApply "HΦ".
        iExists _.
        iModIntro.
        iSplit=> //.
        iExists _, _, _.
        iSplit=> //.
        iFrame.
        iApply "Hlk".
  Qed. 

End channel.