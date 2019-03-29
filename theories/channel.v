From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl auth.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang.lib Require Import lock.
From iris.heap_lang.lib Require Import spin_lock.
From osiris Require Import list.
From osiris Require Import auth_excl.
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
  Context `{!heapG Σ, !lockG Σ, !auth_exclG (list val) Σ} (N : namespace).

  Definition is_list_ref (l : val) (xs : list val) : iProp Σ :=
    (∃ l':loc, ∃ hd : val, ⌜l = #l'⌝ ∧ l' ↦ hd ∗ ⌜is_list hd xs⌝)%I.

  Definition is_side (s : val) : Prop :=
    s = left ∨ s = right.
  
  Record chan_name := Chan_name {
    chan_lock_name : gname;
    chan_l_name : gname;
    chan_r_name : gname
  }.

  Definition chan_ctx (γ : chan_name) (c : val) : iProp Σ :=
    (∃ l r lk : val,
      ⌜c = ((l, r), lk)%V⌝ ∧
      is_lock N (chan_lock_name γ) lk (∃ ls rs, 
        is_list_ref l ls ∗ own (chan_l_name γ) (● to_auth_excl ls) ∗
        is_list_ref r rs ∗ own (chan_r_name γ) (● to_auth_excl rs)))%I.

  Definition is_chan (γ : chan_name) (c : val) (ls rs : list val) : iProp Σ :=
    (∃ l r lk : val,
      ⌜c = ((l, r), lk)%V⌝ ∧
      own (chan_l_name γ) (◯ to_auth_excl ls) ∗ own (chan_r_name γ) (◯ to_auth_excl rs))%I.

  Lemma new_chan_spec :
    {{{ True }}}
      new_chan #()
    {{{ c γ, RET c; is_chan γ c [] [] ∗ chan_ctx γ c }}}.
  Proof. 
    iIntros (Φ) "_ HΦ". rewrite /is_chan /chan_ctx /is_lock.
    repeat wp_lam. wp_alloc lk as "Hlk".
    iMod (own_alloc (Excl ())) as (lkγ) "Hγlk"; first done.
    repeat wp_lam. wp_alloc r as "Hr".
    iMod (own_alloc (Auth (Excl' (to_auth_excl [])) (to_auth_excl []))) as (lsγ) "Hls"; first done.
    repeat wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (Auth (Excl' (to_auth_excl [])) (to_auth_excl []))) as (rsγ) "Hrs"; first done.
    rewrite auth_both_op own_op own_op.
    pose (Chan_name lkγ lsγ rsγ). 
    iDestruct "Hls" as "[Hlsa Hlsf]".
    iDestruct "Hrs" as "[Hrsa Hrsf]".
    iMod (inv_alloc N _ (lock_inv lkγ lk (∃ (ls rs : list val), is_list_ref #l ls ∗ own lsγ (● to_auth_excl ls) ∗ is_list_ref #r rs ∗ own rsγ (● to_auth_excl rs)))%I with "[Hlk Hγlk Hr Hl Hlsa Hrsa]") as "Hlk".
    { 
      rewrite /is_list_ref /is_list /lock_inv.
      iNext. iExists _.
      iSplitL "Hlk"=> //=.
      iSplitL "Hγlk"=> //=.
      iExists _, _. iFrame.      
      iSplitL "Hl"=> //; iExists _, _; iSplit=> //; iFrame=> //. 
    }
    wp_pures.
    iSpecialize ("HΦ" $!(#l, #r, #lk)%V c).
    iApply ("HΦ"). 
    iSplitL "Hlsf Hrsf"=> //;
    eauto 10 with iFrame.
  Qed.

  Definition send_upd γ c ls rs s v : iProp Σ :=
    match s with
    | left  => is_chan γ c (ls ++ [v]) rs
    | right => is_chan γ c ls (rs ++ [v])
    | _ => ⌜False⌝%I
    end.

  Lemma send_spec Φ E γ (c v s : val) :
    is_side s →
    chan_ctx γ c -∗
    (|={⊤,E}=> ∃ ls rs,
      is_chan γ c ls rs ∗
      (send_upd γ c ls rs s v ={E,⊤}=∗ Φ #())
    ) -∗
    WP send c s v {{ Φ }}.
  Proof.
    iIntros (Hside) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (l r lk ->) "#Hlock"; wp_pures.
    wp_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]".
    iDestruct "Hinv" as (ls rs) "(Hl & Hls & Hr & Hrs)".
    destruct Hside as [-> | ->].
    - wp_pures. iDestruct "Hl" as (ll lhd ->) "(Hl & Hll)".
      wp_load. wp_apply (lsnoc_spec with "Hll").
      iIntros (hd') "Hll". wp_store. wp_pures.
      iApply fupd_wp. iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
      iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hls' Hrs']".
      iDestruct (excl_eq with "Hls Hls'") as %->.
      iMod (excl_update _ _ _ (ls ++ [v]) with "Hls Hls'") as "[Hls Hls']".
      iMod ("HΦ" with "[Hls' Hrs']") as "HΦ".
      { rewrite /= /is_chan. eauto with iFrame. }
      iModIntro.
      wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
      { rewrite /is_list_ref. eauto 10 with iFrame. }
      iIntros "_ //".
    - wp_pures. iDestruct "Hr" as (lr rhd ->) "(Hr & Hlr)".
      wp_load. wp_apply (lsnoc_spec with "Hlr").
      iIntros (hd') "Hlr". wp_store. wp_pures.
      iApply fupd_wp. iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
      iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hls' Hrs']".
      iDestruct (excl_eq with "Hrs Hrs'") as %->.
      iMod (excl_update _ _ _ (rs ++ [v]) with "Hrs Hrs'") as "[Hrs Hrs']".
      iMod ("HΦ" with "[Hls' Hrs']") as "HΦ".
      { rewrite /= /is_chan. eauto with iFrame. }
      iModIntro.
      wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
      { rewrite /is_list_ref. eauto 10 with iFrame. }
      iIntros "_ //".
  Qed.

  Definition try_recv_upd  γ c ls rs s v : iProp Σ :=
    match s with
    | left => match v with
              | NONEV => (is_chan γ c ls rs ∧ ⌜rs = []⌝)%I
              | SOMEV w => (∃ rs', is_chan γ c ls rs' ∧ ⌜rs = w::rs'⌝)%I
              | _ => ⌜False⌝%I
              end
    | right => match v with
               | NONEV => (is_chan γ c ls rs ∧ ⌜ls = []⌝)%I
               | SOMEV w => (∃ ls', is_chan γ c ls' rs ∧ ⌜ls = w::ls'⌝)%I
               | _ => ⌜False⌝%I
               end 
    | _ => ⌜False⌝%I
    end.
  
  Lemma try_recv_spec Φ E γ (c v s : val) :
    is_side s →
    chan_ctx γ c -∗
    (|={⊤,E}=> ∃ ls rs,
      is_chan γ c ls rs ∗
      (∀ v, try_recv_upd γ c ls rs s v ={E,⊤}=∗ Φ v)
    ) -∗
    WP try_recv c s {{ Φ }}.
  Proof.
    iIntros (Hside) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (l r lk ->) "#Hlock"; wp_pures.
    wp_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]".
    iDestruct "Hinv" as (ls rs) "(Hls & Hlsa & Hrs & Hrsa)".
    destruct Hside as [-> | ->].
    - iDestruct "Hrs" as (rl rhd ->) "[Hrs #Hrhd]".
      wp_load.
      destruct rs.
      + iRevert "Hrhd". rewrite /is_list. iIntros (->).
        wp_pures.
        iApply fupd_wp.
        iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
        iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hlsf Hrsf]".
        iDestruct (excl_eq with "Hlsa Hlsf") as %->.
        iDestruct (excl_eq with "Hrsa Hrsf") as %->.
        iSpecialize ("HΦ" $!(InjLV #())).
        iMod ("HΦ" with "[Hlsf Hrsf]") as "HΦ".
        { rewrite /try_recv_upd /is_chan. eauto 10 with iFrame. } 
        iModIntro.
        wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
        { rewrite /is_list_ref /is_list. eauto 10 with iFrame. }
        iIntros (_).
        wp_pures.
        by iApply "HΦ".
      + iRevert "Hrhd". rewrite /is_list. iIntros ([hd' [-> Hrhd']]).
        wp_pures.
        iApply fupd_wp.
        iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
        iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hlsf Hrsf]".
        iDestruct (excl_eq with "Hlsa Hlsf") as %->.
        iDestruct (excl_eq with "Hrsa Hrsf") as %->.
        iDestruct (excl_update _ _ _ (rs) with "Hrsa Hrsf") as ">[Hrsa Hrsf]".
        iSpecialize ("HΦ" $!(InjRV (v0))).
        iMod ("HΦ" with "[Hlsf Hrsf]") as "HΦ".
        { rewrite /try_recv_upd /is_chan. eauto 10 with iFrame. }
        iModIntro.
        wp_store.
        wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
        { rewrite /is_list_ref /is_list. eauto 10 with iFrame. }
        iIntros (_).
        wp_pures.
        by iApply "HΦ".
    - iDestruct "Hls" as (ll lhd ->) "[Hls #Hlhd]".
      wp_load.
      destruct ls.
      + iRevert "Hlhd". rewrite /is_list. iIntros (->).
        wp_pures.
        iApply fupd_wp.
        iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
        iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hlsf Hrsf]".
        iDestruct (excl_eq with "Hlsa Hlsf") as %->.
        iDestruct (excl_eq with "Hrsa Hrsf") as %->.
        iSpecialize ("HΦ" $!(InjLV #())).
        iMod ("HΦ" with "[Hlsf Hrsf]") as "HΦ".
        { rewrite /try_recv_upd /is_chan. eauto 10 with iFrame. } 
        iModIntro.
        wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
        { rewrite /is_list_ref /is_list. eauto 10 with iFrame. }
        iIntros (_).
        wp_pures.
        by iApply "HΦ".
      + iRevert "Hlhd". rewrite /is_list. iIntros ([hd' [-> Hlhd']]).
        wp_pures.
        iApply fupd_wp.
        iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
        iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hlsf Hrsf]".
        iDestruct (excl_eq with "Hlsa Hlsf") as %->.
        iDestruct (excl_eq with "Hrsa Hrsf") as %->.
        iDestruct (excl_update _ _ _ (ls) with "Hlsa Hlsf") as ">[Hlsa Hlsf]".
        iSpecialize ("HΦ" $!(InjRV (v0))).
        iMod ("HΦ" with "[Hlsf Hrsf]") as "HΦ".
        { rewrite /try_recv_upd /is_chan. eauto 10 with iFrame. }
        iModIntro.
        wp_store.
        wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
        { rewrite /is_list_ref /is_list. eauto 10 with iFrame. }
        iIntros (_).
        wp_pures.
        by iApply "HΦ".
  Qed.

End channel.