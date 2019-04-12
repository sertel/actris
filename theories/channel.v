From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl auth.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang.lib Require Import spin_lock.
From osiris Require Import list.
From osiris Require Import auth_excl.
Set Default Proof Using "Type".
Import uPred.

Definition new_chan : val :=
  λ: <>,
     let: "l" := ref lnil #() in
     let: "r" := ref lnil #() in
     let: "lk" := newlock #() in
     (("l","r"),"lk").

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

  Global Instance chan_ctx_persistent : Persistent (chan_ctx γ c).
  Proof. by apply _. Qed.

  Definition chan_frag (γ : chan_name) (c : val) (ls rs : list val) : iProp Σ :=
    (∃ l r lk : val,
      ⌜c = ((l, r), lk)%V⌝ ∧
      own (chan_l_name γ) (◯ to_auth_excl ls) ∗
      own (chan_r_name γ) (◯ to_auth_excl rs))%I.

  Global Instance chan_frag_timeless : Timeless (chan_frag γ c ls rs).
  Proof. by apply _. Qed.

  Definition is_chan (γ : chan_name) (c : val) (ls rs : list val) : iProp Σ :=
    (chan_ctx γ c ∗ chan_frag γ c ls rs)%I.

  Lemma new_chan_spec :
    {{{ True }}}
      new_chan #()
    {{{ c γ, RET c; is_chan γ c [] [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /is_chan /chan_ctx /chan_frag.
    wp_lam.
    wp_apply (lnil_spec with "[//]"); iIntros (ls Hls). wp_alloc l as "Hl".
    wp_apply (lnil_spec with "[//]"); iIntros (rs Hrs). wp_alloc r as "Hr".
    iMod (own_alloc (● (to_auth_excl []) ⋅ ◯ (to_auth_excl [])))
      as (lsγ) "[Hls Hls']"; first done.
    iMod (own_alloc (● (to_auth_excl []) ⋅ ◯ (to_auth_excl [])))
      as (rsγ) "[Hrs Hrs']"; first done.
    iAssert (is_list_ref #l []) with "[Hl]" as "Hl".
    { rewrite /is_list_ref; eauto. }
    iAssert (is_list_ref #r []) with "[Hr]" as "Hr".
    { rewrite /is_list_ref; eauto. }
    wp_apply (newlock_spec N (∃ ls rs,
      is_list_ref #l ls ∗ own lsγ (● to_auth_excl ls) ∗
      is_list_ref #r rs ∗ own rsγ (● to_auth_excl rs))%I
                with "[Hl Hr Hls Hrs]").
    { eauto 10 with iFrame. }
    iIntros (lk γlk) "#Hlk". wp_pures.
    iApply ("HΦ" $! _ (Chan_name γlk lsγ rsγ)).
    eauto 20 with iFrame.
  Qed.

  Definition chan_frag_snoc γ c ls rs s v : iProp Σ :=
    match s with
    | left  => chan_frag γ c (ls ++ [v]) rs
    | right => chan_frag γ c ls (rs ++ [v])
    | _ => ⌜False⌝%I
    end.

  Lemma send_spec Φ E γ (c v s : val) :
    is_side s →
    chan_ctx γ c -∗
    (|={⊤,E}=> ∃ ls rs,
      chan_frag γ c ls rs ∗
      ▷ (chan_frag_snoc γ c ls rs s v ={E,⊤}=∗ Φ #())) -∗
    WP send c s v {{ Φ }}.
  Proof.
    iIntros (Hside) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (l r lk ->) "#Hlock"; wp_pures.
    wp_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]".
    iDestruct "Hinv" as (ls rs) "(Hl & Hls & Hr & Hrs)".
    destruct Hside as [-> | ->].
    - wp_pures. iDestruct "Hl" as (ll lhd ->) "(Hl & Hll)".
      wp_load. wp_apply (lsnoc_spec with "Hll").
      iIntros (hd') "Hll". wp_pures.
      wp_bind (_ <- _)%E. iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
      wp_store.
      iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hls' Hrs']".
      iDestruct (excl_eq with "Hls Hls'") as %->.
      iMod (excl_update _ _ _ (ls ++ [v]) with "Hls Hls'") as "[Hls Hls']".
      iMod ("HΦ" with "[Hls' Hrs']") as "HΦ".
      { rewrite /= /chan_frag. eauto with iFrame. }
      iModIntro.
      wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
      { rewrite /is_list_ref. eauto 10 with iFrame. }
      iIntros "_ //".
    - wp_pures. iDestruct "Hr" as (lr rhd ->) "(Hr & Hlr)".
      wp_load. wp_apply (lsnoc_spec with "Hlr").
      iIntros (hd') "Hlr". wp_pures.
      wp_bind (_ <- _)%E. iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
      wp_store.
      iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hls' Hrs']".
      iDestruct (excl_eq with "Hrs Hrs'") as %->.
      iMod (excl_update _ _ _ (rs ++ [v]) with "Hrs Hrs'") as "[Hrs Hrs']".
      iMod ("HΦ" with "[Hls' Hrs']") as "HΦ".
      { rewrite /= /chan_frag. eauto with iFrame. }
      iModIntro.
      wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
      { rewrite /is_list_ref. eauto 10 with iFrame. }
      iIntros "_ //".
  Qed.

  Definition try_recv_upd_fail γ c ls rs s : iProp Σ :=
    match s with
    | left  => (chan_frag γ c ls rs ∧ ⌜rs = []⌝)%I
    | right => (chan_frag γ c ls rs ∧ ⌜ls = []⌝)%I
    | _ => ⌜False⌝%I
    end.

  Definition try_recv_upd_succ γ c ls rs s v : iProp Σ :=
    match s with
    | left =>  (∃ rs', chan_frag γ c ls  rs' ∧ ⌜rs = v::rs'⌝)%I
    | right => (∃ ls', chan_frag γ c ls' rs  ∧ ⌜ls = v::ls'⌝)%I
    | _ => ⌜False⌝%I
    end.

  Definition try_recv_upd γ c ls rs s v : iProp Σ :=
    match v with
    | NONEV => try_recv_upd_fail γ c ls rs s
    | SOMEV w => try_recv_upd_succ γ c ls rs s w
    | _ => ⌜False⌝%I
    end.

  Definition try_recv_vs E γ c s Φ :=
    (|={⊤,E}=> ∃ ls rs,
      chan_frag γ c ls rs ∗
      (∀ v, try_recv_upd γ c ls rs s v ={E,⊤}=∗ Φ v))%I.

  Lemma try_recv_spec Φ E γ (c s : val) :
    is_side s →
    chan_ctx γ c -∗
    try_recv_vs E γ c s Φ -∗
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
        { rewrite /try_recv_upd /try_recv_upd_fail /chan_frag.
          eauto 10 with iFrame. }
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
        iSpecialize ("HΦ" $!(InjRV (v))).
        iMod ("HΦ" with "[Hlsf Hrsf]") as "HΦ".
        { rewrite /try_recv_upd /try_recv_upd_succ /chan_frag.
          eauto 10 with iFrame. }
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
        { rewrite /try_recv_upd /try_recv_upd_fail /chan_frag.
          eauto 10 with iFrame. }
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
        iSpecialize ("HΦ" $!(InjRV (v))).
        iMod ("HΦ" with "[Hlsf Hrsf]") as "HΦ".
        { rewrite /try_recv_upd /try_recv_upd_succ /chan_frag.
          eauto 10 with iFrame. }
        iModIntro.
        wp_store.
        wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
        { rewrite /is_list_ref /is_list. eauto 10 with iFrame. }
        iIntros (_).
        wp_pures.
        by iApply "HΦ".
  Qed.

  Definition recv_vs E γ c s Φ :=
    (□ (|={⊤,E}=> ∃ ls rs,
      chan_frag γ c ls rs ∗
        ((try_recv_upd_fail γ c ls rs s ={E,⊤}=∗ True) ∗
         (∀ v, try_recv_upd_succ γ c ls rs s v ={E,⊤}=∗ Φ v))))%I.

  Lemma recv_spec Φ E γ c s :
    is_side s →
    chan_ctx γ c -∗
    recv_vs E γ c s Φ -∗
    WP recv c s {{ Φ }}.
  Proof.
    iIntros (Hside) "#Hc #HΦ".
    rewrite /recv.
    iLöb as "IH".
    wp_apply (try_recv_spec with "Hc")=> //.
    iMod "HΦ" as (ls rs) "[Hchan [HΦfail HΦsucc]]".
    iModIntro.
    iExists _, _.
    iFrame.
    iIntros (v) "Hupd".
    destruct v; try (by iRevert "Hupd"; iIntros (Hupd); inversion Hupd).
    - destruct v; try (by iRevert "Hupd"; iIntros (Hupd); inversion Hupd).
      destruct l; try (by iRevert "Hupd"; iIntros (Hupd); inversion Hupd).
      iClear "HΦsucc". iDestruct ("HΦfail") as "HΦ".
      iMod ("HΦ" with "Hupd") as "HΦ".
      iModIntro.
      wp_match.
      by iApply ("IH").
    - iClear "HΦfail". iDestruct ("HΦsucc") as "HΦ".
      iSpecialize("HΦ" $!v).
      iMod ("HΦ" with "Hupd") as "HΦ".
      iModIntro.
      by wp_pures.
  Qed.

End channel.