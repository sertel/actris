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
     let: "l" := ref (lnil #()) in
     let: "r" := ref (lnil #()) in
     let: "lk" := newlock #() in
     (("l","r"),"lk").

Inductive side := Left | Right.
Coercion side_to_bool (s : side) : bool :=
  match s with Left => true | Right => false end.

Definition get_buffs c := Fst c.
Definition get_left c := Fst (get_buffs c).
Definition get_right c := Snd (get_buffs c).
Definition get_lock c := Snd c.

Definition dual_side s :=
  (if: s = #Left then #Right else #Left)%E.

Definition get_side c s :=
  (if: s = #Left then get_left c else get_right c)%E.

Definition send : val :=
  λ: "c" "s" "v",
    let: "lk" := get_lock "c" in
    acquire "lk";;
    let: "l" := get_side "c" "s" in
    "l" <- lsnoc !"l" "v";;
    release "lk".

Definition try_recv : val :=
  λ: "c" "s",
    let: "lk" := get_lock "c" in
    acquire "lk";;
    let: "l" := (get_side "c" (dual_side "s")) in
    match: !"l" with
      SOME "p" => "l" <- Snd "p";; release "lk";; SOME (Fst "p")
    | NONE => release "lk";; NONE
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

  Definition chan_frag_snoc (γ : chan_name) (c : val)
             (l r : list val) (s : side) (v : val)
    : iProp Σ :=
    match s with
    | Left  => chan_frag γ c (l ++ [v]) r
    | Right => chan_frag γ c l (r ++ [v])
    end.

  Lemma send_spec Φ E γ c v s :
    chan_ctx γ c -∗
    (|={⊤,E}=> ∃ ls rs,
      chan_frag γ c ls rs ∗
      ▷ (chan_frag_snoc γ c ls rs s v ={E,⊤}=∗ Φ #())) -∗
    WP send c #s v {{ Φ }}.
  Proof.
    iIntros "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (l r lk ->) "#Hlock"; wp_pures.
    wp_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]".
    iDestruct "Hinv" as (ls rs) "(Hl & Hls & Hr & Hrs)".
    destruct s.
    - wp_pures. iDestruct "Hl" as (ll lhd ->) "(Hl & Hll)".
      wp_load. wp_apply (lsnoc_spec with "Hll").
      iIntros (hd' Hll).
      wp_bind (_ <- _)%E. iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
      iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hls' Hrs']".
      iDestruct (excl_eq with "Hls Hls'") as %->.
      iMod (excl_update _ _ _ (ls ++ [v]) with "Hls Hls'") as "[Hls Hls']".
      wp_store.
      iMod ("HΦ" with "[Hls' Hrs']") as "HΦ".
      { rewrite /= /chan_frag. eauto with iFrame. }
      iModIntro.
      wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); last eauto.
      { rewrite /is_list_ref. eauto 10 with iFrame. }
    - wp_pures. iDestruct "Hr" as (lr rhd ->) "(Hr & Hlr)".
      wp_load. wp_apply (lsnoc_spec with "Hlr").
      iIntros (hd' Hlr). wp_pures.
      wp_bind (_ <- _)%E. iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
      wp_store.
      iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hls' Hrs']".
      iDestruct (excl_eq with "Hrs Hrs'") as %->.
      iMod (excl_update _ _ _ (rs ++ [v]) with "Hrs Hrs'") as "[Hrs Hrs']".
      iMod ("HΦ" with "[Hls' Hrs']") as "HΦ".
      { rewrite /= /chan_frag. eauto with iFrame. }
      iModIntro.
      wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); last eauto.
      { rewrite /is_list_ref. eauto 10 with iFrame. }
  Qed.

  Definition try_recv_fail (γ : chan_name) (c : val)
             (l r : list val) (s : side) : iProp Σ :=
    match s with
    | Left  => (chan_frag γ c l r ∧ ⌜r = []⌝)%I
    | Right => (chan_frag γ c l r ∧ ⌜l = []⌝)%I
    end.

  Definition try_recv_succ (γ : chan_name) (c : val)
             (l r : list val) (s : side) (v : val) : iProp Σ :=
    match s with
    | Left =>  (∃ r', chan_frag γ c l  r' ∧ ⌜r = v::r'⌝)%I
    | Right => (∃ l', chan_frag γ c l' r  ∧ ⌜l = v::l'⌝)%I
    end.

  Lemma try_recv_spec Φ E γ c s :
    chan_ctx γ c -∗
    (|={⊤,E}=> ∃ ls rs,
      chan_frag γ c ls rs ∗
      ▷ ((try_recv_fail γ c ls rs s ={E,⊤}=∗ Φ NONEV) ∧
         (∀ v, try_recv_succ γ c ls rs s v ={E,⊤}=∗ Φ (SOMEV v)))) -∗
    WP try_recv c #s {{ Φ }}.
  Proof.
    iIntros "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (l r lk ->) "#Hlock"; wp_pures.
    wp_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]".
    iDestruct "Hinv" as (ls rs) "(Hls & Hlsa & Hrs & Hrsa)".
    destruct s; simpl.
    - iDestruct "Hrs" as (rl rhd ->) "[Hrs #Hrhd]".
      wp_pures.
      wp_bind (Load _).
      iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
      wp_load.
      destruct rs; simpl.
      + iDestruct "Hrhd" as %->.
        iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hlsf Hrsf]".
        iDestruct (excl_eq with "Hlsa Hlsf") as %->.
        iDestruct (excl_eq with "Hrsa Hrsf") as %->.
        iDestruct "HΦ" as "[HΦ _]".
        iMod ("HΦ" with "[Hlsf Hrsf]") as "HΦ".
        { rewrite /try_recv_fail /chan_frag.
          eauto 10 with iFrame. }
        iModIntro.
        wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
        { rewrite /is_list_ref /is_list. eauto 10 with iFrame. }
        iIntros (_).
        wp_pures.
        by iApply "HΦ".
      + iDestruct "Hrhd" as %[hd' [-> Hrhd']].
        iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hlsf Hrsf]".
        iDestruct (excl_eq with "Hlsa Hlsf") as %->.
        iDestruct (excl_eq with "Hrsa Hrsf") as %->.
        iDestruct (excl_update _ _ _ (rs) with "Hrsa Hrsf") as ">[Hrsa Hrsf]".
        iDestruct "HΦ" as "[_ HΦ]".
        iMod ("HΦ" with "[Hlsf Hrsf]") as "HΦ".
        { rewrite /try_recv_succ /chan_frag.
          eauto 10 with iFrame. }
        iModIntro.
        wp_store.
        wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
        { rewrite /is_list_ref /is_list. eauto 10 with iFrame. }
        iIntros (_).
        wp_pures.
        by iApply "HΦ".
    - iDestruct "Hls" as (ll lhd ->) "[Hls #Hlhd]".
      wp_pures.
      wp_bind (Load _).
      iMod "HΦ" as (ls' rs') "[Hchan HΦ]".
      wp_load.
      destruct ls; simpl.
      + iDestruct "Hlhd" as %->.
        iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hlsf Hrsf]".
        iDestruct (excl_eq with "Hlsa Hlsf") as %->.
        iDestruct (excl_eq with "Hrsa Hrsf") as %->.
        iDestruct "HΦ" as "[HΦ _]".
        iMod ("HΦ" with "[Hlsf Hrsf]") as "HΦ".
        { rewrite /try_recv_fail /chan_frag.
          eauto 10 with iFrame. }
        iModIntro.
        wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
        { rewrite /is_list_ref /is_list. eauto 10 with iFrame. }
        iIntros (_).
        wp_pures.
        by iApply "HΦ".
      + iDestruct "Hlhd" as %[hd' [-> Hlhd']].
        iDestruct "Hchan" as (l' r' lk' [= <- <- <-]) "[Hlsf Hrsf]".
        iDestruct (excl_eq with "Hlsa Hlsf") as %->.
        iDestruct (excl_eq with "Hrsa Hrsf") as %->.
        iDestruct (excl_update _ _ _ (ls) with "Hlsa Hlsf") as ">[Hlsa Hlsf]".
        iDestruct "HΦ" as "[_ HΦ]".
        iMod ("HΦ" with "[Hlsf Hrsf]") as "HΦ".
        { rewrite /try_recv_succ /chan_frag. eauto 10 with iFrame. }
        iModIntro.
        wp_store.
        wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
        { rewrite /is_list_ref /is_list. eauto 10 with iFrame. }
        iIntros (_).
        wp_pures.
        by iApply "HΦ".
  Qed.

  Lemma recv_spec Φ E γ c s :
    chan_ctx γ c -∗
    (□ (|={⊤,E}=> ∃ ls rs,
      chan_frag γ c ls rs ∗
        ▷ ((try_recv_fail γ c ls rs s ={E,⊤}=∗ True) ∗
          (∀ v, try_recv_succ γ c ls rs s v ={E,⊤}=∗ Φ v)))) -∗
    WP recv c #s {{ Φ }}.
  Proof.
    iIntros "#Hc #HΦ".
    rewrite /recv.
    iLöb as "IH".
    wp_apply (try_recv_spec with "Hc")=> //.
    iMod "HΦ" as (ls rs) "[Hchan [HΦfail HΦsucc]]".
    iModIntro.
    iExists _, _.
    iFrame.
    iNext.
    iSplitL "HΦfail".
    - iIntros "Hupd".
      iDestruct ("HΦfail") as "HΦ".
      iMod ("HΦ" with "Hupd") as "HΦ".
      iModIntro.
      wp_match.
      by iApply ("IH").
    - iDestruct ("HΦsucc") as "HΦ".
      iIntros (v) "Hupd".
      iSpecialize("HΦ" $!v).
      iMod ("HΦ" with "Hupd") as "HΦ".
      iModIntro.
      by wp_pures.
  Qed.
End channel.