From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl auth.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang.lib Require Import spin_lock.
From osiris Require Import list.
From osiris Require Import auth_excl.
From osiris Require Import typing.
Set Default Proof Using "Type".
Import uPred.

Definition new_chan : val :=
  λ: <>,
     let: "l" := ref (lnil #()) in
     let: "r" := ref (lnil #()) in
     let: "lk" := newlock #() in
     (("l","r"),"lk").

Coercion side_to_bool (s : side) : bool :=
  match s with Left => true | Right => false end.
Definition side_elim {A} (s : side) (l r : A) : A :=
  match s with Left => l | Right => r end.

Definition get_side : val := λ: "c" "s",
  (if: "s" = #Left then Fst (Fst "c") else Snd (Fst "c"))%E.
Definition get_lock : val := λ: "c", Snd "c".

Definition get_dual_side : val := λ: "s",
  (if: "s" = #Left then #Right else #Left)%E.

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
    let: "l" := get_side "c" (get_dual_side "s") in
    let: "ret" :=
      match: !"l" with
        SOME "p" => "l" <- Snd "p";; SOME (Fst "p")
      | NONE => NONE
      end in
    release "lk";; "ret".

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

  Definition chan_inv (γ : chan_name) (l r : val) : iProp Σ :=
    (∃ ls rs,
      is_list_ref l ls ∗ own (chan_l_name γ) (● to_auth_excl ls) ∗
      is_list_ref r rs ∗ own (chan_r_name γ) (● to_auth_excl rs))%I.
  Typeclasses Opaque chan_inv.

  Definition is_chan (γ : chan_name) (c : val) : iProp Σ :=
    (∃ l r lk : val,
      ⌜c = ((l, r), lk)%V⌝ ∧
      is_lock N (chan_lock_name γ) lk (chan_inv γ l r))%I.

  Global Instance is_chan_persistent : Persistent (is_chan γ c).
  Proof. by apply _. Qed.

  Definition chan_own (γ : chan_name) (s : side) (vs : list val) : iProp Σ :=
    own (side_elim s chan_l_name chan_r_name γ) (◯ to_auth_excl vs)%I.

  Global Instance chan_own_timeless γ s vs : Timeless (chan_own γ s vs).
  Proof. by apply _. Qed.

  Lemma get_side_spec Φ s (l r lk : val) :
    Φ (side_elim s l r) -∗
    WP get_side ((l, r), lk)%V #s {{ Φ }}.
  Proof. iIntros "?". wp_lam. by destruct s; wp_pures. Qed.

  Lemma get_lock_spec Φ (l r lk : val) :
    Φ lk -∗
    WP get_lock ((l, r), lk)%V {{ Φ }}.
  Proof. iIntros "?". wp_lam. by wp_pures. Qed.

  Lemma dual_side_spec Φ s :
    Φ #(dual_side s) -∗ WP get_dual_side #s {{ Φ }}.
  Proof. iIntros "?". wp_lam. by destruct s; wp_pures. Qed.

  Lemma new_chan_spec :
    {{{ True }}}
      new_chan #()
    {{{ c γ, RET c; is_chan γ c ∗ chan_own γ Left [] ∗ chan_own γ Right [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /is_chan /chan_own.
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
    iApply ("HΦ" $! _ (Chan_name γlk lsγ rsγ)); simpl.
    rewrite /chan_inv /=. eauto 20 with iFrame.
  Qed.

  Lemma chan_inv_alt s γ l r :
    chan_inv γ l r ⊣⊢ ∃ ls rs,
      is_list_ref (side_elim s l r) ls ∗
      own (side_elim s chan_l_name chan_r_name γ) (● to_auth_excl ls) ∗
      is_list_ref (side_elim s r l) rs ∗
      own (side_elim s chan_r_name chan_l_name γ) (● to_auth_excl rs).
  Proof.
    destruct s; rewrite /chan_inv //=.
    iSplit; iDestruct 1 as (ls rs) "(?&?&?&?)"; iExists rs, ls; iFrame.
  Qed.

  Lemma send_spec Φ E γ c v s :
    is_chan γ c -∗
    (|={⊤,E}=> ∃ vs,
      chan_own γ s vs ∗
      ▷ (chan_own γ s (vs ++ [v]) ={E,⊤}=∗ Φ #())) -∗
    WP send c #s v {{ Φ }}.
  Proof.
    iIntros "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (l r lk ->) "#Hlock"; wp_pures.
    wp_apply get_lock_spec; wp_pures.
    wp_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]".
    wp_apply get_side_spec; wp_pures.
    iDestruct (chan_inv_alt s with "Hinv") as
        (vs ws) "(Href & Hvs & Href' & Hws)".
    iDestruct "Href" as (ll lhd Hslr) "(Hll & Hlvs)"; rewrite Hslr.
    wp_load. wp_apply (lsnoc_spec with "Hlvs"). iIntros (lhd' Hlvs).
    wp_bind (_ <- _)%E.
    iMod "HΦ" as (vs') "[Hchan HΦ]".
    iDestruct (excl_eq with "Hvs Hchan") as %->.
    iMod (excl_update _ _ _ (vs ++ [v]) with "Hvs Hchan") as "[Hvs Hchan]".
    wp_store. iMod ("HΦ" with "Hchan") as "HΦ".
    iModIntro.
    wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); last eauto.
    iApply (chan_inv_alt s).
    rewrite /is_list_ref. eauto 10 with iFrame.
  Qed.

  Lemma try_recv_spec Φ E γ c s :
    is_chan γ c -∗
    (|={⊤,E}=> ∃ vs,
      chan_own γ (dual_side s) vs ∗
      ▷ ((⌜vs = []⌝ -∗ chan_own γ (dual_side s) vs ={E,⊤}=∗ Φ NONEV) ∧
         (∀ v vs', ⌜vs = v :: vs'⌝ -∗
                   chan_own γ (dual_side s) vs' ={E,⊤}=∗ Φ (SOMEV v)))) -∗
    WP try_recv c #s {{ Φ }}.
  Proof.
    iIntros "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (l r lk ->) "#Hlock"; wp_pures.
    wp_apply get_lock_spec; wp_pures.
    wp_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]". wp_pures.
    wp_apply dual_side_spec. wp_apply get_side_spec; wp_pures.
    iDestruct (chan_inv_alt (dual_side s) with "Hinv") as
        (vs ws) "(Href & Hvs & Href' & Hws)".
    iDestruct "Href" as (ll lhd Hslr) "(Hll & Hlvs)"; rewrite Hslr.
    wp_bind (! _)%E.
    iMod "HΦ" as (vs') "[Hchan HΦ]".
    wp_load.
    iDestruct (excl_eq with "Hvs Hchan") as %->.
    destruct vs as [|v vs]; simpl.
    - iDestruct "Hlvs" as %->.
      iDestruct "HΦ" as "[HΦ _]".
      iMod ("HΦ" with "[//] Hchan") as "HΦ".
      iModIntro.
      wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
      { iApply (chan_inv_alt (dual_side s)).
        rewrite /is_list_ref. eauto 10 with iFrame. }
      iIntros (_). wp_pures. by iApply "HΦ".
    - iDestruct "Hlvs" as %(hd' & -> & Hhd').
      iMod (excl_update _ _ _ vs with "Hvs Hchan") as "[Hvs Hchan]".
      iDestruct "HΦ" as "[_ HΦ]".
      iMod ("HΦ" with "[//] Hchan") as "HΦ".
      iModIntro. wp_store.
      wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
      { iApply (chan_inv_alt (dual_side s)).
        rewrite /is_list_ref. eauto 10 with iFrame. }
      iIntros (_). wp_pures. by iApply "HΦ".
  Qed.

  Lemma recv_spec Φ E γ c s :
    is_chan γ c -∗
    (□ (|={⊤,E}=> ∃ vs,
      chan_own γ (dual_side s) vs ∗
        ▷ ((⌜vs = []⌝ -∗ chan_own γ (dual_side s) vs ={E,⊤}=∗ True) ∗
          (∀ v vs', ⌜vs = v :: vs'⌝ -∗
                    chan_own γ (dual_side s) vs' ={E,⊤}=∗ Φ v)))) -∗
    WP recv c #s {{ Φ }}.
  Proof.
    iIntros "#Hc #HΦ".
    rewrite /recv.
    iLöb as "IH".
    wp_apply (try_recv_spec with "Hc")=> //.
    iMod "HΦ" as (vs) "[Hchan [HΦfail HΦsucc]]".
    iModIntro.
    iExists _.
    iFrame.
    iNext.
    iSplitL "HΦfail".
    - iIntros "Hvs Hown".
      iRename ("HΦfail") into "HΦ".
      iDestruct ("HΦ" with "Hvs Hown") as "HΦ".
      iMod ("HΦ") as "HΦ".
      iModIntro.
      wp_match.
      by iApply ("IH").
    - iRename ("HΦsucc") into "HΦ".
      iIntros (v vs') "Hvs Hown".
      iMod ("HΦ" with "Hvs Hown") as "HΦ".
      iModIntro.
      by wp_pures.
  Qed.

End channel.