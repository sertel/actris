(** This file contains the definition of the channels, encoded as a pair of
lock-protected buffers, and their primitive proof rules. Actris's proof rules
for channels in terms of dependent separation protocols can be found in the file
[theories/channel/proto_channel.v].

In this file we define the three message-passing connectives:

- [new_chan] creates references to two empty buffers and a lock, and returns a
  pair of endpoints, where the order of the two references determines the
  polarity of the endpoints.
- [send] takes an endpoint and adds an element to the first buffer.
- [recv] performs a busy loop until there is something in the second buffer,
  which it pops and returns, locking during each peek.

The logically-atomic basic (i.e. non dependent separation protocol)
proof rules [new_chan_spec], [send_spec] and [recv_spec] are defined in terms
of the logical connectives [is_chan] and [chan_own]:

- [is_chan γ v1 v2] is a persistent proposition expressing that [v1] and [v2]
  are the endpoints of a channel with logical name [γ].
- [chan_own γ s vs] is an exclusive proposition expressing the buffer of side
  [s] ([Left] or [Right]) has contents [vs].

Note that the specifications include 3 laters [▷] to account for the three
levels of indirection due to step-indexing in the model of dependent separation
protocols. *)
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.heap_lang Require Import lifting.
From iris.algebra Require Import excl auth list.
From actris.utils Require Import auth_excl llist.
Set Default Proof Using "Type".

Inductive side := Left | Right.
Instance side_inhabited : Inhabited side := populate Left.
Definition side_elim {A} (s : side) (l r : A) : A :=
  match s with Left => l | Right => r end.

(** * The definition of the message-passing connectives *)
Definition new_chan : val :=
  λ: <>,
     let: "l" := lnil #() in
     let: "r" := lnil #() in
     let: "lk" := newlock #() in
     ((("l","r"),"lk"), (("r","l"),"lk")).

Definition send : val :=
  λ: "c" "v",
    let: "lk" := Snd "c" in
    acquire "lk";;
    let: "l" := Fst (Fst "c") in
    lsnoc "l" "v";;
    release "lk".

Definition try_recv : val :=
  λ: "c",
    let: "lk" := Snd "c" in
    acquire "lk";;
    let: "l" := Snd (Fst "c") in
    let: "ret" := if: lisnil "l" then NONE else SOME (lpop "l") in
    release "lk";; "ret".

Definition recv : val :=
  rec: "go" "c" :=
    match: try_recv "c" with
      SOME "p" => "p"
    | NONE => "go" "c"
    end.

(** * Setup of Iris's cameras *)
Class chanG Σ := {
  chanG_lockG :> lockG Σ;
  chanG_authG :> auth_exclG (listO valO) Σ;
}.
Definition chanΣ : gFunctors :=
  #[ lockΣ; auth_exclΣ (constOF (listO valO)) ].
Instance subG_chanΣ {Σ} : subG chanΣ Σ → chanG Σ.
Proof. solve_inG. Qed.

Section channel.
  Context `{!heapG Σ, !chanG Σ} (N : namespace).

  Record chan_name := Chan_name {
    chan_lock_name : gname;
    chan_l_name : gname;
    chan_r_name : gname
  }.

  (** * The logical connectives *)
  Definition chan_inv (γ : chan_name) (l r : loc) : iProp Σ :=
    (∃ ls rs,
      llist sbi_internal_eq l ls ∗ own (chan_l_name γ) (● to_auth_excl ls) ∗
      llist sbi_internal_eq r rs ∗ own (chan_r_name γ) (● to_auth_excl rs))%I.
  Typeclasses Opaque chan_inv.

  Definition is_chan (γ : chan_name) (c1 c2 : val) : iProp Σ :=
    (∃ (l r : loc) (lk : val),
      ⌜ c1 = ((#l, #r), lk)%V ∧ c2 = ((#r, #l), lk)%V ⌝ ∗
      is_lock N (chan_lock_name γ) lk (chan_inv γ l r))%I.

  Global Instance is_chan_persistent : Persistent (is_chan γ c1 c2).
  Proof. by apply _. Qed.

  Lemma chan_inv_alt s γ l r :
    chan_inv γ l r ⊣⊢ ∃ ls rs,
      llist sbi_internal_eq (side_elim s l r) ls ∗
      own (side_elim s chan_l_name chan_r_name γ) (● to_auth_excl ls) ∗
      llist sbi_internal_eq (side_elim s r l) rs ∗
      own (side_elim s chan_r_name chan_l_name γ) (● to_auth_excl rs).
  Proof.
    destruct s; rewrite /chan_inv //=.
    iSplit; iDestruct 1 as (ls rs) "(?&?&?&?)"; iExists rs, ls; iFrame.
  Qed.

  Definition chan_own (γ : chan_name) (s : side) (vs : list val) : iProp Σ :=
    own (side_elim s chan_l_name chan_r_name γ) (◯ to_auth_excl vs)%I.

  (** * The proof rules *)
  Global Instance chan_own_timeless γ s vs : Timeless (chan_own γ s vs).
  Proof. by apply _. Qed.

  Lemma new_chan_spec :
    {{{ True }}}
      new_chan #()
    {{{ c1 c2 γ, RET (c1,c2); is_chan γ c1 c2 ∗ chan_own γ Left [] ∗ chan_own γ Right [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /is_chan /chan_own.
    wp_lam.
    wp_apply (lnil_spec with "[//]"); iIntros (l) "Hl".
    wp_apply (lnil_spec with "[//]"); iIntros (r) "Hr".
    iMod (own_alloc (● (to_auth_excl []) ⋅ ◯ (to_auth_excl []))) as (lsγ) "[Hls Hls']".
    { by apply auth_both_valid. }
    iMod (own_alloc (● (to_auth_excl []) ⋅ ◯ (to_auth_excl []))) as (rsγ) "[Hrs Hrs']".
    { by apply auth_both_valid. }
    wp_apply (newlock_spec N (∃ ls rs,
      llist sbi_internal_eq l ls ∗ own lsγ (● to_auth_excl ls) ∗
      llist sbi_internal_eq r rs ∗ own rsγ (● to_auth_excl rs))%I with "[Hl Hr Hls Hrs]").
    { eauto 10 with iFrame. }
    iIntros (lk γlk) "#Hlk". wp_pures.
    iApply ("HΦ" $! _ _ (Chan_name γlk lsγ rsγ)); simpl.
    rewrite /chan_inv /=. eauto 20 with iFrame.
  Qed.

  Lemma send_spec Φ E γ c1 c2 v s :
    is_chan γ c1 c2 -∗
    (|={⊤,E}=> ∃ vs,
      chan_own γ s vs ∗
      ▷ (chan_own γ s (vs ++ [v]) ={E,⊤}=∗ ▷ ▷ Φ #())) -∗
    WP send (side_elim s c1 c2) v {{ Φ }}.
  Proof.
    iIntros "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (l r lk [-> ->]) "#Hlock"; wp_pures.
    assert (side_elim s (#l, #r, lk)%V (#r, #l, lk)%V =
      ((#(side_elim s l r), #(side_elim s r l)), lk)%V) as -> by (by destruct s).
    wp_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]".
    iDestruct (chan_inv_alt s with "Hinv") as
      (vs ws) "(Hll & Hvs & Href' & Hws)".
    wp_seq. wp_bind (Fst (_,_)%V)%E.
    iMod "HΦ" as (vs') "[Hchan HΦ]".
    iDestruct (excl_eq with "Hvs Hchan") as %<-%leibniz_equiv.
    iMod (excl_update _ _ _ (vs ++ [v]) with "Hvs Hchan") as "[Hvs Hchan]".
    wp_pures. iMod ("HΦ" with "Hchan") as "HΦ"; iModIntro.
    wp_apply (lsnoc_spec with "[$Hll //]"); iIntros "Hll".
    wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); last eauto.
    iApply (chan_inv_alt s).
    rewrite /llist. eauto 20 with iFrame.
  Qed.

  Lemma try_recv_spec Φ E γ c1 c2 s :
    is_chan γ c1 c2 -∗
    ((|={⊤,E}▷=> ▷ Φ NONEV) ∧
     (|={⊤,E}=> ∃ vs,
       chan_own γ s vs ∗
       ▷ (∀ v vs', ⌜ vs = v :: vs' ⌝ -∗
                   chan_own γ s vs' ={E,⊤,⊤}▷=∗ ▷ Φ (SOMEV v)))) -∗
    WP try_recv (side_elim s c2 c1) {{ Φ }}.
  Proof.
    iIntros "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (l r lk [-> ->]) "#Hlock"; wp_pures.
    assert (side_elim s (#r, #l, lk)%V (#l, #r, lk)%V =
      ((#(side_elim s r l), #(side_elim s l r)), lk)%V) as -> by (by destruct s).
    wp_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]".
    iDestruct (chan_inv_alt s with "Hinv")
      as (vs ws) "(Hll & Hvs & Href' & Hws)".
    wp_seq. wp_bind (Fst (_,_)%V)%E. destruct vs as [|v vs]; simpl.
    - iDestruct "HΦ" as "[>HΦ _]". wp_pures. iMod "HΦ"; iModIntro.
      wp_apply (lisnil_spec with "Hll"); iIntros "Hll". wp_pures.
      wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
      { iApply (chan_inv_alt s).
        rewrite /llist. eauto 10 with iFrame. }
      iIntros (_). by wp_pures.
    - iDestruct "HΦ" as "[_ >HΦ]". iDestruct "HΦ" as (vs') "[Hvs' HΦ]".
      iDestruct (excl_eq with "Hvs Hvs'") as %<-%leibniz_equiv.
      iMod (excl_update _ _ _ vs with "Hvs Hvs'") as "[Hvs Hvs']".
      wp_pures. iMod ("HΦ" with "[//] Hvs'") as "HΦ"; iModIntro.
      wp_apply (lisnil_spec with "Hll"); iIntros "Hll". iMod "HΦ".
      wp_apply (lpop_spec with "Hll"); iIntros (v') "[% Hll]"; simplify_eq/=.
      wp_apply (release_spec with "[-HΦ $Hlocked $Hlock]").
      { iApply (chan_inv_alt s).
        rewrite /llist. eauto 10 with iFrame. }
      iIntros (_). by wp_pures.
  Qed.

  Lemma recv_spec Φ E γ c1 c2 s :
    is_chan γ c1 c2 -∗
    (|={⊤,E}=> ∃ vs,
      chan_own γ s vs ∗
      ▷ ∀ v vs', ⌜ vs = v :: vs' ⌝ -∗
                 chan_own γ s vs' ={E,⊤,⊤}▷=∗ ▷ Φ v) -∗
    WP recv (side_elim s c2 c1) {{ Φ }}.
  Proof.
    iIntros "#Hc HΦ". iLöb as "IH". wp_lam.
    wp_apply (try_recv_spec _ E with "Hc")=> //. iSplit.
    - iMod (fupd_intro_mask' _ E) as "Hclose"; first done. iIntros "!> !>".
      iMod "Hclose" as %_; iIntros "!> !>". wp_pures. by iApply "IH".
    - iMod "HΦ" as (vs) "[Hvs HΦ]". iExists vs; iFrame "Hvs".
      iIntros "!> !>" (v vs' ->) "Hvs".
      iMod ("HΦ" with "[//] Hvs") as "HΦ". iIntros "!> !>". iMod "HΦ".
      iIntros "!> !>". by wp_pures.
  Qed.
End channel.
