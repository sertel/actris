(** This file contains the definition of the channels, encoded as a pair of
lock-protected buffers, and their primitive proof rules. Moreover:

- It defines the connective [c ↣ prot] for ownership of channel endpoints,
  which describes that channel endpoint [c] adheres to protocol [prot].
- It proves Actris's specifications of [send] and [recv] w.r.t. dependent
  separation protocols.

An encoding of the usual (binary) choice connectives [prot1 <{Q1}+{Q2}> prot2]
and [prot1 <{Q1}&{Q2}> prot2], inspired by session types, is also included in
this file.

In this file we define the three message-passing connectives:

- [new_chan] creates references to two empty buffers and a lock, and returns a
  pair of endpoints, where the order of the two references determines the
  polarity of the endpoints.
- [send] takes an endpoint and adds an element to the first buffer.
- [recv] performs a busy loop until there is something in the second buffer,
  which it pops and returns, locking during each peek.

It is additionally shown that the channel ownership [c ↣ prot] is closed under
the subprotocol relation [⊑] *)
From iris.heap_lang Require Export primitive_laws notation.
From iris.heap_lang Require Export proofmode.
From iris.heap_lang.lib Require Import spin_lock.
From actris.channel Require Export proto channel.
From actris.utils Require Import llist skip.
Set Default Proof Using "Type".

Definition new_chan : val :=
  λ: "<>",
    let: "cs" := channel.new_chan #() in
    let: "c1" := Fst "cs" in
    let: "c2" := Snd "cs" in
    ((λ: "v", send "c1" "v", λ: "<>", recv "c1"),
     (λ: "v", send "c2" "v", λ: "<>", recv "c2")).
Definition start_chan : val := λ: "f",
  let: "cc" := new_chan #() in
  Fork ("f" (Snd "cc"));; Fst "cc".
Definition send : val := λ: "c", Fst "c".
Definition recv : val := λ: "c", Snd "c" #().

(** * Definition of the mapsto connective *)
Definition iProto_mapsto_def `{!heapGS Σ, !chanG Σ}
  (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γ s (send recv : val),
    ⌜c = (send, recv)%V⌝ ∗
    iProto_own (chan_proto_name γ) s p ∗
    (∀ v (p : iProto Σ),
       {{{ iProto_own (chan_proto_name γ) s (<!> MSG v; p)%proto }}}
         send v
       {{{ RET #(); iProto_own (chan_proto_name γ) s p }}}) ∗
    (∀ {TT:tele} (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ),
       {{{ iProto_own (chan_proto_name γ) s
             (<?.. x> MSG v x {{ ▷ P x }}; p x)%proto }}}
         recv #()
       {{{ x, RET v x; iProto_own (chan_proto_name γ) s (p x)%proto ∗ P x }}}).
Definition iProto_mapsto_aux : seal (@iProto_mapsto_def). by eexists. Qed.
Definition iProto_mapsto := iProto_mapsto_aux.(unseal).
Definition iProto_mapsto_eq :
  @iProto_mapsto = @iProto_mapsto_def := iProto_mapsto_aux.(seal_eq).
Arguments iProto_mapsto {_ _ _} _ _%proto.
Global Instance: Params (@iProto_mapsto) 4 := {}.
Notation "c ↣ p" := (iProto_mapsto c p)
  (at level 20, format "c  ↣  p").

Global Instance iProto_mapsto_contractive `{!heapGS Σ, !chanG Σ} c :
  Contractive (iProto_mapsto c).
Proof. rewrite iProto_mapsto_eq. solve_contractive. Qed.

Section channel.
  Context `{!heapGS Σ, !chanG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.
  Global Instance iProto_mapsto_ne c : NonExpansive (iProto_mapsto c).
  Proof. rewrite iProto_mapsto_eq. solve_proper. Qed.
  Global Instance iProto_mapsto_proper c : Proper ((≡) ==> (≡)) (iProto_mapsto c).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_mapsto_le c p1 p2 : c ↣ p1 -∗ ▷ (p1 ⊑ p2) -∗ c ↣ p2.
  Proof.
    rewrite iProto_mapsto_eq. iDestruct 1 as (γ s send recv ->) "[Hown H]".
    iIntros "Hle'". iExists γ, s, send, recv. iSplit; [done|]. iFrame "H".
    by iApply (iProto_own_le with "Hown").
  Qed.

  (** ** Specifications of [send] and [recv] *)
  Lemma new_chan_spec p :
    {{{ True }}}
      new_chan #()
    {{{ c1 c2, RET (c1,c2); c1 ↣ p ∗ c2 ↣ iProto_dual p }}}.
  Proof.
    iIntros (Φ _) "HΦ". wp_lam.
    wp_apply (new_chan_spec with "[//]"); iIntros (c1 c2) "[Hl Hr]".
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iSplitL "Hl".
    - rewrite channel.iProto_mapsto_eq iProto_mapsto_eq.
      iDestruct "Hl" as (γ s l r lk ->) "[#Hlk H]".
      iExists γ, s, _, _.
      iFrame "H". iSplit; [done|].
      iSplit.
      + iIntros (v p' Ψ) "!> Hown HΨ".
        wp_pures. wp_apply (send_spec with "[Hown]").
        { rewrite channel.iProto_mapsto_eq.
          iExists γ, s, l, r, lk.
          iSplit; [done|].
          iFrame "#∗". }
        iIntros "H". iApply "HΨ".
        rewrite channel.iProto_mapsto_eq.
        iDestruct "H" as (γ' s' l' r' lk' ?) "[#Hlk' H]".
        admit.                  (* Needs meta ghost state for unification *)
      + iIntros (TT v P p' Ψ) "!> Hown HΨ".
        wp_pures. wp_apply (recv_spec with "[Hown]").
        { rewrite channel.iProto_mapsto_eq.
          iExists γ, s, l, r, lk.
          iSplit; [done|].
          iFrame "#∗". }
        iIntros (x) "[H HP]". iApply "HΨ".
        rewrite channel.iProto_mapsto_eq.
        iDestruct "H" as (γ' s' l' r' lk' ?) "[#Hlk' H]".
        iFrame "HP".
        admit.                  (* Needs meta ghost state for unification *)
    - rewrite channel.iProto_mapsto_eq iProto_mapsto_eq.
      iDestruct "Hr" as (γ s l r lk ->) "[#Hlk H]".
      iExists γ, s, _, _.
      iFrame "H". iSplit; [done|].
      iSplit.
      + iIntros (v p' Ψ) "!> Hown HΨ".
        wp_pures. wp_apply (send_spec with "[Hown]").
        { rewrite channel.iProto_mapsto_eq.
          iExists γ, s, l, r, lk.
          iSplit; [done|].
          iFrame "#∗". }
        iIntros "H". iApply "HΨ".
        rewrite channel.iProto_mapsto_eq.
        iDestruct "H" as (γ' s' l' r' lk' ?) "[#Hlk' H]".
        admit.                  (* Needs meta ghost state for unification *)
      + iIntros (TT v P p' Ψ) "!> Hown HΨ".
        wp_pures. wp_apply (recv_spec with "[Hown]").
        { rewrite channel.iProto_mapsto_eq.
          iExists γ, s, l, r, lk.
          iSplit; [done|].
          iFrame "#∗". }
        iIntros (x) "[H HP]". iApply "HΨ".
        rewrite channel.iProto_mapsto_eq.
        iDestruct "H" as (γ' s' l' r' lk' ?) "[#Hlk' H]".
        iFrame "HP".
        admit.                  (* Needs meta ghost state for unification *)
  Admitted.

  Lemma start_chan_spec p Φ (f : val) :
    ▷ (∀ c, c ↣ iProto_dual p -∗ WP f c {{ _, True }}) -∗
    ▷ (∀ c, c ↣ p -∗ Φ c) -∗
    WP start_chan f {{ Φ }}.
  Proof.
    iIntros "Hfork HΦ". wp_lam.
    wp_smart_apply (new_chan_spec p with "[//]"); iIntros (c1 c2) "[Hc1 Hc2]".
    wp_smart_apply (wp_fork with "[Hfork Hc2]").
    { iNext. wp_smart_apply ("Hfork" with "Hc2"). }
    wp_pures. iApply ("HΦ" with "Hc1").
  Qed.

  Lemma send_spec c v p :
    {{{ c ↣ <!> MSG v; p }}}
      send c v
    {{{ RET #(); c ↣ p }}}.
  Proof.
    rewrite iProto_mapsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (γ s send recv ->) "[Hown #[Hsend Hrecv]]"; wp_pures.
    wp_smart_apply ("Hsend" with "Hown"); iIntros "Hown".
    iApply "HΦ". iExists γ, s, send, recv. by iFrame "#∗".
  Qed.

  Lemma send_spec_tele {TT} c (tt : TT)
        (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ (<!.. x > MSG v x {{ P x }}; p x) ∗ P tt }}}
      send c (v tt)
    {{{ RET #(); c ↣ (p tt) }}}.
  Proof.
    iIntros (Φ) "[Hc HP] HΦ".
    iDestruct (iProto_mapsto_le _ _ (<!> MSG v tt; p tt)%proto with "Hc [HP]")
      as "Hc".
    { iIntros "!>".
      iApply iProto_le_trans.
      iApply iProto_le_texist_intro_l.
      by iFrame "HP". }
    by iApply (send_spec with "Hc").
  Qed.

  Lemma recv_spec {TT} c (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ <?.. x> MSG v x {{ ▷ P x }}; p x }}}
      recv c
    {{{ x, RET v x; c ↣ p x ∗ P x }}}.
  Proof.
    rewrite iProto_mapsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (γ s send recv ->) "[Hown #[Hsend Hrecv]]". wp_pures.
    wp_smart_apply ("Hrecv" with "[$Hown]");  iIntros (x) "[Hown HP]".
    iApply "HΦ". iFrame "HP". iExists γ, s, send, recv. by iFrame "#∗".
  Qed.

  (** ** Specifications for choice *)
  Lemma select_spec c (b : bool) P1 P2 p1 p2 :
    {{{ c ↣ (p1 <{P1}+{P2}> p2) ∗ if b then P1 else P2 }}}
      send c #b
    {{{ RET #(); c ↣ (if b then p1 else p2) }}}.
  Proof.
    rewrite /iProto_choice. iIntros (Φ) "[Hc HP] HΦ".
    iApply (send_spec with "[Hc HP] HΦ").
    iApply (iProto_mapsto_le with "Hc").
    iIntros "!>". iExists b. by iFrame "HP".
  Qed.

  Lemma branch_spec c P1 P2 p1 p2 :
    {{{ c ↣ (p1 <{P1}&{P2}> p2) }}}
      recv c
    {{{ b, RET #b; c ↣ (if b : bool then p1 else p2) ∗ if b then P1 else P2 }}}.
  Proof.
    rewrite /iProto_choice. iIntros (Φ) "Hc HΦ".
    iApply (recv_spec _ (tele_app _)
      (tele_app (TT:=[tele _ : bool]) (λ b, if b then P1 else P2))%I
      (tele_app _) with "[Hc]").
    { iApply (iProto_mapsto_le with "Hc").
      iIntros "!> /=" (b) "HP". iExists b. by iSplitL. }
    rewrite -bi_tforall_forall.
    iIntros "!>" (x) "[Hc H]". iApply "HΦ". iFrame.
  Qed.

End channel.
