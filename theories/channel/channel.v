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

It is additionaly shown that the channel ownership [c ↣ prot] is closed under
the subprotocol relation [⊑] *)
From iris.algebra Require Import gmap excl_auth gmap_view.
From iris.heap_lang Require Export primitive_laws notation.
From iris.heap_lang Require Export proofmode.
From iris.heap_lang.lib Require Import spin_lock.
From actris.utils Require Export llist.
From actris.channel Require Import proto_model.
From actris.channel Require Export proto.
Set Default Proof Using "Type".

(** * The definition of the message-passing connectives *)
Definition new_chan : val :=
  λ: <>, let: "l1" := ref NONEV in
         let: "l2" := ref NONEV in
         (("l1","l2"), ("l2","l1")).

Definition fork_chan : val := λ: "f",
  let: "cc" := new_chan #() in
  Fork ("f" (Snd "cc"));; Fst "cc".

Definition wait : val :=
  rec: "go" "l" :=
    match: !"l" with
      NONE => #()
    | SOME <> => "go" "l"
    end.

Definition send : val :=
  λ: "c" "v",
    let: "l" := Fst "c" in
    "l" <- SOME "v";; wait "l".

(* Definition recv : val := *)
(*   rec: "go" "c" "i" := *)
(*     let: "l" := Snd (llookup "c" "i") in *)
(*     match: !"l" with *)
(*       NONE => "go" "c" *)
(*     | SOME "v" => "c" <- NONE;; "v"  *)
(*     end. *)

Definition recv : val :=
  rec: "go" "c" :=
    let: "l" := Snd "c" in
    let: "v" := Xchg "l" NONEV in
    match: "v" with
      NONE => "go" "c"
    | SOME "v" => "v" 
    end.

Class chanG Σ := {
  chanG_tokG :: inG Σ (exclR unitO);
  chanG_protoG :: protoG Σ val;
}.
Definition chanΣ : gFunctors := #[ protoΣ val; GFunctor (exclR unitO) ].
Global Instance subG_chanΣ {Σ} : subG chanΣ Σ → chanG Σ.
Proof. solve_inG. Qed.

(** * Definition of the pointsto connective *)
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Definition tok `{!chanG Σ} (γ : gname) : iProp Σ := own γ (Excl ()).

Definition chan_inv `{!heapGS Σ, !chanG Σ} γ γE γt s (l:loc) : iProp Σ :=
  (l ↦ NONEV ∗ tok γt) ∨
  (∃ v m, l ↦ SOMEV v ∗
          iProto_own γ s (<!> m)%proto ∗
          (∃ p, iMsg_car m v (Next p) ∗ own γE (●E (Next p)))) ∨
  (∃ p, l ↦ NONEV ∗
          iProto_own γ s p ∗ own γE (●E (Next p))).

Definition iProto_pointsto_def `{!heapGS Σ, !chanG Σ}
    (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γ γE1 γE2 γt1 γt2 s (l1 l2:loc),
    ⌜ c = PairV #l1 #l2 ⌝ ∗
    inv (nroot.@"ctx") (iProto_ctx γ) ∗
    inv (nroot.@"p") (chan_inv γ γE1 γt1 s l1) ∗
    inv (nroot.@"p") (chan_inv γ γE2 γt2 (side_dual s) l2) ∗
    own γE1 (●E (Next p)) ∗ own γE1 (◯E (Next p)) ∗
    iProto_own γ s p.
Definition iProto_pointsto_aux : seal (@iProto_pointsto_def). by eexists. Qed.
Definition iProto_pointsto := iProto_pointsto_aux.(unseal).
Definition iProto_pointsto_eq :
  @iProto_pointsto = @iProto_pointsto_def := iProto_pointsto_aux.(seal_eq).
Arguments iProto_pointsto {_ _ _} _ _%proto.
Global Instance: Params (@iProto_pointsto) 4 := {}.
Notation "c ↣ p" := (iProto_pointsto c p)
  (at level 20, format "c  ↣  p").

Section channel.
  Context `{!heapGS Σ, !chanG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Global Instance iProto_pointsto_ne c : NonExpansive (iProto_pointsto c).
  Proof. rewrite iProto_pointsto_eq. solve_proper. Qed.
  Global Instance iProto_pointsto_proper c : Proper ((≡) ==> (≡)) (iProto_pointsto c).
  Proof. apply (ne_proper _). Qed.

  (* Lemma iProto_pointsto_le c p1 p2 : c ↣ p1 ⊢ ▷ (p1 ⊑ p2) -∗ c ↣ p2. *)
  (* Proof. *)
  (*   rewrite iProto_pointsto_eq. iDestruct 1 as (γ s l r lk ->) "[Hlk H]". *)
  (*   iIntros "Hle'". iExists γ, s, l, r, lk. iSplit; [done|]. iFrame "Hlk". *)
  (*   by iApply (iProto_own_le with "H"). *)
  (* Qed. *)

  (** ** Specifications of [send] and [recv] *)
  Lemma new_chan_spec p :
    {{{ True }}}
      new_chan #()
    {{{ c1 c2, RET (c1,c2); c1 ↣ p ∗ c2 ↣ iProto_dual p }}}.
  Proof.
    iIntros (Φ _) "HΦ". wp_lam.
    wp_alloc l1 as "Hl1".
    wp_alloc l2 as "Hl2".
    iMod (iProto_init p) as (γp) "(Hctx & Hcl & Hcr)".
    iMod (own_alloc (●E (Next p) ⋅ ◯E (Next p))) as (γl) "[H●l H◯l]".
    { by apply excl_auth_valid. }
    iMod (own_alloc (●E (Next (iProto_dual p)) ⋅ ◯E (Next (iProto_dual p)))) as (γr) "[H●r H◯r]".
    { by apply excl_auth_valid. }
    iMod (own_alloc (Excl ())) as (γtl) "Htokl".
    { done. }
    iMod (own_alloc (Excl ())) as (γtr) "Htokr".
    { done. }
    wp_pures.
    iMod (inv_alloc _ ⊤ (iProto_ctx γp) with "[Hctx]")
      as "#IH".
    { done. }
    iMod (inv_alloc _ ⊤ (chan_inv γp γl γtl Left l1) with "[Hl1 Htokl]")
      as "#IHl".
    { iLeft. iFrame. }
    iMod (inv_alloc _ ⊤ (chan_inv γp γr γtr Right l2) with "[Hl2 Htokr]")
      as "#IHr".
    { iLeft. iFrame. }
    iModIntro.
    iApply "HΦ".
    iSplitL "Hcl H●l H◯l".
    - rewrite iProto_pointsto_eq.
      iExists _, _, _, _, _, _, _, _. eauto with iFrame.
    - rewrite iProto_pointsto_eq.
      iExists _, _, _, _, _, _, _, _. 
      iSplit; [done|]. iFrame "#∗". 
  Qed.

  Lemma fork_chan_spec p Φ (f : val) :
    ▷ (∀ c, c ↣ iProto_dual p -∗ WP f c {{ _, True }}) -∗
    ▷ (∀ c, c ↣ p -∗ Φ c) -∗
    WP fork_chan f {{ Φ }}.
  Proof.
    iIntros "Hfork HΦ". wp_lam.
    wp_smart_apply (new_chan_spec p with "[//]"); iIntros (c1 c2) "[Hc1 Hc2]".
    wp_smart_apply (wp_fork with "[Hfork Hc2]").
    { iNext. wp_smart_apply ("Hfork" with "Hc2"). }
    wp_pures. iApply ("HΦ" with "Hc1").
  Qed.

  Lemma own_prot_excl γ (p1 p2 : iProto Σ) :
    own γ (◯E (Next p1)) -∗ own γ (◯E (Next p2)) -∗ False.
  Proof. Admitted.

  Lemma send_spec c v p :
    {{{ c ↣ <!> MSG v; p }}}
      send c v
    {{{ RET #(); c ↣ p }}}.
  Proof.
    rewrite iProto_pointsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (γ γE1 γE2 γt1 γt2 s l1 l2 ->)
                        "(#IH & #IHl & #IHr & H● & H◯ & Hown)".
    wp_pures.
    wp_bind (Store _ _).
    iInv "IHl" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]"; last first.
    { iDestruct "HIp" as "[HIp|HIp]".
      - iDestruct "HIp" as (? m) "(>Hl & Hown' & HIp)".
        wp_store.
        rewrite /iProto_own.
        iDestruct "Hown" as (p') "[_ Hown]".
        iDestruct "Hown'" as (p'') "[_ Hown']".
        iDestruct (own_prot_excl with "Hown Hown'") as "H". done.
      - iDestruct "HIp" as (p') "(>Hl & Hown' & HIp)".
        wp_store.
        rewrite /iProto_own.
        iDestruct "Hown" as (p'') "[_ Hown]".
        iDestruct "Hown'" as (p''') "[_ Hown']".
        iDestruct (own_prot_excl with "Hown Hown'") as "H". done. }
    iDestruct "HIp" as "[>Hl Htok]".
    wp_store.
    iMod (own_update_2 with "H● H◯") as "[H● H◯]".
    { apply excl_auth_update. }
    iModIntro.
    iSplitL "Hl H● Hown". 
    { iRight. iLeft. iIntros "!>". iExists _, _. iFrame.
      iExists _. iFrame. rewrite iMsg_base_eq. simpl. done. }
    wp_pures.
    iLöb as "HL".
    wp_lam.
    wp_bind (Load _).
    iInv "IHl" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]".
    { iDestruct "HIp" as ">[Hl Htok']".
      iDestruct (own_valid_2 with "Htok Htok'") as %H. done. }
    iDestruct "HIp" as "[HIp|HIp]".
    - iDestruct "HIp" as (? m) "(>Hl & Hown & HIp)".
      wp_load. iModIntro.
      iSplitL "Hl Hown HIp".
      { iRight. iLeft. iExists _, _. iFrame. }
      wp_pures. iApply ("HL" with "HΦ Htok H◯").
    - iDestruct "HIp" as (p') "(>Hl & Hown & H●)".
      wp_load.
      iModIntro.
      iSplitL "Hl Htok".
      { iLeft. iFrame. }
      iDestruct (own_valid_2 with "H● H◯") as "#Hagree".
      iDestruct (excl_auth_agreeI with "Hagree") as "Hagree'".
      wp_pures.
      iMod (own_update_2 with "H● H◯") as "[H● H◯]".
      { apply excl_auth_update. }
      iModIntro.
      iApply "HΦ".
      iExists _, _, _, _, _, _, _, _.
      iSplit; [done|]. iFrame "#∗".
      iRewrite -"Hagree'". done.
  Qed.

  (* Lemma send_spec_tele {TT} c (tt : TT) *)
  (*       (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) : *)
  (*   {{{ c ↣ (<!.. x > MSG v x {{ P x }}; p x) ∗ P tt }}} *)
  (*     send c (v tt) *)
  (*   {{{ RET #(); c ↣ (p tt) }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "[Hc HP] HΦ". *)
  (*   iDestruct (iProto_pointsto_le _ _ (<!> MSG v tt; p tt)%proto with "Hc [HP]") *)
  (*     as "Hc". *)
  (*   { iIntros "!>". *)
  (*     iApply iProto_le_trans. *)
  (*     iApply iProto_le_texist_intro_l. *)
  (*     by iFrame "HP". } *)
  (*   by iApply (send_spec with "Hc"). *)
  (* Qed. *)

  Lemma recv_spec {TT} c (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ <?.. x> MSG v x {{ ▷ P x }}; p x }}}
      recv c
    {{{ x, RET v x; c ↣ p x ∗ P x }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iLöb as "HL". wp_lam.
    rewrite iProto_pointsto_eq.
    iDestruct "Hc" as (γ E1 γE2 γt1 γt2 s l1 l2 ->)
                        "(#IH & #IHl & #IHr & H● & H◯ & Hown)".
    wp_pures.
    wp_bind (Xchg _ _).
    iInv "IHr" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]".
    { iDestruct "HIp" as ">[Hl Htok]".
      wp_xchg.
      iModIntro.
      iSplitL "Hl Htok".
      { iLeft. iFrame. }
      wp_pures. iApply ("HL" with "[H● H◯ Hown] HΦ").
      iExists _, _, _, _, _, _, _, _. iSplit; [done|]. iFrame "#∗". }
    iDestruct "HIp" as "[HIp|HIp]"; last first.
    { iDestruct "HIp" as (p') "[>Hl [Hown' H◯']]".
      wp_xchg.
      iModIntro.
      iSplitL "Hl Hown' H◯'".
      { iRight. iRight. iExists _. iFrame. }
      wp_pures. iApply ("HL" with "[H● H◯ Hown] HΦ").
      iExists _, _, _, _, _, _, _, _. iSplit; [done|]. iFrame "#∗". }
    iDestruct "HIp" as (w m) "(>Hl & Hown' & HIp)".
    iDestruct "HIp" as (p') "[Hm Hp']".
    iInv "IH" as "Hctx".
    wp_xchg.
    destruct s.
    - simpl.
      iMod (iProto_step_r with "Hctx Hown Hown' Hm") as
        (p'') "(Hm & Hctx & Hown & Hown')".
      iModIntro.
      iSplitL "Hctx"; [done|].
      iModIntro.
      iSplitL "Hl Hown' Hp'".
      { iRight. iRight. iExists _. iFrame. }
      wp_pure _.
      rewrite iMsg_base_eq. 
      iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
      wp_pures. 
      iMod (own_update_2 with "H● H◯") as "[H● H◯]".
      { apply excl_auth_update. }
      iModIntro. iApply "HΦ".
      iFrame.
      iExists _, _, _, _, _, _, _, _. iSplit; [done|].
      iRewrite "Hp". iFrame "#∗". done.
    - simpl.
      iMod (iProto_step_l with "Hctx Hown' Hown Hm") as
        (p'') "(Hm & Hctx & Hown & Hown')".
      iModIntro.
      iSplitL "Hctx"; [done|].
      iModIntro.
      iSplitL "Hl Hown Hp'".
      { iRight. iRight. iExists _. iFrame. }
      wp_pure _.
      rewrite iMsg_base_eq. 
      iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
      wp_pures. 
      iMod (own_update_2 with "H● H◯") as "[H● H◯]".
      { apply excl_auth_update. }
      iModIntro. iApply "HΦ".
      iFrame.
      iExists _, _, _, _, _, _, _, _. iSplit; [done|].
      iRewrite "Hp". iFrame "#∗". done.
  Qed.

End channel.
