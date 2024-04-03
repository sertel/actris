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
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Export primitive_laws notation proofmode.
From multi_actris.utils Require Import matrix.
From multi_actris.channel Require Import proto_model.
From multi_actris.channel Require Export proto.
Set Default Proof Using "Type".

(** * The definition of the message-passing connectives *)
Definition new_chan : val :=
  λ: "n", new_matrix "n" "n" NONEV.

Definition get_chan : val :=
  λ: "cs" "i", ("cs","i").

Definition wait : val :=
  rec: "go" "c" :=
    match: !"c" with
      NONE => #()
    | SOME <> => "go" "c"
    end.

Definition send : val :=
  λ: "c" "j" "v",
    let: "m" := Fst "c" in
    let: "i" := Snd "c" in
    let: "l" := matrix_get "m" "i" "j" in
    "l" <- SOME "v";; wait "l".

(* TODO: Move recursion further in *)
Definition recv : val :=
  rec: "go" "c" "j" :=
    let: "m" := Fst "c" in
    let: "i" := Snd "c" in
    let: "l" := matrix_get "m" "j" "i" in
    let: "v" := Xchg "l" NONEV in
    match: "v" with
      NONE     => "go" "c" "j"
    | SOME "v" => "v"
    end.

(** * Setup of Iris's cameras *)
Class proto_exclG Σ V :=
  protoG_exclG ::
    inG Σ (excl_authR (laterO (proto (leibnizO V) (iPropO Σ) (iPropO Σ)))).

Definition proto_exclΣ V := #[
  GFunctor (authRF (optionURF (exclRF (laterOF (protoOF (leibnizO V) idOF idOF)))))
].

Class chanG Σ := {
  chanG_proto_exclG :: proto_exclG Σ val;
  chanG_tokG :: inG Σ (exclR unitO);
  chanG_protoG :: protoG Σ val;
}.
Definition chanΣ : gFunctors := #[ proto_exclΣ val; protoΣ val; GFunctor (exclR unitO) ].
Global Instance subG_chanΣ {Σ} : subG chanΣ Σ → chanG Σ.
Proof. solve_inG. Qed.

(** * Definition of the pointsto connective *)
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Definition tok `{!chanG Σ} (γ : gname) : iProp Σ := own γ (Excl ()).

Definition chan_inv `{!heapGS Σ, !chanG Σ} γ γE γt i j (l:loc) : iProp Σ :=
  (l ↦ NONEV ∗ tok γt)%I ∨
  (∃ v p, l ↦ SOMEV v ∗
          iProto_own γ i (<(Send, j)> MSG v ; p)%proto ∗ own γE (●E (Next p))) ∨
  (∃ p, l ↦ NONEV ∗
          iProto_own γ i p ∗ own γE (●E (Next p))).

Definition iProto_pointsto_def `{!heapGS Σ, !chanG Σ}
    (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γ (γEs : list gname) (m:val) (i:nat) (n:nat) p',
    ⌜ c = (m,#i)%V ⌝ ∗
    inv (nroot.@"ctx") (iProto_ctx γ n) ∗
    is_matrix m n n
      (λ i j l, ∃ γt, inv (nroot.@"p") (chan_inv γ (γEs !!! i) γt i j l)) ∗
    ▷ (p' ⊑ p) ∗
    own (γEs !!! i) (●E (Next p')) ∗ own (γEs !!! i) (◯E (Next p')) ∗
    iProto_own γ i p'.
Definition iProto_pointsto_aux : seal (@iProto_pointsto_def). by eexists. Qed.
Definition iProto_pointsto := iProto_pointsto_aux.(unseal).
Definition iProto_pointsto_eq :
  @iProto_pointsto = @iProto_pointsto_def := iProto_pointsto_aux.(seal_eq).
Arguments iProto_pointsto {_ _ _} _ _%proto.
Global Instance: Params (@iProto_pointsto) 5 := {}.
Notation "c ↣ p" := (iProto_pointsto c p)
  (at level 20, format "c  ↣  p").

Definition chan_pool `{!heapGS Σ, !chanG Σ}
    (m : val) (i':nat) (ps : list (iProto Σ)) : iProp Σ :=
  ∃ γ (γEs : list gname) (n:nat),
    ⌜(i' + length ps = n)%nat⌝ ∗
    inv (nroot.@"ctx") (iProto_ctx γ n) ∗
    is_matrix m n n (λ i j l,
      ∃ γt, inv (nroot.@"p") (chan_inv γ (γEs !!! i) γt i j l)) ∗
    [∗ list] i ↦ p ∈ ps,
      (own (γEs !!! (i+i')) (●E (Next p)) ∗
       own (γEs !!! (i+i')) (◯E (Next p)) ∗
       iProto_own γ (i+i') p).

Section channel.
  Context `{!heapGS Σ, !chanG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Global Instance iProto_pointsto_ne c : NonExpansive (iProto_pointsto c).
  Proof. rewrite iProto_pointsto_eq. solve_proper. Qed.
  Global Instance iProto_pointsto_proper c : Proper ((≡) ==> (≡)) (iProto_pointsto c).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_pointsto_le c p1 p2 : c ↣ p1 ⊢ ▷ (p1 ⊑ p2) -∗ c ↣ p2.
  Proof.
    rewrite iProto_pointsto_eq.
    iDestruct 1 as (?????? ->) "(#IH & Hls & Hle & H● & H◯ & Hown)".
    iIntros "Hle'". iExists _,_,_,_,_,p'.
    iSplit; [done|]. iFrame "#∗".
    iApply (iProto_le_trans with "Hle Hle'").
  Qed.

  (** ** Specifications of [send] and [recv] *)
  Lemma new_chan_spec (ps:list (iProto Σ)) :
    0 < length ps →
    {{{ iProto_consistent ps }}}
      new_chan #(length ps)
    {{{ cs, RET cs; chan_pool cs 0 ps }}}.
  Proof.
    iIntros (Hle Φ) "Hps HΦ". wp_lam.
    iMod (iProto_init with "Hps") as (γ) "[Hps Hps']".
    iAssert (|==> ∃ (γEs : list gname),
                ⌜length γEs = length ps⌝ ∗
                [∗ list] i ↦ p ∈ ps,
                  own (γEs !!! i) (●E (Next (ps !!! i))) ∗
                  own (γEs !!! i) (◯E (Next (ps !!! i))) ∗
                  iProto_own γ i (ps !!! i))%I with "[Hps']" as "H".
    { clear Hle.
      iInduction ps as [|p ps] "IHn" using rev_ind.
      { iExists []. iModIntro. simpl. done. }
      iDestruct "Hps'" as "[Hps' Hp]".
      iMod (own_alloc (●E (Next p) ⋅ ◯E (Next p))) as (γE) "[Hauth Hfrag]".
      { apply excl_auth_valid. }
      iMod ("IHn" with "Hps'") as (γEs Hlen) "H".
      iModIntro. iExists (γEs++[γE]).
      rewrite !app_length Hlen.
      iSplit; [iPureIntro=>/=;lia|]=> /=.
      iSplitL "H".
      { iApply (big_sepL_impl with "H").
        iIntros "!>" (i ? HSome') "(Hauth & Hfrag & Hown)".
        assert (i < length ps) as Hle.
        { by apply lookup_lt_is_Some_1. }
        rewrite !lookup_total_app_l; [|lia..]. iFrame. }
      rewrite Nat.add_0_r.
      simpl. rewrite right_id_L.
      rewrite !lookup_total_app_r; [|lia..]. rewrite !Hlen.
      rewrite Nat.sub_diag. simpl. iFrame.
      iDestruct "Hp" as "[$ _]". }
    iMod "H" as (γEs Hlen) "H".
    iMod (inv_alloc with "Hps") as "#IHp".
    wp_smart_apply (new_matrix_spec _ _ _ _
                     (λ i j l, ∃ γt,
            inv (nroot.@"p") (chan_inv γ (γEs !!! i) γt i j
                                       l))%I); [done..| |].
    { iApply (big_sepL_intro).
      iIntros "!>" (k tt Hin).
      iApply (big_sepL_intro).
      iIntros "!>" (k' tt' Hin').
      iIntros (l) "Hl".
      iMod (own_alloc (Excl ())) as (γ') "Hγ'"; [done|].
      iExists γ'.
      iApply inv_alloc.
      iNext.
      iLeft. iFrame. }
    iIntros (mat) "Hmat".
    iApply "HΦ".
    iExists _, _, _. iFrame "#∗".
    rewrite left_id. iSplit; [done|].
    iApply (big_sepL_impl with "H").
    iIntros "!>" (i ? HSome') "(Hauth & Hfrag & Hown)".
    iFrame.
    rewrite (list_lookup_total_alt ps).
    simpl. rewrite right_id_L. rewrite HSome'. iFrame.
  Qed.

  Lemma get_chan_spec cs i ps p :
    {{{ chan_pool cs i (p::ps) }}}
      get_chan cs #i
    {{{ c, RET c; c ↣ p ∗ chan_pool cs (i+1) ps }}}.
  Proof.
    iIntros (Φ) "Hcs HΦ".
    iDestruct "Hcs" as (γp γEs n <-) "(#IHp & #Hm & Hl)".
    wp_lam. wp_pures.
    iDestruct "Hl" as "[Hl Hls]".
    iModIntro.
    iApply "HΦ".
    iSplitL "Hl".
    { rewrite iProto_pointsto_eq. iExists _, _, _, _, _, _.
      iSplit; [done|].
      iFrame. iFrame "#∗". iNext. done. }
    iExists γp, γEs, _. iSplit; [done|].
    iFrame. iFrame "#∗".
    simpl.
    replace (i + 1 + length ps) with (i + (S $ length ps))%nat by lia.
    iFrame "#".
    iApply (big_sepL_impl with "Hls").
    iIntros "!>" (k x HSome) "(H1 & H2 & H3)".
    replace (S (k + i)) with (k + (i + 1)) by lia.
    iFrame.
  Qed.

  Lemma send_spec c j v p :
    {{{ c ↣ <(Send, j)> MSG v; p }}}
      send c #j v
    {{{ RET #(); c ↣ p }}}.
  Proof.
    rewrite iProto_pointsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as
      (γ γE l i n p' ->) "(#IH & #Hls & Hle & H● & H◯ & Hown)".
    wp_bind (Fst _).
    iInv "IH" as "Hctx".
    iDestruct (iProto_le_msg_inv_r with "Hle") as (m') "#Heq".
    iRewrite "Heq" in "Hown".
    iDestruct (iProto_ctx_agree with "Hctx [Hown//]") as "#Hi".
    iDestruct (iProto_target with "Hctx [Hown//]") as "#Hj".
    iRewrite -"Heq" in "Hown". wp_pures. iModIntro. iFrame.
    wp_pures.
    iDestruct "Hi" as %Hi.
    iDestruct "Hj" as %Hj.
    wp_smart_apply (matrix_get_spec with "Hls"); [done..|].
    iIntros (l') "[Hl' _]".
    iDestruct "Hl'" as (γt) "#IHl1".
    wp_pures. wp_bind (Store _ _).
    iInv "IHl1" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]"; last first.
    { iDestruct "HIp" as "[HIp|HIp]".
      - iDestruct "HIp" as (? p'') "(>Hl & Hown' & HIp)".
        wp_store.
        iDestruct (iProto_own_excl with "Hown Hown'") as %[].
      - iDestruct "HIp" as (p'') "(>Hl' & Hown' & HIp)".
        wp_store.
        iDestruct (iProto_own_excl with "Hown Hown'") as %[]. }
    iDestruct "HIp" as "[>Hl' Htok]".
    wp_store.
    iMod (own_update_2 with "H● H◯") as "[H● H◯]"; [by apply excl_auth_update|].
    iModIntro.
    iSplitL "Hl' H● Hown Hle".
    { iRight. iLeft. iIntros "!>". iExists _, _. iFrame.
      iDestruct (iProto_own_le with "Hown Hle") as "Hown".
      by rewrite iMsg_base_eq. }
    wp_pures.
    iLöb as "HL".
    wp_lam.
    wp_bind (Load _).
    iInv "IHl1" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]".
    { iDestruct "HIp" as ">[Hl' Htok']".
      iDestruct (own_valid_2 with "Htok Htok'") as %[]. }
    iDestruct "HIp" as "[HIp|HIp]".
    - iDestruct "HIp" as (? p'') "(>Hl' & Hown & HIp)".
      wp_load. iModIntro.
      iSplitL "Hl' Hown HIp".
      { iRight. iLeft. iExists _,_. iFrame. }
      wp_pures. iApply ("HL" with "HΦ Htok H◯").
    - iDestruct "HIp" as (p'') "(>Hl' & Hown & H●)".
      wp_load.
      iModIntro.
      iSplitL "Hl' Htok".
      { iLeft. iFrame. }
      iDestruct (own_valid_2 with "H● H◯") as "#Hagree".
      iDestruct (excl_auth_agreeI with "Hagree") as "Hagree'".
      wp_pures.
      iMod (own_update_2 with "H● H◯") as "[H● H◯]".
      { apply excl_auth_update. }
      iModIntro.
      iApply "HΦ".
      iExists _, _, _, _, _, _.
      iSplit; [done|]. iFrame "#∗".
      iRewrite -"Hagree'". iApply iProto_le_refl.
  Qed.

  Lemma send_spec_tele {TT} c i (tt : TT)
        (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ (<(Send,i) @.. x > MSG v x {{ P x }}; p x) ∗ P tt }}}
      send c #i (v tt)
    {{{ RET #(); c ↣ (p tt) }}}.
  Proof.
    iIntros (Φ) "[Hc HP] HΦ".
    iDestruct (iProto_pointsto_le _ _ (<(Send,i)> MSG v tt; p tt)%proto
                with "Hc [HP]") as "Hc".
    { iIntros "!>". iApply iProto_le_trans. iApply iProto_le_texist_intro_l.
      by iApply iProto_le_payload_intro_l. }
    by iApply (send_spec with "Hc").
  Qed.

  Lemma recv_spec {TT} c j (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ <(Recv, j) @.. x> MSG v x {{ ▷ P x }}; p x }}}
      recv c #j
    {{{ x, RET v x; c ↣ p x ∗ P x }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iLöb as "HL". wp_lam.
    rewrite iProto_pointsto_eq.
    iDestruct "Hc" as
      (γ γE l i n p' ->) "(#IH & #Hls & Hle & H● & H◯ & Hown)".
    do 5 wp_pure _.
    wp_bind (Snd _).
    iInv "IH" as "Hctx".
    iDestruct (iProto_le_msg_inv_r with "Hle") as (m') "#Heq".
    iRewrite "Heq" in "Hown".
    iDestruct (iProto_ctx_agree with "Hctx [Hown//]") as "#Hi".
    iDestruct (iProto_target with "Hctx [Hown//]") as "#Hj".
    iRewrite -"Heq" in "Hown". wp_pures. iModIntro. iFrame.
    wp_pure _.
    iDestruct "Hi" as %Hi.
    iDestruct "Hj" as %Hj.
    wp_smart_apply (matrix_get_spec with "Hls"); [done..|].
    iIntros (l') "[Hl' _]".
    iDestruct "Hl'" as (γt) "#IHl2".
    wp_pures.
    wp_bind (Xchg _ _).
    iInv "IHl2" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]".
    { iDestruct "HIp" as ">[Hl' Htok]".
      wp_xchg. iModIntro.
      iSplitL "Hl' Htok".
      { iLeft. iFrame. }
      wp_pures. iApply ("HL" with "[H● H◯ Hown Hle] HΦ").
      iExists _, _, _, _, _, _. iSplit; [done|]. iFrame "#∗". }
    iDestruct "HIp" as "[HIp|HIp]"; last first.
    { iDestruct "HIp" as (p'') "[>Hl' [Hown' H◯']]".
      wp_xchg.
      iModIntro.
      iSplitL "Hl' Hown' H◯'".
      { iRight. iRight. iExists _. iFrame. }
      wp_pures. iApply ("HL" with "[H● H◯ Hown Hle] HΦ").
      iExists _, _, _, _, _, _. iSplit; [done|]. iFrame "#∗". }
    iDestruct "HIp" as (w p'') "(>Hl' & Hown' & Hp')".
    iInv "IH" as "Hctx".
    wp_xchg.
    iDestruct (iProto_own_le with "Hown Hle") as "Hown".
    iMod (iProto_step with "Hctx Hown' Hown []") as
      (p''') "(Hm & Hctx & Hown & Hown')".
    { by rewrite iMsg_base_eq. }
    iModIntro.
    iSplitL "Hctx"; [done|].
    iModIntro.
    iSplitL "Hl' Hown Hp'".
    { iRight. iRight. iExists _. iFrame. }
    wp_pure _.
    rewrite iMsg_base_eq.
    iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
    wp_pures.
    iMod (own_update_2 with "H● H◯") as "[H● H◯]";
      [apply (excl_auth_update _ _ (Next p'''))|].
    iModIntro. iApply "HΦ". rewrite /iProto_pointsto_def. iFrame "IH Hls ∗".
    iSplit; [done|]. iRewrite "Hp". iApply iProto_le_refl.
  Qed.

End channel.
