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
From actris.channel Require Import multi_proto_model multi_proto.
Set Default Proof Using "Type".

(* TODO: Update new_chan definition to use pointers with offsets *)
(** * The definition of the message-passing connectives *)
Definition new_chan : val :=
  λ: "n",
    let: "l" := AllocN ("n"*"n") NONEV in
    let: "xxs" := AllocN "n" NONEV in
    (rec: "go1" "i" := if: "i" = "n" then #() else
       let: "xs" := AllocN "n" NONEV in
       (rec: "go2" "j" := if: "j" = "n" then #() else
          ("xs" +ₗ "j") <- ("l" +ₗ ("i"*"n"+"j"), "l" +ₗ ("j"*"n"+"i"));;
          "go2" ("j"+#1)) #0;;
       ("xxs" +ₗ "i") <- "xs";;
       "go1" ("i"+#1)) #0;; "xxs".

Definition wait : val :=
  rec: "go" "c" :=
    match: !"c" with
      NONE => #()
    | SOME <> => "go" "c"
    end.

Definition send : val :=
  λ: "c" "i" "v",
    let: "len" := Fst "c" in
    if: "i" < "len" then
      let: "l" := Fst (! ((Snd "c") +ₗ "i")) in
      "l" <- SOME "v";; wait "l"
    (* OBS: Hacky *)
    else (rec: "go" <> := "go" #())%V #().

Definition recv : val :=
  rec: "go" "c" "i" :=
    let: "len" := Fst "c" in
    if: "i" < "len" then
      let: "l" := Snd (! ((Snd "c") +ₗ "i")) in
      let: "v" := Xchg "l" NONEV in
      match: "v" with
        NONE => "go" "c" "i"
      | SOME "v" => "v"
      end
    (* OBS: Hacky *)
    else (rec: "go" <> := "go" #())%V #().

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
  (l ↦ NONEV ∗ tok γt) ∨
  (∃ v m, l ↦ SOMEV v ∗
            iProto_own γ i (<Send j> m)%proto ∗
            (∃ p, iMsg_car m v (Next p) ∗ own γE (●E (Next p)))) ∨
  (∃ p, l ↦ NONEV ∗
          iProto_own γ i p ∗ own γE (●E (Next p))).

Definition iProto_pointsto_def `{!heapGS Σ, !chanG Σ}
    (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γ γE1 γE2 γt1 γt2 i (l:loc) ls,
    ⌜ c = PairV #(length ls) #l ⌝ ∗
    inv (nroot.@"ctx") (iProto_ctx γ) ∗
    l ↦∗ ls ∗
    ([∗list] j ↦ v ∈ ls, 
       ∃ (l1 l2 : loc),
         ⌜v = PairV #l1 #l2⌝ ∗
         inv (nroot.@"p") (chan_inv γ γE1 γt1 i j l1) ∗
         inv (nroot.@"p") (chan_inv γ γE2 γt2 j i l2)) ∗
    own γE1 (●E (Next p)) ∗ own γE1 (◯E (Next p)) ∗
    iProto_own γ i p.
Definition iProto_pointsto_aux : seal (@iProto_pointsto_def). by eexists. Qed.
Definition iProto_pointsto := iProto_pointsto_aux.(unseal).
Definition iProto_pointsto_eq :
  @iProto_pointsto = @iProto_pointsto_def := iProto_pointsto_aux.(seal_eq).
Arguments iProto_pointsto {_ _ _} _ _%proto.
Global Instance: Params (@iProto_pointsto) 5 := {}.
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
  Lemma new_chan_spec (n:nat) (ps:gmap nat (iProto Σ)) :
    (∀ i, i < n → is_Some (ps !! i)) →
    {{{ iProto_consistent ps }}}
      new_chan #n
    {{{ cs ls, RET #cs;
        ⌜length ls = n⌝ ∗ cs ↦∗ ls ∗
        [∗list] i ↦ l ∈ ls, l ↣ (ps !!! i) }}}.
  Proof. Admitted.

  Lemma own_prot_excl γ i (p1 p2 : iProto Σ) :
    own γ (gmap_view_frag i (DfracOwn 1) (Excl' (Next p1))) -∗
    own γ (gmap_view_frag i (DfracOwn 1) (Excl' (Next p2))) -∗
    False.
  Proof. Admitted.

  Lemma send_spec c j v p :
    {{{ c ↣ <Send j> MSG v; p }}}
      send c #j v
    {{{ RET #(); c ↣ p }}}.
  Proof.
    rewrite iProto_pointsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as
      (γ γE1 γE2 γt1 γt2 i l ls ->) "(#IH & Hl & Hls & H● & H◯ & Hown)".
    wp_pures.
    case_bool_decide; last first.
    { wp_pures. iClear "IH H● H◯ Hown HΦ Hls Hl".
      iLöb as "IH". wp_lam. iApply "IH". }
    assert (is_Some (ls !! j)) as [l' HSome].
    { apply lookup_lt_is_Some_2. lia. }
    wp_pures.
    wp_smart_apply (wp_load_offset with "Hl").
    { done. } 
    iIntros "Hl". wp_pures.
    iDestruct (big_sepL_lookup_acc with "Hls") as "[Hj Hls]"; [done|].
    iDestruct "Hj" as (l1 l2 ->) "#[IHl1 IHl2]". 
    iDestruct ("Hls" with "[]") as "Hls".
    { iExists _, _. iFrame "#". done. }
    wp_pures.
    wp_bind (Store _ _).
    iInv "IHl1" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]"; last first.
    { iDestruct "HIp" as "[HIp|HIp]".
      - iDestruct "HIp" as (? m) "(>Hl' & Hown' & HIp)".
        wp_store.
        rewrite /iProto_own.
        iDestruct (own_prot_excl with "Hown Hown'") as "H". done.
      - iDestruct "HIp" as (p') "(>Hl' & Hown' & HIp)".
        wp_store.
        rewrite /iProto_own.
        iDestruct (own_prot_excl with "Hown Hown'") as "H". done. }
    iDestruct "HIp" as "[>Hl' Htok]".
    wp_store.
    iMod (own_update_2 with "H● H◯") as "[H● H◯]".
    { apply excl_auth_update. }
    iModIntro.
    iSplitL "Hl' H● Hown". 
    { iRight. iLeft. iIntros "!>". iExists _, _. iFrame.
      iExists _. iFrame. rewrite iMsg_base_eq. simpl. done. }
    wp_pures.
    iLöb as "HL".
    wp_lam.
    wp_bind (Load _).
    iInv "IHl1" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]".
    { iDestruct "HIp" as ">[Hl' Htok']".
      iDestruct (own_valid_2 with "Htok Htok'") as %[]. }
    iDestruct "HIp" as "[HIp|HIp]".
    - iDestruct "HIp" as (? m) "(>Hl' & Hown & HIp)".
      wp_load. iModIntro.
      iSplitL "Hl' Hown HIp".
      { iRight. iLeft. iExists _, _. iFrame. }
      wp_pures. iApply ("HL" with "HΦ Hl Hls Htok H◯").
    - iDestruct "HIp" as (p') "(>Hl' & Hown & H●)".
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
      iExists _, _, _, _, _, _, _, _.
      iSplit; [done|]. iFrame "#∗".
      iRewrite -"Hagree'". done.
  Qed.
  
  Lemma send_spec_tele {TT} c j (tt : TT)
        (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ (<(Send j) @.. x > MSG v x {{ P x }}; p x) ∗ P tt }}}
      send c #j (v tt)
    {{{ RET #(); c ↣ (p tt) }}}.
  Proof.
    rewrite iProto_pointsto_eq. iIntros (Φ) "[Hc HP] HΦ". wp_lam; wp_pures.    
    iDestruct "Hc" as
      (γ γE1 γE2 γt1 γt2 i l ls ->) "(#IH & Hl & Hls & H● & H◯ & Hown)".
    wp_pures.
    case_bool_decide; last first.
    { wp_pures. iClear "IH H● H◯ Hown HΦ Hls Hl".
      iLöb as "IH". wp_lam. iApply "IH". iFrame. }
    assert (is_Some (ls !! j)) as [l' HSome].
    { apply lookup_lt_is_Some_2. lia. }
    wp_pures.
    wp_smart_apply (wp_load_offset with "Hl").
    { done. } 
    iIntros "Hl". wp_pures.
    iDestruct (big_sepL_lookup_acc with "Hls") as "[Hj Hls]"; [done|].
    iDestruct "Hj" as (l1 l2 ->) "#[IHl1 IHl2]". 
    iDestruct ("Hls" with "[]") as "Hls".
    { iExists _, _. iFrame "#". done. }
    wp_pures.
    wp_bind (Store _ _).
    iInv "IHl1" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]"; last first.
    { iDestruct "HIp" as "[HIp|HIp]".
      - iDestruct "HIp" as (? m) "(>Hl' & Hown' & HIp)".
        wp_store.
        rewrite /iProto_own.
        iDestruct (own_prot_excl with "Hown Hown'") as "H". done.
      - iDestruct "HIp" as (p') "(>Hl' & Hown' & HIp)".
        wp_store.
        rewrite /iProto_own.
        iDestruct (own_prot_excl with "Hown Hown'") as "H". done. }
    iDestruct "HIp" as "[>Hl' Htok]".
    wp_store.
    iMod (own_update_2 with "H● H◯") as "[H● H◯]".
    { apply excl_auth_update. }
    iModIntro.
    iSplitL "Hl' H● Hown HP". 
    { iRight. iLeft. iIntros "!>". iExists _, _. iFrame.
      iExists _. iFrame. rewrite iMsg_base_eq. simpl.
      iApply iMsg_texist_exist.
      simpl. iExists tt.
      iSplit; [done|]. 
      iSplit; [done|]. 
      done. }
    wp_pures.
    iLöb as "HL".
    wp_lam.
    wp_bind (Load _).
    iInv "IHl1" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]".
    { iDestruct "HIp" as ">[Hl' Htok']".
      iDestruct (own_valid_2 with "Htok Htok'") as %[]. }
    iDestruct "HIp" as "[HIp|HIp]".
    - iDestruct "HIp" as (? m) "(>Hl' & Hown & HIp)".
      wp_load. iModIntro.
      iSplitL "Hl' Hown HIp".
      { iRight. iLeft. iExists _, _. iFrame. }
      wp_pures. iApply ("HL" with "HΦ Hl Hls Htok H◯").
    - iDestruct "HIp" as (p') "(>Hl' & Hown & H●)".
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
      iExists _, _, _, _, _, _, _, _.
      iSplit; [done|]. iFrame "#∗".
      iRewrite -"Hagree'". done.
  Qed.

  Lemma recv_spec {TT} c j (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ <(Recv j) @.. x> MSG v x {{ P x }}; p x }}}
      recv c #j
    {{{ x, RET v x; c ↣ p x ∗ P x }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iLöb as "HL". wp_lam.
    rewrite iProto_pointsto_eq.
    iDestruct "Hc" as
      (γ γE1 γE2 γt1 γt2 i l ls ->) "(#IH & Hl & Hls & H● & H◯ & Hown)".
    wp_pures.
    case_bool_decide; last first.
    { wp_pures. iClear "IH H● H◯ Hown HΦ Hls Hl".
      iLöb as "IH". wp_lam. iApply "IH". }
    wp_pures.
    assert (is_Some (ls !! j)) as [l' HSome].
    { apply lookup_lt_is_Some_2. lia. }
    wp_smart_apply (wp_load_offset with "Hl").
    { done. } 
    iIntros "Hl". wp_pures.
    iDestruct (big_sepL_lookup_acc with "Hls") as "[Hj Hls]"; [done|].
    iDestruct "Hj" as (l1 l2 ->) "#[IHl1 IHl2]". 
    iDestruct ("Hls" with "[]") as "Hls".
    { iExists _, _. iFrame "#". done. }    
    wp_pures.
    wp_bind (Xchg _ _).
    iInv "IHl2" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]".
    { iDestruct "HIp" as ">[Hl' Htok]".
      wp_xchg.
      iModIntro.
      iSplitL "Hl' Htok".
      { iLeft. iFrame. }
      wp_pures. iApply ("HL" with "[H● H◯ Hown Hls Hl] HΦ").
      iExists _, _, _, _, _, _, _, _. iSplit; [done|]. iFrame "#∗". }
    iDestruct "HIp" as "[HIp|HIp]"; last first.
    { iDestruct "HIp" as (p') "[>Hl' [Hown' H◯']]".
      wp_xchg.
      iModIntro.
      iSplitL "Hl' Hown' H◯'".
      { iRight. iRight. iExists _. iFrame. }
      wp_pures. iApply ("HL" with "[H● H◯ Hown Hls Hl] HΦ").
      iExists _, _, _, _, _, _, _, _. iSplit; [done|]. iFrame "#∗". }
    iDestruct "HIp" as (w m) "(>Hl' & Hown' & HIp)".
    iDestruct "HIp" as (p') "[Hm Hp']".
    iInv "IH" as "Hctx".
    wp_xchg.
    iMod (iProto_step with "Hctx Hown' Hown Hm") as
      (p'') "(Hm & Hctx & Hown & Hown')".
    iModIntro.
    iSplitL "Hctx"; [done|].
    iModIntro.
    iSplitL "Hl' Hown Hp'".
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
    iRewrite "Hp". iFrame "#∗".
  Qed.

End channel.
