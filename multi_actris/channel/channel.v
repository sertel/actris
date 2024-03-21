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
From multi_actris.channel Require Import proto_model.
From multi_actris.channel Require Export proto.
Set Default Proof Using "Type".

(** * The definition of the message-passing connectives *)
Definition new_chan : val :=
  λ: "n", (AllocN ("n"*"n") NONEV, "n").

Definition get_chan : val :=
  λ: "cs" "i", ("cs","i").

Definition wait : val :=
  rec: "go" "c" :=
    match: !"c" with
      NONE => #()
    | SOME <> => "go" "c"
    end.


Definition pos (n i j : nat) : nat := i * n + j.
Definition vpos : val := λ: "n" "i" "j", "i"*"n" + "j".

Definition send : val :=
  λ: "c" "j" "v",
    let: "n" := Snd (Fst "c") in
    let: "ls" := Fst (Fst "c") in
    let: "i" := Snd "c" in
    let: "l" := "ls" +ₗ vpos "n" "i" "j" in
    "l" <- SOME "v";; wait "l".

(* TODO: Move recursion further in *)
Definition recv : val :=
  rec: "go" "c" "j" :=
    let: "n" := Snd (Fst "c") in
    let: "ls" := Fst (Fst "c") in
    let: "i" := Snd "c" in
    let: "l" := "ls" +ₗ vpos "n" "j" "i" in
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
  (∃ v m, l ↦ SOMEV v ∗
            iProto_own γ i (<(Send, j)> m)%proto ∗
            (∃ p, iMsg_car m v (Next p) ∗ own γE (●E (Next p)))) ∨
  (∃ p, l ↦ NONEV ∗
          iProto_own γ i p ∗ own γE (●E (Next p))).

Definition iProto_pointsto_def `{!heapGS Σ, !chanG Σ}
    (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γ γE1 (l:loc) (i:nat) (n:nat) p',
    ⌜ c = (#l,#n,#i)%V ⌝ ∗
    inv (nroot.@"ctx") (iProto_ctx γ n) ∗
    ([∗list] j ↦ _ ∈ replicate n (),
       ∃ γE2 γt1 γt2,
         inv (nroot.@"p") (chan_inv γ γE1 γt1 i j (l +ₗ (pos n i j))) ∗
         inv (nroot.@"p") (chan_inv γ γE2 γt2 j i (l +ₗ (pos n j i)))) ∗
    ▷ (p' ⊑ p) ∗
    own γE1 (●E (Next p')) ∗ own γE1 (◯E (Next p')) ∗
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
    (cs : val) (i':nat) (ps : list (iProto Σ)) : iProp Σ :=
  ∃ γ (γEs : list gname) (n:nat) (l:loc),
    ⌜cs = (#l,#n)%V⌝ ∗ ⌜(i' + length ps = n)%nat⌝ ∗
    inv (nroot.@"ctx") (iProto_ctx γ n) ∗
    [∗ list] i ↦ _ ∈ replicate n (),
      (∀ p, ⌜i' <= i⌝ -∗ ⌜ps !! (i - i') = Some p⌝ -∗
            own (γEs !!! i) (●E (Next p)) ∗
            own (γEs !!! i) (◯E (Next p)) ∗
            iProto_own γ i p) ∗
      [∗ list] j ↦ _ ∈ replicate n (),
        ∃ γt1 γt2,
        inv (nroot.@"p") (chan_inv γ (γEs !!! i) γt1 i j (l +ₗ (pos n i j))) ∗
        inv (nroot.@"p") (chan_inv γ (γEs !!! j) γt2 j i (l +ₗ (pos n j i))).

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

  Lemma big_sepL_replicate {A B} n (x1 : A) (x2 : B) (P : nat → iProp Σ) :
    ([∗ list] i ↦ _ ∈ replicate n x1, P i) ⊢
    ([∗ list] i ↦ _ ∈ replicate n x2, P i).
  Proof.
    iIntros "H".
    iInduction n as [|n] "IHn"; [done|].
    replace (S n) with (n + 1) by lia.
    rewrite !replicate_add /=. iDestruct "H" as "[H1 H2]".
    iSplitL "H1"; [by iApply "IHn"|]=> /=.
    by rewrite !replicate_length.
  Qed.

  Lemma array_to_matrix_pre l n m v :
    l ↦∗ replicate (n * m) v -∗
    [∗ list] i ↦ _ ∈ replicate n (), (l +ₗ i*m) ↦∗ replicate m v.
  Proof.
    iIntros "Hl".
    iInduction n as [|n] "IHn"; [done|].
    replace (S n) with (n + 1) by lia.
    replace ((n + 1) * m) with (n * m + m) by lia.
    rewrite !replicate_add /= array_app=> /=.
    iDestruct "Hl" as "[Hl Hls]".
    iDestruct ("IHn" with "Hl") as "Hl".
    iFrame=> /=.
    rewrite Nat.add_0_r !replicate_length.
    replace (Z.of_nat (n * m)) with (Z.of_nat n * Z.of_nat m)%Z by lia.
    by iFrame.
  Qed.

  Lemma array_to_matrix l n v :
    l ↦∗ replicate (n * n) v -∗
    [∗ list] i ↦ _ ∈ replicate n (),
      [∗ list] j ↦ _ ∈ replicate n (),
        (l +ₗ pos n i j) ↦ v.
  Proof.
    iIntros "Hl".
    iDestruct (array_to_matrix_pre with "Hl") as "Hl".
    iApply (big_sepL_impl with "Hl").
    iIntros "!>" (i ? _) "Hl".
    iApply big_sepL_replicate.
    iApply (big_sepL_impl with "Hl").
    iIntros "!>" (j ? HSome) "Hl".
    rewrite Loc.add_assoc.
    replace (Z.of_nat i * Z.of_nat n + Z.of_nat j)%Z with
      (Z.of_nat (i * n + j))%Z by lia.
    by apply lookup_replicate in HSome as [-> _].
  Qed.

  (** ** Specifications of [send] and [recv] *)
  Lemma new_chan_spec (ps:list (iProto Σ)) :
    0 < length ps →
    {{{ iProto_consistent ps }}}
      new_chan #(length ps)
    {{{ cs, RET cs; chan_pool cs 0 ps }}}.
  Proof.
    iIntros (Hle Φ) "Hps HΦ". wp_lam.
    wp_smart_apply wp_allocN; [lia|done|].
    iIntros (l) "[Hl _]".
    iMod (iProto_init with "Hps") as (γ) "[Hps Hps']".
    wp_pures. iApply "HΦ".
    iAssert (|==> ∃ (γEs : list gname),
                ⌜length γEs = length ps⌝ ∗
                [∗ list] i ↦ _ ∈ replicate (length ps) (),
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
      rewrite replicate_add.
      iSplitL "H".
      { iApply (big_sepL_impl with "H").
        iIntros "!>" (i ? HSome') "(Hauth & Hfrag & Hown)".
        assert (i < length ps) as Hle.
        { by apply lookup_replicate_1 in HSome' as [??]. }
        rewrite !lookup_total_app_l; [|lia..]. iFrame. }
      rewrite replicate_length Nat.add_0_r.
      simpl. rewrite right_id_L.
      rewrite !lookup_total_app_r; [|lia..]. rewrite !Hlen.
      rewrite Nat.sub_diag. simpl. iFrame.
      iDestruct "Hp" as "[$ _]". }
    iMod "H" as (γEs Hlen) "H".
    set n := length ps.
    iAssert (|={⊤}=>
        [∗ list] i ↦ _ ∈ replicate (length ps) (),
          [∗ list] j ↦ _ ∈ replicate (length ps) (),
            ∃ γt,
            inv (nroot.@"p") (chan_inv γ (γEs !!! i) γt i j
                                       (l +ₗ (pos (length ps) i j))))%I with "[Hl]" as "IH".
    { replace (Z.to_nat (Z.of_nat n * Z.of_nat n)) with (n*n) by lia.
      iDestruct (array_to_matrix with "Hl") as "Hl".
      iApply big_sepL_fupd.
      iApply (big_sepL_impl with "Hl").
      iIntros "!>" (i ? HSome') "H1".
      iApply big_sepL_fupd.
      iApply (big_sepL_impl with "H1").
      iIntros "!>" (j ? HSome'') "H1".
      iMod (own_alloc (Excl ())) as (γ') "Hγ'"; [done|].
      iExists γ'. iApply inv_alloc. iLeft. iFrame. }
    iMod "IH" as "#IH".
    iMod (inv_alloc with "Hps") as "#IHp".
    iExists _,_,_,_.
    iModIntro.
    iSplit.
    { iPureIntro. done. }
    iSplit.
    { done. }
    iFrame "IHp".
    iApply (big_sepL_impl with "H").
    iIntros "!>" (i ? HSome') "(Hauth & Hfrag & Hown)".
    iSplitL.
    { iIntros (p Hle' HSome'').
      iFrame. rewrite right_id_L in HSome''.
      rewrite (list_lookup_total_alt ps).
      rewrite HSome''. simpl. iFrame. }
    iApply big_sepL_intro.
    iIntros "!>" (j ? HSome'').
    assert (i < n) as Hle'.
    { apply lookup_replicate in HSome' as [_ Hle']. done. }
    assert (j < n) as Hle''.
    { apply lookup_replicate in HSome'' as [_ Hle'']. done. }
    iDestruct (big_sepL_lookup _ _ i () with "IH") as "IH'";
      [by rewrite lookup_replicate|].
    iDestruct (big_sepL_lookup _ _ j () with "IH'") as "IH''";
      [by rewrite lookup_replicate|].
    iDestruct (big_sepL_lookup _ _ j () with "IH") as "H";
      [by rewrite lookup_replicate|].
    iDestruct (big_sepL_lookup _ _ i () with "H") as "H'";
      [by rewrite lookup_replicate|].
    iDestruct "IH''" as (γ1) "?".
    iDestruct "H'" as (γ2) "?".
    iExists _, _. iFrame "#".
  Qed.

  Lemma get_chan_spec cs i ps p :
    {{{ chan_pool cs i (p::ps) }}}
      get_chan cs #i
    {{{ c, RET c; c ↣ p ∗ chan_pool cs (i+1) ps }}}.
  Proof.
    iIntros (Φ) "Hcs HΦ".
    iDestruct "Hcs" as (γp γEs n l -> <-) "[#IHp Hl]".
    wp_lam. wp_pures.
    simpl.
    rewrite replicate_add. simpl.
    iDestruct "Hl" as "[Hl1 [[Hi #IHs] Hl3]]". simpl.
    iDestruct ("Hi" with "[] []") as "(Hauth & Hown & Hp)".
    { rewrite right_id_L. rewrite replicate_length. iPureIntro. lia. }
    { rewrite right_id_L. rewrite replicate_length.
      rewrite Nat.sub_diag. simpl. done. }
    iModIntro.
    iApply "HΦ".
    iSplitR "Hl1 Hl3".
    { rewrite iProto_pointsto_eq. iExists _, _, _, _, _, _.
      iSplit; [done|].
      rewrite replicate_length. rewrite right_id_L.
      iFrame "#∗".
      iSplit; [|iNext; done].
      rewrite replicate_add.
      iApply (big_sepL_impl with "IHs").
      iIntros "!>" (???). iDestruct 1 as (γt1 γt2) "[??]".
      iExists _,_,_. iFrame. }
    iExists _, _, _, _. iSplit; [done|].
    iSplit.
    { iPureIntro. lia. }
    iFrame "#∗".
    rewrite replicate_add.
    simpl.
    iSplitL "Hl1".
    { iApply (big_sepL_impl with "Hl1").
      iIntros "!>" (i' ? HSome'').
      assert (i' < i).
      { rewrite lookup_replicate in HSome''. lia. }
      iIntros "[H $]" (p' Hle'). lia. }
    simpl.
    iFrame "#∗".
    iSplitR.
    { iIntros (p' Hle'). rewrite right_id_L in Hle'.
      rewrite replicate_length in Hle'. lia. }
    iApply (big_sepL_impl with "Hl3").
    iIntros "!>" (i' ? HSome'').
    assert (i' < length ps).
    { rewrite lookup_replicate in HSome''. lia. }
    iIntros "[H $]" (p' Hle' HSome).
    iApply "H".
    { iPureIntro. lia. }
    iPureIntro.
    rewrite replicate_length.
    rewrite replicate_length in HSome.
    replace (i + S i' - i) with (S i') by lia.
    simpl.
    replace (i + S i' - (i+1)) with (i') in HSome by lia.
    done.
  Qed.

  Lemma vpos_spec (n i j : nat) :
    {{{ True }}} vpos #n #i #j {{{ RET #(pos n i j); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_pures. rewrite /pos.
    replace (Z.of_nat i * Z.of_nat n + Z.of_nat j)%Z with
      (Z.of_nat (i * n + j)) by lia.
    by iApply "HΦ".
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
    iInv "IH" as "HI".
    iDestruct (iProto_le_msg_inv_r with "Hle") as (m') "#Heq".
    iRewrite "Heq" in "Hown".
    iAssert (▷ (▷ ⌜j < n⌝ ∗ iProto_own γ i (<(Send, j)> m') ∗
                iProto_ctx γ n))%I with "[HI Hown]"
      as "[HI [Hown Hctx]]".
    { iNext. iDestruct (iProto_target with "HI Hown") as "[Hin [$ $]]".
      iFrame. }
    iRewrite -"Heq" in "Hown". wp_pures. iModIntro. iFrame.
    wp_smart_apply (vpos_spec); [done|]; iIntros "_".
    iDestruct "HI" as %Hle.
    iDestruct (big_sepL_lookup_acc with "Hls") as "[Hj _]";
      [by apply lookup_replicate_2|].
    iDestruct "Hj" as (γE' γt γt') "#[IHl1 IHl2]".
    wp_pures. wp_bind (Store _ _).
    iInv "IHl1" as "HIp".
    iDestruct "HIp" as "[HIp|HIp]"; last first.
    { iDestruct "HIp" as "[HIp|HIp]".
      - iDestruct "HIp" as (? m) "(>Hl & Hown' & HIp)".
        wp_store.
        rewrite /iProto_own.
        iDestruct "Hown" as (p'') "[Hle' Hown]".
        iDestruct "Hown'" as (p''') "[Hle'' Hown']".
        iDestruct (own_prot_excl with "Hown Hown'") as "H". done.
      - iDestruct "HIp" as (p'') "(>Hl' & Hown' & HIp)".
        wp_store.
        rewrite /iProto_own.
        iDestruct "Hown" as (p''') "[Hle' Hown]".
        iDestruct "Hown'" as (p'''') "[Hle'' Hown']".
        iDestruct (own_prot_excl with "Hown Hown'") as "H". done. }
    iDestruct "HIp" as "[>Hl' Htok]".
    wp_store.
    iMod (own_update_2 with "H● H◯") as "[H● H◯]"; [by apply excl_auth_update|].
    iModIntro.
    iSplitL "Hl' H● Hown Hle".
    { iRight. iLeft. iIntros "!>". iExists _, _. iFrame.
      iSplitL "Hown Hle"; [by iApply (iProto_own_le with "Hown Hle")|].
      iExists _. iFrame. by rewrite iMsg_base_eq. }
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
    do 6 wp_pure _. wp_bind (Fst _). wp_pure _.
    iInv "IH" as "HI".
    iDestruct (iProto_le_msg_inv_r with "Hle") as (m') "#Heq".
    iRewrite "Heq" in "Hown".
    iAssert (▷ (▷ ⌜j < n⌝ ∗ iProto_own γ i (<(Recv, j)> m') ∗
                iProto_ctx γ n))%I with "[HI Hown]" as "[HI [Hown Hctx]]".
    { iNext. iDestruct (iProto_target with "HI Hown") as "[Hin [$$]]".
      iFrame. }
    iRewrite -"Heq" in "Hown". wp_pures. iModIntro. iFrame.
    wp_smart_apply (vpos_spec); [done|]; iIntros "_".
    iDestruct "HI" as %Hle.
    iDestruct (big_sepL_lookup_acc with "Hls") as "[Hj _]";
      [by apply lookup_replicate_2|].
    iDestruct "Hj" as (γE' γt γt') "#[IHl1 IHl2]".
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
    iDestruct "HIp" as (w m) "(>Hl' & Hown' & HIp)".
    iDestruct "HIp" as (p'') "[Hm Hp']".
    iInv "IH" as "Hctx".
    wp_xchg.
    iDestruct (iProto_own_le with "Hown Hle") as "Hown".
    iMod (iProto_step with "Hctx Hown' Hown Hm") as
      (p''') "(Hm & Hctx & Hown & Hown')".
    iModIntro.
    iSplitL "Hctx"; [done|].
    iModIntro.
    iSplitL "Hl' Hown Hp'".
    { iRight. iRight. iExists _. iFrame. }
    wp_pure _.
    rewrite iMsg_base_eq.
    iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
    wp_pures.
    iMod (own_update_2 with "H● H◯") as "[H● H◯]";[apply excl_auth_update|].
    iModIntro. iApply "HΦ".
    iFrame. iExists _, _, _, _, _, _. iSplit; [done|].
    iRewrite "Hp". iFrame "#∗". iApply iProto_le_refl.
  Qed.

  Lemma iProto_le_select_l {TT1 TT2:tele} j
        (v1 : TT1 → val) (v2 : TT2 → val) P1 P2 (p1 : TT1 → iProto Σ) (p2 : TT2 → iProto Σ) :
    ⊢ (iProto_choice (Send, j) v1 v2 P1 P2 p1 p2) ⊑
      (<(Send,j) @.. (tt:TT1)> MSG (InjLV (v1 tt)) {{ P1 tt }} ; p1 tt).
  Proof.
    rewrite /iProto_choice.
    iApply iProto_le_trans; last first.
    { iApply iProto_le_texist_elim_r. iIntros (x). iExists x.
      iApply iProto_le_refl. }
    iIntros (tt). by iExists (inl tt).
  Qed.

  Lemma iProto_le_select_r {TT1 TT2:tele} j
        (v1 : TT1 → val) (v2 : TT2 → val) P1 P2 (p1 : TT1 → iProto Σ) (p2 : TT2 → iProto Σ) :
    ⊢ (iProto_choice (Send, j) v1 v2 P1 P2 p1 p2) ⊑
      (<(Send,j) @.. (tt:TT2)> MSG (InjRV (v2 tt)) {{ P2 tt }} ; p2 tt).
  Proof.
    rewrite /iProto_choice.
    iApply iProto_le_trans; last first.
    { iApply iProto_le_texist_elim_r. iIntros (x). iExists x.
      iApply iProto_le_refl. }
    iIntros (tt). by iExists (inr tt).
  Qed.

End channel.
