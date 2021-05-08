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
From iris.heap_lang Require Export primitive_laws notation.
From iris.heap_lang Require Export proofmode.
From iris.heap_lang.lib Require Import spin_lock.
From actris.channel Require Export proto.
From actris.utils Require Import llist skip.
Set Default Proof Using "Type".

(** * The definition of the message-passing connectives *)
Definition new_chan : val :=
  λ: <>,
     let: "l" := lnil #() in
     let: "r" := lnil #() in
     let: "lk" := newlock #() in
     ((("l","r"),"lk"), (("r","l"),"lk")).

Definition start_chan : val := λ: "f",
  let: "cc" := new_chan #() in
  Fork ("f" (Snd "cc"));; Fst "cc".

Definition send : val :=
  λ: "c" "v",
    let: "lk" := Snd "c" in
    let: "l" := Fst (Fst "c") in
    let: "r" := Snd (Fst "c") in
    acquire "lk";;
    lsnoc "l" "v";;
    skipN (llength "r");; (* "Ghost" operation for later stripping *)
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
  chanG_protoG :> protoG Σ val;
}.
Definition chanΣ : gFunctors := #[ lockΣ; protoΣ val ].
Instance subG_chanΣ {Σ} : subG chanΣ Σ → chanG Σ.
Proof. solve_inG. Qed.

Record chan_name := ChanName {
  chan_lock_name : gname;
  chan_proto_name : proto_name;
}.
Instance chan_name_inhabited : Inhabited chan_name :=
  populate (ChanName inhabitant inhabitant).
Instance chan_name_eq_dec : EqDecision chan_name.
Proof. solve_decision. Qed.
Instance chan_name_countable : Countable chan_name.
Proof.
 refine (inj_countable (λ '(ChanName γl γr), (γl,γr))
   (λ '(γl, γr), Some (ChanName γl γr)) _); by intros [].
Qed.

(** * Definition of the mapsto connective *)
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Definition metaN := nroot .@ "iProto_meta".

Definition iProto_mapsto_def `{!heapGS Σ, !chanG Σ}
    (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γ s (l r : loc) (lk : val),
    ⌜ c = ((#(side_elim s l r), #(side_elim s r l)), lk)%V ⌝ ∗
    meta (side_elim s l r) metaN (γ,s) ∗
    meta (side_elim s r l) metaN (γ,side_elim s Right Left) ∗
    is_lock (chan_lock_name γ) lk (∃ vsl vsr,
      llist internal_eq l vsl ∗
      llist internal_eq r vsr ∗
      iProto_ctx (chan_proto_name γ) vsl vsr) ∗
    iProto_own (chan_proto_name γ) s p.
Definition iProto_mapsto_aux : seal (@iProto_mapsto_def). by eexists. Qed.
Definition iProto_mapsto := iProto_mapsto_aux.(unseal).
Definition iProto_mapsto_eq :
  @iProto_mapsto = @iProto_mapsto_def := iProto_mapsto_aux.(seal_eq).
Arguments iProto_mapsto {_ _ _} _ _%proto.
Instance: Params (@iProto_mapsto) 4 := {}.
Notation "c ↣ p" := (iProto_mapsto c p)
  (at level 20, format "c  ↣  p").

Instance iProto_mapsto_contractive `{!heapGS Σ, !chanG Σ} c :
  Contractive (iProto_mapsto c).
Proof. rewrite iProto_mapsto_eq. solve_contractive. Qed.

Definition iProto_choice {Σ} (a : action) (P1 P2 : iProp Σ)
    (p1 p2 : iProto Σ) : iProto Σ :=
  (<a @ (b : bool)> MSG #b {{ if b then P1 else P2 }}; if b then p1 else p2)%proto.
Typeclasses Opaque iProto_choice.
Arguments iProto_choice {_} _ _%I _%I _%proto _%proto.
Instance: Params (@iProto_choice) 2 := {}.
Infix "<{ P1 }+{ P2 }>" := (iProto_choice Send P1 P2) (at level 85) : proto_scope.
Infix "<{ P1 }&{ P2 }>" := (iProto_choice Recv P1 P2) (at level 85) : proto_scope.
Infix "<+{ P2 }>" := (iProto_choice Send True P2) (at level 85) : proto_scope.
Infix "<&{ P2 }>" := (iProto_choice Recv True P2) (at level 85) : proto_scope.
Infix "<{ P1 }+>" := (iProto_choice Send P1 True) (at level 85) : proto_scope.
Infix "<{ P1 }&>" := (iProto_choice Recv P1 True) (at level 85) : proto_scope.
Infix "<+>" := (iProto_choice Send True True) (at level 85) : proto_scope.
Infix "<&>" := (iProto_choice Recv True True) (at level 85) : proto_scope.

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
    rewrite iProto_mapsto_eq. iDestruct 1 as (γ s l r lk ->) "(Hm1 & Hm2 & Hlk & H)".
    iIntros "Hle'". iExists γ, s, l, r, lk. iSplit; [done|]. iFrame "Hm1 Hm2 Hlk".
    by iApply (iProto_own_le with "H").
  Qed.

  Global Instance iProto_choice_contractive n a :
    Proper (dist n ==> dist n ==>
            dist_later n ==> dist_later n ==> dist n) (@iProto_choice Σ a).
  Proof. solve_contractive. Qed.
  Global Instance iProto_choice_ne n a :
    Proper (dist n ==> dist n ==> dist n ==> dist n ==> dist n) (@iProto_choice Σ a).
  Proof. solve_proper. Qed.
  Global Instance iProto_choice_proper a :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (@iProto_choice Σ a).
  Proof. solve_proper. Qed.

  Lemma iProto_choice_equiv a1 a2 (P11 P12 P21 P22 : iProp Σ)
        (p11 p12 p21 p22 : iProto Σ) :
    ⌜a1 = a2⌝ -∗ ((P11 ≡ P12):iProp Σ) -∗ (P21 ≡ P22) -∗
    ▷ (p11 ≡ p12) -∗ ▷ (p21 ≡ p22) -∗
    iProto_choice a1 P11 P21 p11 p21 ≡ iProto_choice a2 P12 P22 p12 p22.
  Proof.
    iIntros (->) "#HP1 #HP2 #Hp1 #Hp2".
    rewrite /iProto_choice. iApply iProto_message_equiv; [ eauto | | ].
    - iIntros "!>" (b) "H". iExists b. iSplit; [ done | ].
      destruct b;
        [ iRewrite -"HP1"; iFrame "H Hp1" | iRewrite -"HP2"; iFrame "H Hp2" ].
    - iIntros "!>" (b) "H". iExists b. iSplit; [ done | ].
      destruct b;
        [ iRewrite "HP1"; iFrame "H Hp1" | iRewrite "HP2"; iFrame "H Hp2" ].
  Qed.

  Lemma iProto_dual_choice a P1 P2 p1 p2 :
    iProto_dual (iProto_choice a P1 P2 p1 p2)
    ≡ iProto_choice (action_dual a) P1 P2 (iProto_dual p1) (iProto_dual p2).
  Proof.
    rewrite /iProto_choice iProto_dual_message /= iMsg_dual_exist.
    f_equiv; f_equiv=> -[]; by rewrite iMsg_dual_base.
  Qed.

  Lemma iProto_app_choice a P1 P2 p1 p2 q :
    (iProto_choice a P1 P2 p1 p2 <++> q)%proto
    ≡ (iProto_choice a P1 P2 (p1 <++> q) (p2 <++> q))%proto.
  Proof.
    rewrite /iProto_choice iProto_app_message /= iMsg_app_exist.
    f_equiv; f_equiv=> -[]; by rewrite iMsg_app_base.
  Qed.

  Lemma iProto_le_choice a P1 P2 p1 p2 p1' p2' :
    (P1 -∗ P1 ∗ ▷ (p1 ⊑ p1')) ∧ (P2 -∗ P2 ∗ ▷ (p2 ⊑ p2')) -∗
    iProto_choice a P1 P2 p1 p2 ⊑ iProto_choice a P1 P2 p1' p2'.
  Proof.
    iIntros "H". rewrite /iProto_choice. destruct a;
      iIntros (b) "HP"; iExists b; destruct b;
      iDestruct ("H" with "HP") as "[$ ?]"; by iModIntro.
  Qed.

  (** ** Specifications of [send] and [recv] *)
  Lemma new_chan_spec p :
    {{{ True }}}
      new_chan #()
    {{{ c1 c2, RET (c1,c2); c1 ↣ p ∗ c2 ↣ iProto_dual p }}}.
  Proof.
    iIntros (Φ _) "HΦ". wp_lam.
    wp_smart_apply (lnil_spec' internal_eq with "[//]"); iIntros (l) "[Hl Hmetal]".
    wp_smart_apply (lnil_spec' internal_eq with "[//]"); iIntros (r) "[Hr Hmetar]".
    iMod (iProto_init p) as (γp) "(Hctx & Hcl & Hcr)".
    wp_smart_apply (newlock_spec (∃ vsl vsr,
      llist internal_eq l vsl ∗ llist internal_eq r vsr ∗
      iProto_ctx γp vsl vsr) with "[Hl Hr Hctx]").
    { iExists [], []. iFrame. }
    iIntros (lk γlk) "#Hlk". wp_pures. iApply "HΦ".
    set (γ := ChanName γlk γp).
    iMod (meta_set _ l (γ,Left) metaN with "Hmetal") as "#Hmetal".
    { solve_ndisj. }
    iMod (meta_set _ r (γ,Right) metaN with "Hmetar") as "#Hmetar".
    { solve_ndisj. }
    iSplitL "Hcl".
    - rewrite iProto_mapsto_eq. iExists γ, Left, l, r, lk. by iFrame "Hcl #".
    - rewrite iProto_mapsto_eq. iExists γ, Right, l, r, lk. simpl. by iFrame "Hcr #".
  Qed.

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

  Lemma send_spec_atomic c v E Φ :
    □ (|={⊤,E}=> ∃ (p : iProto Σ), (▷ c ↣ <!> MSG v; p) ∗
       (((▷ c ↣ <!> MSG v; p) ={E,⊤}=∗ True)
       ∧  (▷ c ↣ p ={E,⊤}=∗ Φ #()))) -∗
    WP (send c v) {{ Φ }}.
  Proof.
    iIntros "#Hview".
    rewrite iProto_mapsto_eq.
    wp_lam; wp_pures. wp_bind (Snd _).
    iPoseProof "Hview" as "Hview1".
    iMod "Hview1" as (P) "[Hc Hview1]".
    iDestruct "Hview1" as "[Hview1 _]".
    iDestruct "Hc" as (γ s l r lk) "(>% & #Hmeta1 & #Hmeta2 & #Hlk & H)".
    simplify_eq/=. wp_pures.
    iMod ("Hview1" with "[-]") as "_".
    { iExists _,_,_,_,_. iFrame "Hlk H". eauto with iFrame. }
    clear P. iModIntro. wp_pures.
    wp_smart_apply (acquire_spec with "Hlk"); iIntros "[Hlkd Hinv]".
    iDestruct "Hinv" as (vsl vsr) "(Hl & Hr & Hctx)".
    wp_bind (Lam _ _).
    iMod "Hview" as (P) "[Hc Hview]".
    iDestruct "Hc" as (γ' s' l' r' lk') "(>%Hc & #>Hmeta1' & #>Hmeta2' & #Hlk' & H)".
    iAssert (⌜(γ,s) = (γ',s')⌝)%I as %Hfoo.
    { destruct s, s'; simplify_eq/=; iApply meta_agree; eauto with iFrame. }
    iClear "Hmeta1' Hmeta2' Hlk'". symmetry in Hfoo. simplify_eq/=.
    iDestruct "Hview" as "[_ Hview]".
    wp_pures. destruct s; simpl.
    - iMod (iProto_send_l with "Hctx H []") as "[Hctx H]".
      { rewrite iMsg_base_eq /=; auto. }
      iMod ("Hview" with "[H]") as "HΦ".
      { iExists _,_,_,_,_. iFrame "Hlk H". eauto with iFrame. }
      iModIntro.
      wp_smart_apply (lsnoc_spec with "[$Hl //]"); iIntros "Hl".
      wp_smart_apply (llength_spec with "[$Hr //]"); iIntros "Hr".
      wp_smart_apply skipN_spec.
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      by iIntros "_".
    - iMod (iProto_send_r with "Hctx H []") as "[Hctx H]".
      { rewrite iMsg_base_eq /=; auto. }
      iMod ("Hview" with "[H]") as "HΦ".
      { iExists _,_,_,_,_. iFrame "Hlk H". eauto with iFrame. }
      iModIntro.
      wp_smart_apply (lsnoc_spec with "[$Hr //]"); iIntros "Hr".
      wp_smart_apply (llength_spec with "[$Hl //]"); iIntros "Hl".
      wp_smart_apply skipN_spec.
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      by iIntros "_".
  Qed.

  Lemma try_recv_spec_atomic {X} c (v : X → val) (P : X → iProp Σ) (p : iProto Σ) E Φ
        `{!Inhabited X} :
    □ (|={⊤,E}=> ∃ q, (▷ c ↣ <? (x : X)> MSG v x {{ P x }}; q) ∗ (▷ ▷ (p ≡ q)) ∗
            ((▷ c ↣ <? x> MSG v x {{ P x }}; q) ={E,⊤}=∗ Φ NONEV)
          ∧ (∀ x q, ▷ ((c ↣ q) ∗ P x ∗ ▷ (p ≡ q)) ={E,⊤}=∗ Φ (SOMEV (v x)))) -∗
    WP try_recv c {{ v, Φ v }}.
  Proof.
    iIntros "#Hview".
    rewrite iProto_mapsto_eq.
    wp_lam; wp_pures. wp_bind (Snd _).
    iPoseProof "Hview" as "Hview1".
    iMod "Hview1" as (q) "(Hc & Heq & Hview1)".
    iDestruct "Hview1" as "[Hview1 _]".
    iDestruct "Hc" as (γ s l r lk) "(>% & #Hmeta1 & #Hmeta2 & #Hlk & H)".
    simplify_eq/=. wp_pures.
    iMod ("Hview1" with "[-]") as "_".
    { iExists _,_,_,_,_. iNext. iFrame "Hlk H". eauto with iFrame. }
    clear q. iModIntro. wp_pures.
    wp_smart_apply (acquire_spec with "Hlk"); iIntros "[Hlkd Hinv]".
    iDestruct "Hinv" as (vsl vsr) "(Hl & Hr & Hctx)".
    wp_pures. destruct s; simpl.
    - wp_smart_apply (lisnil_spec with "Hr"); iIntros "Hr".
      destruct vsr as [|vr vsr]; wp_pures.
      { wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
        iIntros "_". iApply wp_fupd. wp_pures.
        iMod "Hview" as (q) "(Hc & Heq & Hview)".
        iDestruct "Hc" as (γ' s' l' r' lk') "(>%Hc & #>Hmeta1' & #>Hmeta2' & #Hlk' & H)".
        iAssert (⌜(γ,Left) = (γ',s')⌝)%I as %Hfoo.
        { simplify_eq/=; iApply meta_agree; eauto with iFrame. }
        iClear "Hmeta1' Hmeta2' Hlk'". symmetry in Hfoo. simplify_eq/=.
        iDestruct "Hview" as "[Hview _]".
        iApply "Hview". iNext.
        iExists γ, Left, l', r', lk'. eauto 10 with iFrame. }
      wp_smart_apply (lpop_spec with "Hr"); iIntros (v') "[% Hr]"; simplify_eq/=.
      wp_bind (InjR _).
      iMod "Hview" as (q) "(Hc & Heq & Hview)".
      iDestruct "Hc" as (γ' s' l' r' lk') "(>%Hc & #>Hmeta1' & #>Hmeta2' & #Hlk' & H)".
      iAssert (⌜(γ,Left) = (γ',s')⌝)%I as %Hfoo.
      { simplify_eq/=; iApply meta_agree; eauto with iFrame. }
      iClear "Hmeta1' Hmeta2' Hlk'". symmetry in Hfoo. simplify_eq/=.
      iDestruct "Hview" as "[_ Hview]".
      rewrite iProto_recv_l.
      iSpecialize ("Hctx" with "H").
      rewrite iMsg_base_eq.
      wp_pures. iMod "Hctx" as (q') "(Hctx & H & Hm) /=".
      rewrite iMsg_exist_eq /=.
      iDestruct "Hm" as (x) "(>%foo & Hp & HP)".
      iMod ("Hview" with "[H Hp HP Heq]") as "HΦ".
      { iNext. iFrame "HP". iSplitL "H".
        - iExists γ, Left, l', r', lk'. iFrame "Hlk Hmeta1 Hmeta2 H".
          eauto with iFrame.
        - iNext. by iRewrite "Heq". }
      iModIntro. wp_pures.
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". wp_pures. iModIntro. by rewrite foo.
    - wp_smart_apply (lisnil_spec with "Hl"); iIntros "Hl".
      destruct vsl as [|vl vsl]; wp_pures.
      { wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
        iIntros "_". iApply wp_fupd. wp_pures.
        iMod "Hview" as (q) "(Hc & Heq & Hview)".
        iDestruct "Hc" as (γ' s' l' r' lk') "(>%Hc & #>Hmeta1' & #>Hmeta2' & #Hlk' & H)".
        iAssert (⌜(γ,Right) = (γ',s')⌝)%I as %Hfoo.
        { simplify_eq/=; iApply meta_agree; eauto with iFrame. }
        iClear "Hmeta1' Hmeta2' Hlk'". symmetry in Hfoo. simplify_eq/=.
        iDestruct "Hview" as "[Hview _]".
        iApply "Hview". iNext.
        iExists γ, Right, l', r', lk'. eauto 10 with iFrame. }
      wp_smart_apply (lpop_spec with "Hl"); iIntros (v') "[% Hl]"; simplify_eq/=.
      wp_bind (InjR _).
      iMod "Hview" as (q) "(Hc & Heq & Hview)".
      iDestruct "Hc" as (γ' s' l' r' lk') "(>%Hc & #>Hmeta1' & #>Hmeta2' & #Hlk' & H)".
      iAssert (⌜(γ,Right) = (γ',s')⌝)%I as %Hfoo.
      { simplify_eq/=; iApply meta_agree; eauto with iFrame. }
      iClear "Hmeta1' Hmeta2' Hlk'". symmetry in Hfoo. simplify_eq/=.
      iDestruct "Hview" as "[_ Hview]".
      rewrite iProto_recv_r.
      iSpecialize ("Hctx" with "H").
      rewrite iMsg_base_eq.
      wp_pures. iMod "Hctx" as (q') "(Hctx & H & Hm) /=".
      rewrite iMsg_exist_eq /=.
      iDestruct "Hm" as (x) "(>%foo & Hp & HP)".
      iMod ("Hview" with "[H Hp HP Heq]") as "HΦ".
      { iNext. iFrame "HP". iSplitL "H".
        - iExists γ, Right, l', r', lk'. iFrame "Hlk Hmeta1 Hmeta2 H".
          eauto with iFrame.
        - iNext. by iRewrite "Heq". }
      iModIntro. wp_pures.
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". wp_pures. iModIntro. by rewrite foo.
  Qed.

  Lemma recv_spec_atomic {X} c (v : X → val) (P : X → iProp Σ) (p : iProto Σ) E Φ
        `{!Inhabited X} :
    □ (|={⊤,E}=> ∃ q, (▷ c ↣ <? (x : X)> MSG v x {{ P x }}; q) ∗ (▷ ▷ (p ≡ q)) ∗
            ((▷ c ↣ <? x> MSG v x {{ P x }}; q) ={E,⊤}=∗ True)
          ∧ (∀ x q, ▷ ((c ↣ q) ∗ P x ∗ ▷ (p ≡ q)) ={E,⊤}=∗ Φ (v x))) -∗
    WP recv c {{ Φ }}.
  Proof.
    iIntros "#H". iLöb as "IH". wp_lam. wp_bind (try_recv c).
    iApply (@try_recv_spec_atomic X). iModIntro.
    iMod "H" as (q) "(Hc & Heq & Hview)". iModIntro.
    iExists q. iFrame "Hc Heq". iSplit.
    - iIntros "Hc". iDestruct "Hview" as "[Hview _]".
      iMod ("Hview" with "Hc") as "_". iModIntro.
      by wp_pures.
    - iIntros (x q') "Hc". iDestruct "Hview" as "[_ Hview]".
      iMod ("Hview" with "Hc") as "HΦ". iModIntro.
      by wp_pures.
  Qed.

  Lemma send_spec c v p :
    {{{ c ↣ <!> MSG v; p }}}
      send c v
    {{{ RET #(); c ↣ p }}}.
  Proof.
    rewrite iProto_mapsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (γ s l r lk ->) "(#Hmeta1 & #Hmeta2 & #Hlk & H)"; wp_pures.
    wp_smart_apply (acquire_spec with "Hlk"); iIntros "[Hlkd Hinv]".
    iDestruct "Hinv" as (vsl vsr) "(Hl & Hr & Hctx)". destruct s; simpl.
    - iMod (iProto_send_l with "Hctx H []") as "[Hctx H]".
      { rewrite iMsg_base_eq /=; auto. }
      wp_smart_apply (lsnoc_spec with "[$Hl //]"); iIntros "Hl".
      wp_smart_apply (llength_spec with "[$Hr //]"); iIntros "Hr".
      wp_smart_apply skipN_spec.
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". iApply "HΦ". iExists γ, Left, l, r, lk. eauto 10 with iFrame.
    - iMod (iProto_send_r with "Hctx H []") as "[Hctx H]".
      { rewrite iMsg_base_eq /=; auto. }
      wp_smart_apply (lsnoc_spec with "[$Hr //]"); iIntros "Hr".
      wp_smart_apply (llength_spec with "[$Hl //]"); iIntros "Hl".
      wp_smart_apply skipN_spec.
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". iApply "HΦ". iExists γ, Right, l, r, lk. eauto 10 with iFrame.
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

  Lemma try_recv_spec {TT} c (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ <?.. x> MSG v x {{ P x }}; p x }}}
      try_recv c
    {{{ w, RET w; (⌜w = NONEV⌝ ∗ c ↣ <?.. x> MSG v x {{ P x }}; p x) ∨
                  (∃.. x, ⌜w = SOMEV (v x)⌝ ∗ c ↣ p x ∗ P x) }}}.
  Proof.
    rewrite iProto_mapsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (γ s l r lk ->) "(Hmeta1 & Hmeta2 & #Hlk & H)"; wp_pures.
    wp_smart_apply (acquire_spec with "Hlk"); iIntros "[Hlkd Hinv]".
    iDestruct "Hinv" as (vsl vsr) "(Hl & Hr & Hctx)". destruct s; simpl.
    - wp_smart_apply (lisnil_spec with "Hr"); iIntros "Hr".
      destruct vsr as [|vr vsr]; wp_pures.
      { wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
        iIntros "_". wp_pures. iModIntro. iApply "HΦ". iLeft. iSplit; [done|].
        iExists γ, Left, l, r, lk. eauto 10 with iFrame. }
      wp_smart_apply (lpop_spec with "Hr"); iIntros (v') "[% Hr]"; simplify_eq/=.
      iMod (iProto_recv_l with "Hctx H") as (q) "(Hctx & H & Hm)". wp_pures.
      rewrite iMsg_base_eq.
      iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". wp_pures. iModIntro. iApply "HΦ". iRight. iExists x. iSplit; [done|].
      iFrame "HP". iExists γ, Left, l, r, lk. iSplit; [done|]. iFrame "Hlk".
      iFrame "Hmeta1 Hmeta2". by iRewrite "Hp".
    - wp_smart_apply (lisnil_spec with "Hl"); iIntros "Hl".
      destruct vsl as [|vl vsl]; wp_pures.
      { wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
        iIntros "_". wp_pures. iModIntro. iApply "HΦ". iLeft. iSplit; [done|].
        iExists γ, Right, l, r, lk. eauto 10 with iFrame. }
      wp_smart_apply (lpop_spec with "Hl"); iIntros (v') "[% Hl]"; simplify_eq/=.
      iMod (iProto_recv_r with "Hctx H") as (q) "(Hctx & H & Hm)". wp_pures.
      rewrite iMsg_base_eq.
      iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". wp_pures. iModIntro. iApply "HΦ". iRight. iExists x. iSplit; [done|].
      iFrame "HP". iExists γ, Right, l, r, lk. iSplit; [done|]. iFrame "Hlk Hmeta1 Hmeta2".
      by iRewrite "Hp".
  Qed.

  Lemma recv_spec {TT} c (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ <?.. x> MSG v x {{ ▷ P x }}; p x }}}
      recv c
    {{{ x, RET v x; c ↣ p x ∗ P x }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iLöb as "IH". wp_lam.
    wp_smart_apply (try_recv_spec with "Hc"); iIntros (w) "[[-> H]|H]".
    { wp_pures. by iApply ("IH" with "[$]"). }
    iDestruct "H" as (x ->) "[Hc HP]". wp_pures. iApply "HΦ". by iFrame.
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
