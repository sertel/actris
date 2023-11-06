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

Local Existing Instance spin_lock.

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
  chanG_lockG :: lockG Σ;
  chanG_protoG :: protoG Σ val;
}.
Definition chanΣ : gFunctors := #[ spin_lockΣ; protoΣ val ].
Global Instance subG_chanΣ {Σ} : subG chanΣ Σ → chanG Σ.
Proof. solve_inG. Qed.

Record chan_name := ChanName {
  chan_lock_name : gname;
  chan_proto_name : proto_name;
}.
Global Instance chan_name_inhabited : Inhabited chan_name :=
  populate (ChanName inhabitant inhabitant).
Global Instance chan_name_eq_dec : EqDecision chan_name.
Proof. solve_decision. Qed.
Global Instance chan_name_countable : Countable chan_name.
Proof.
 refine (inj_countable (λ '(ChanName γl γr), (γl,γr))
   (λ '(γl, γr), Some (ChanName γl γr)) _); by intros [].
Qed.

(** * Definition of the pointsto connective *)
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Definition iProto_pointsto_def `{!heapGS Σ, !chanG Σ}
    (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γ s (l r : loc) (lk : val),
    ⌜ c = ((#(side_elim s l r), #(side_elim s r l)), lk)%V ⌝ ∗
    is_lock (chan_lock_name γ) lk (∃ vsl vsr,
      llist internal_eq l vsl ∗
      llist internal_eq r vsr ∗
      steps_lb (length vsl) ∗ steps_lb (length vsr) ∗
      iProto_ctx (chan_proto_name γ) vsl vsr) ∗
    iProto_own (chan_proto_name γ) s p.
Definition iProto_pointsto_aux : seal (@iProto_pointsto_def). by eexists. Qed.
Definition iProto_pointsto := iProto_pointsto_aux.(unseal).
Definition iProto_pointsto_eq :
  @iProto_pointsto = @iProto_pointsto_def := iProto_pointsto_aux.(seal_eq).
Arguments iProto_pointsto {_ _ _} _ _%proto.
Global Instance: Params (@iProto_pointsto) 4 := {}.
Notation "c ↣ p" := (iProto_pointsto c p)
  (at level 20, format "c  ↣  p").

Global Instance iProto_pointsto_contractive `{!heapGS Σ, !chanG Σ} c :
  Contractive (iProto_pointsto c).
Proof. rewrite iProto_pointsto_eq. solve_contractive. Qed.

Definition iProto_choice {Σ} (a : action) (P1 P2 : iProp Σ)
    (p1 p2 : iProto Σ) : iProto Σ :=
  (<a @ (b : bool)> MSG #b {{ if b then P1 else P2 }}; if b then p1 else p2)%proto.
Global Typeclasses Opaque iProto_choice.
Arguments iProto_choice {_} _ _%I _%I _%proto _%proto.
Global Instance: Params (@iProto_choice) 2 := {}.
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

  Global Instance iProto_pointsto_ne c : NonExpansive (iProto_pointsto c).
  Proof. rewrite iProto_pointsto_eq. solve_proper. Qed.
  Global Instance iProto_pointsto_proper c : Proper ((≡) ==> (≡)) (iProto_pointsto c).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_pointsto_le c p1 p2 : c ↣ p1 ⊢ ▷ (p1 ⊑ p2) -∗ c ↣ p2.
  Proof.
    rewrite iProto_pointsto_eq. iDestruct 1 as (γ s l r lk ->) "[Hlk H]".
    iIntros "Hle'". iExists γ, s, l, r, lk. iSplit; [done|]. iFrame "Hlk".
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
    wp_bind (lnil _).
    iApply wp_lb_init; iIntros "#Hlb".
    wp_smart_apply (lnil_spec internal_eq with "[//]"); iIntros (l) "Hl".
    wp_smart_apply (lnil_spec internal_eq with "[//]"); iIntros (r) "Hr".
    iMod (iProto_init p) as (γp) "(Hctx & Hcl & Hcr)".
    wp_smart_apply (newlock_spec (∃ vsl vsr,
      llist internal_eq l vsl ∗ llist internal_eq r vsr ∗
      steps_lb (length vsl) ∗ steps_lb (length vsr) ∗
      iProto_ctx γp vsl vsr) with "[Hl Hr Hctx]").
    { iExists [], []. iFrame "#∗". }
    iIntros (lk γlk) "#Hlk". wp_pures. iApply "HΦ".
    set (γ := ChanName γlk γp). iSplitL "Hcl".
    - rewrite iProto_pointsto_eq. iExists γ, Left, l, r, lk. by iFrame "Hcl #".
    - rewrite iProto_pointsto_eq. iExists γ, Right, l, r, lk. by iFrame "Hcr #".
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

  Lemma send_spec c v p :
    {{{ c ↣ <!> MSG v; p }}}
      send c v
    {{{ RET #(); c ↣ p }}}.
  Proof.
    rewrite iProto_pointsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (γ s l r lk ->) "[#Hlk H]"; wp_pures.
    wp_smart_apply (acquire_spec with "Hlk"); iIntros "[Hlkd Hinv]".
    iDestruct "Hinv" as (vsl vsr) "(Hl & Hr & #Hlbl & #Hlbr & Hctx)".
    destruct s; simpl.
    - wp_pures. wp_bind (lsnoc _ _).
      iApply (wp_step_fupdN_lb with "Hlbr [Hctx H]"); [done| |].
      { iApply fupd_mask_intro; [set_solver|]. simpl.
        iIntros "Hclose !>!>".
        iMod (iProto_send_l with "Hctx H []") as "[Hctx H]".
        { rewrite iMsg_base_eq /=; auto. }
        iModIntro.
        iApply step_fupdN_intro; [done|].
        iIntros "!>". iMod "Hclose".
        iCombine ("Hctx H") as "H".
        iExact "H". }
      iApply (wp_lb_update with "Hlbl").
      wp_smart_apply (lsnoc_spec with "[$Hl //]"); iIntros "Hl".
      iIntros "#Hlbl' [Hctx H] !>".
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]").
      { iExists (vsl ++ [v]), vsr.
        rewrite app_length /=.
        replace (length vsl + 1) with (S (length vsl)) by lia.
        iFrame "#∗". }
      iIntros "_". iApply "HΦ". iExists γ, Left, l, r, lk. eauto 10 with iFrame.
    - wp_pures. wp_bind (lsnoc _ _).
      iApply (wp_step_fupdN_lb with "Hlbl [Hctx H]"); [done| |].
      { iApply fupd_mask_intro; [set_solver|]. simpl.
        iIntros "Hclose !>!>".
        iMod (iProto_send_r with "Hctx H []") as "[Hctx H]".
        { rewrite iMsg_base_eq /=; auto. }
        iModIntro.
        iApply step_fupdN_intro; [done|].
        iIntros "!>". iMod "Hclose".
        iCombine ("Hctx H") as "H".
        iExact "H". }
      iApply (wp_lb_update with "Hlbr").
      wp_smart_apply (lsnoc_spec with "[$Hr //]"); iIntros "Hr".
      iIntros "#Hlbr' [Hctx H] !>".
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]").
      { iExists vsl, (vsr ++ [v]).
        rewrite app_length /=.
        replace (length vsr + 1) with (S (length vsr)) by lia.
        iFrame "#∗". }
      iIntros "_". iApply "HΦ". iExists γ, Right, l, r, lk. eauto 10 with iFrame.
  Qed.

  Lemma send_spec_tele {TT} c (tt : TT)
        (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ (<!.. x > MSG v x {{ P x }}; p x) ∗ P tt }}}
      send c (v tt)
    {{{ RET #(); c ↣ (p tt) }}}.
  Proof.
    iIntros (Φ) "[Hc HP] HΦ".
    iDestruct (iProto_pointsto_le _ _ (<!> MSG v tt; p tt)%proto with "Hc [HP]")
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
    rewrite iProto_pointsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (γ s l r lk ->) "[#Hlk H]"; wp_pures.
    wp_smart_apply (acquire_spec with "Hlk"); iIntros "[Hlkd Hinv]".
    iDestruct "Hinv" as (vsl vsr) "(Hl & Hr & #Hlbl & #Hlbr & Hctx)". destruct s; simpl.
    - wp_smart_apply (lisnil_spec with "Hr"); iIntros "Hr".
      destruct vsr as [|vr vsr]; wp_pures.
      { wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
        iIntros "_". wp_pures. iModIntro. iApply "HΦ". iLeft. iSplit; [done|].
        iExists γ, Left, l, r, lk. eauto 10 with iFrame. }
      wp_smart_apply (lpop_spec with "Hr"); iIntros (v') "[% Hr]"; simplify_eq/=.
      iMod (iProto_recv_l with "Hctx H") as (q) "(Hctx & H & Hm)". wp_pures.
      rewrite iMsg_base_eq.
      iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
      iDestruct (steps_lb_le _ (length vsr) with "Hlbr") as "#Hlbr'"; [lia|].
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". wp_pures. iModIntro. iApply "HΦ". iRight. iExists x. iSplit; [done|].
      iFrame "HP". iExists γ, Left, l, r, lk. iSplit; [done|]. iFrame "Hlk".
      by iRewrite "Hp".
    - wp_smart_apply (lisnil_spec with "Hl"); iIntros "Hl".
      destruct vsl as [|vl vsl]; wp_pures.
      { wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
        iIntros "_". wp_pures. iModIntro. iApply "HΦ". iLeft. iSplit; [done|].
        iExists γ, Right, l, r, lk. eauto 10 with iFrame. }
      wp_smart_apply (lpop_spec with "Hl"); iIntros (v') "[% Hl]"; simplify_eq/=.
      iMod (iProto_recv_r with "Hctx H") as (q) "(Hctx & H & Hm)". wp_pures.
      rewrite iMsg_base_eq.
      iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
      iDestruct (steps_lb_le _ (length vsl) with "Hlbl") as "#Hlbl'"; [lia|].
      wp_smart_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". wp_pures. iModIntro. iApply "HΦ". iRight. iExists x. iSplit; [done|].
      iFrame "HP". iExists γ, Right, l, r, lk. iSplit; [done|]. iFrame "Hlk".
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
    iApply (iProto_pointsto_le with "Hc").
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
    { iApply (iProto_pointsto_le with "Hc").
      iIntros "!> /=" (b) "HP". iExists b. by iSplitL. }
    rewrite -bi_tforall_forall.
    iIntros "!>" (x) "[Hc H]". iApply "HΦ". iFrame.
  Qed.
End channel.
