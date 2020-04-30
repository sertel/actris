(** This file contains the definition of the channels, encoded as a pair of
lock-protected buffers, and their primitive proof rules. Moreover:

- It defines the connective [c ↣ prot] for ownership of channel endpoints,
  which describes that channel endpoint [c] adheres to protocol [prot].
- It proves Actris's specifications of [send] and [recv] w.r.t. dependent
  separation protocols.

An encoding of the usual choice connectives [prot1 <{Q1}+{Q2}> prot2] and
[prot1 <{Q1}&{Q2}> prot2], inspired by session types, is also included in this
file.

In this file we define the three message-passing connectives:

- [new_chan] creates references to two empty buffers and a lock, and returns a
  pair of endpoints, where the order of the two references determines the
  polarity of the endpoints.
- [send] takes an endpoint and adds an element to the first buffer.
- [recv] performs a busy loop until there is something in the second buffer,
  which it pops and returns, locking during each peek.*)
From iris.heap_lang Require Export lifting notation.
From iris.heap_lang Require Import proofmode.
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
    acquire "lk";;
    let: "l" := Fst (Fst "c") in
    lsnoc "l" "v";;
    skipN (llength (Snd (Fst "c")));; (* Later stripping *)
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

Definition iProto_mapsto_def `{!heapG Σ, !chanG Σ}
    (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γ s (l r : loc) (lk : val),
    ⌜ c = ((#(side_elim s l r), #(side_elim s r l)), lk)%V ⌝ ∗
    is_lock (chan_lock_name γ) lk (∃ vsl vsr,
      llist sbi_internal_eq l vsl ∗
      llist sbi_internal_eq r vsr ∗
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
  Context `{!heapG Σ, !chanG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Global Instance iProto_mapsto_ne c : NonExpansive (iProto_mapsto c).
  Proof. rewrite iProto_mapsto_eq. solve_proper. Qed.
  Global Instance iProto_mapsto_proper c : Proper ((≡) ==> (≡)) (iProto_mapsto c).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_mapsto_le c p1 p2 : c ↣ p1 -∗ ▷ (p1 ⊑ p2) -∗ c ↣ p2.
  Proof.
    rewrite iProto_mapsto_eq. iDestruct 1 as (γ s l r lk ->) "[Hlk H]".
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
    wp_apply (lnil_spec sbi_internal_eq with "[//]"); iIntros (l) "Hl".
    wp_apply (lnil_spec sbi_internal_eq with "[//]"); iIntros (r) "Hr".
    iMod (iProto_init p) as (γp) "(Hctx & Hcl & Hcr)".
    wp_apply (newlock_spec (∃ vsl vsr,
      llist sbi_internal_eq l vsl ∗ llist sbi_internal_eq r vsr ∗
      iProto_ctx γp vsl vsr) with "[Hl Hr Hctx]").
    { iExists [], []. iFrame. }
    iIntros (lk γlk) "#Hlk". wp_pures. iApply "HΦ".
    set (γ := ChanName γlk γp). iSplitL "Hcl".
    - rewrite iProto_mapsto_eq. iExists γ, Left, l, r, lk. by iFrame "Hcl #".
    - rewrite iProto_mapsto_eq. iExists γ, Right, l, r, lk. by iFrame "Hcr #".
  Qed.

  Lemma start_chan_spec p Φ (f : val) :
    ▷ (∀ c, c ↣ iProto_dual p -∗ WP f c {{ _, True }}) -∗
    ▷ (∀ c, c ↣ p -∗ Φ c) -∗
    WP start_chan f {{ Φ }}.
  Proof.
    iIntros "Hfork HΦ". wp_lam.
    wp_apply (new_chan_spec p with "[//]"); iIntros (c1 c2) "[Hc1 Hc2]".
    wp_apply (wp_fork with "[Hfork Hc2]").
    { iNext. wp_apply ("Hfork" with "Hc2"). }
    wp_pures. iApply ("HΦ" with "Hc1").
  Qed.

  Lemma send_spec c v p :
    {{{ c ↣ <!> MSG v; p }}}
      send c v
    {{{ RET #(); c ↣ p }}}.
  Proof.
    rewrite iProto_mapsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (γ s l r lk ->) "[#Hlk H]"; wp_pures.
    wp_apply (acquire_spec with "Hlk"); iIntros "[Hlkd Hinv]".
    iDestruct "Hinv" as (vsl vsr) "(Hl & Hr & Hctx)". destruct s; simpl.
    - iMod (iProto_send_l with "Hctx H []") as "[Hctx H]".
      { rewrite iMsg_base_eq /=; auto. }
      wp_apply (lsnoc_spec with "[$Hl //]"); iIntros "Hl".
      wp_apply (llength_spec with "[$Hr //]"); iIntros "Hr".
      wp_apply skipN_spec.
      wp_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". iApply "HΦ". iExists γ, Left, l, r, lk. eauto 10 with iFrame.
    - iMod (iProto_send_r with "Hctx H []") as "[Hctx H]".
      { rewrite iMsg_base_eq /=; auto. }
      wp_apply (lsnoc_spec with "[$Hr //]"); iIntros "Hr".
      wp_apply (llength_spec with "[$Hl //]"); iIntros "Hl".
      wp_apply skipN_spec.
      wp_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". iApply "HΦ". iExists γ, Right, l, r, lk. eauto 10 with iFrame.
  Qed.

  Lemma try_recv_spec {TT} c (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ <?.. x> MSG v x {{ ▷ P x }}; p x }}}
      try_recv c
    {{{ w, RET w; (⌜w = NONEV⌝ ∗ c ↣ <?.. x> MSG v x {{ ▷ P x }}; p x) ∨
                  (∃.. x, ⌜w = SOMEV (v x)⌝ ∗ c ↣ p x ∗ P x) }}}.
  Proof.
    assert (∀ w lp (m : TT → iMsg Σ),
      iMsg_car (∃.. x, m x)%msg w lp ⊣⊢ (∃.. x, iMsg_car (m x) w lp)) as iMsg_texist.
    { intros w lp m. clear v P p. rewrite /iMsg_texist iMsg_exist_eq.
      induction TT as [|T TT IH]; simpl; [done|]. f_equiv=> x. apply IH. }
    rewrite iProto_mapsto_eq. iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iDestruct "Hc" as (γ s l r lk ->) "[#Hlk H]"; wp_pures.
    wp_apply (acquire_spec with "Hlk"); iIntros "[Hlkd Hinv]".
    iDestruct "Hinv" as (vsl vsr) "(Hl & Hr & Hctx)". destruct s; simpl.
    - wp_apply (lisnil_spec with "Hr"); iIntros "Hr".
      destruct vsr as [|vr vsr]; wp_pures.
      { wp_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
        iIntros "_". wp_pures. iApply "HΦ". iLeft. iSplit; [done|].
        iExists γ, Left, l, r, lk. eauto 10 with iFrame. }
      wp_apply (lpop_spec with "Hr"); iIntros (v') "[% Hr]"; simplify_eq/=.
      iMod (iProto_recv_l with "Hctx H") as "H". wp_pures.
      iMod "H" as (q) "(Hctx & H & Hm)".
      rewrite iMsg_base_eq. iDestruct (iMsg_texist with "Hm") as (x <-) "[Hp HP]".
      wp_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". wp_pures. iApply "HΦ". iRight. iExists x. iSplit; [done|].
      iFrame "HP". iExists γ, Left, l, r, lk. iSplit; [done|]. iFrame "Hlk".
      by iRewrite "Hp".
    - wp_apply (lisnil_spec with "Hl"); iIntros "Hl".
      destruct vsl as [|vl vsl]; wp_pures.
      { wp_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
        iIntros "_". wp_pures. iApply "HΦ". iLeft. iSplit; [done|].
        iExists γ, Right, l, r, lk. eauto 10 with iFrame. }
      wp_apply (lpop_spec with "Hl"); iIntros (v') "[% Hl]"; simplify_eq/=.
      iMod (iProto_recv_r with "Hctx H") as "H". wp_pures.
      iMod "H" as (q) "(Hctx & H & Hm)".
      rewrite iMsg_base_eq. iDestruct (iMsg_texist with "Hm") as (x <-) "[Hp HP]".
      wp_apply (release_spec with "[Hl Hr Hctx $Hlk $Hlkd]"); [by eauto with iFrame|].
      iIntros "_". wp_pures. iApply "HΦ". iRight. iExists x. iSplit; [done|].
      iFrame "HP". iExists γ, Right, l, r, lk. iSplit; [done|]. iFrame "Hlk".
      by iRewrite "Hp".
  Qed.

  Lemma recv_spec {TT} c (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ <?.. x> MSG v x {{ ▷ P x }}; p x }}}
      recv c
    {{{ x, RET v x; c ↣ p x ∗ P x }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iLöb as "IH". wp_lam.
    wp_apply (try_recv_spec with "Hc"); iIntros (w) "[[-> H]|H]".
    { wp_pures. by iApply ("IH" with "[$]"). }
    iDestruct "H" as (x ->) "[Hc HP]". wp_pures. iApply "HΦ". iFrame.
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
