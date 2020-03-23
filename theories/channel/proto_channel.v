(** This file defines the core of the Actris logic:

- It defines dependent separation protocols and the various operations on it
  like dual, append, and branching.
- It defines the connective [c ↣ prot] for ownership of channel endpoints.
- It proves Actris's specifications of [send] and [receive] w.r.t. dependent
  separation protocols.

Dependent separation protocols are defined by instantiating the parameterized
version in [proto_model] with type of values [val] of HeapLang and the
propositions [iProp] of Iris.

In doing so we define ways of constructing instances of the instantiated type
via two constructors:
- [iProto_end], which is identical to [proto_end].
- [iProto_message], which takes an action and a continuation to construct
  the corresponding message protocols.

For convenience sake, we provide the following notations:
- [END], which is simply [iProto_end].
- [<!> x1 .. xn, MSG v; {{ P }}; prot] and [<?> x1 .. xn, MSG v; {{ P }}; prot],
  which construct an instance of [iProto_message] with the appropriate
  continuation.

Futhermore, we define the following operations:
- [iProto_dual], which turns all [Send] of a protocol into [Recv] and vice-versa
- [iProto_app], which appends two protocols as described in proto_model.v

An encoding of the usual branching connectives [prot1 <{Q1}+{Q2}> prot2] and
[prot1 <{Q1}&{Q2}> prot2], inspired by session types, is also included in this
file.

The logical connective for protocol ownership is denoted as [c ↣ prot]. It
describes that channel endpoint [c] adheres to protocol [prot]. This connective
is modeled using Iris invariants and ghost state along with the logical
connectives of the channel encodings [is_chan] and [chan_own].

Lastly, relevant type classes instances are defined for each of the above
notions, such as contractiveness and non-expansiveness, after which the
specifications of the message-passing primitives are defined in terms of the
protocol connectives. *)
From actris.channel Require Export channel. 
From actris.channel Require Import proto_model.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl_auth.
Export action.

Definition start_chan : val := λ: "f",
  let: "cc" := new_chan #() in
  Fork ("f" (Snd "cc"));; Fst "cc".

(** * Setup of Iris's cameras *)
Class proto_chanG Σ := {
  proto_chanG_chanG :> chanG Σ;
  proto_chanG_authG :> inG Σ (excl_authR (laterO (proto val (iPrePropO Σ) (iPrePropO Σ))));
}.

Definition proto_chanΣ := #[
  chanΣ;
  GFunctor (authRF (optionURF (exclRF (laterOF (protoOF val idOF idOF)))))
].
Instance subG_chanΣ {Σ} : subG proto_chanΣ Σ → proto_chanG Σ.
Proof. intros [??%subG_inG]%subG_inv. constructor; apply _. Qed.

(** * Types *)
Definition iProto Σ := proto val (iPropO Σ) (iPropO Σ).
Delimit Scope proto_scope with proto.
Bind Scope proto_scope with iProto.

(** * Operators *)
Definition iProto_end_def {Σ} : iProto Σ := proto_end.
Definition iProto_end_aux : seal (@iProto_end_def). by eexists. Qed.
Definition iProto_end := iProto_end_aux.(unseal).
Definition iProto_end_eq : @iProto_end = @iProto_end_def := iProto_end_aux.(seal_eq).
Arguments iProto_end {_}.

Program Definition iProto_message_def {Σ} {TT : tele} (a : action)
    (pc : TT → val * iProp Σ * iProto Σ) : iProto Σ :=
  proto_message a (λ v, λne f, ∃ x : TT,
    (** We need the later to make [iProto_message] contractive *)
    ⌜ v = (pc x).1.1 ⌝ ∗
    ▷ (pc x).1.2 ∗
    f (Next (pc x).2))%I.
Next Obligation. solve_proper. Qed.
Definition iProto_message_aux : seal (@iProto_message_def). by eexists. Qed.
Definition iProto_message := iProto_message_aux.(unseal).
Definition iProto_message_eq :
  @iProto_message = @iProto_message_def := iProto_message_aux.(seal_eq).
Arguments iProto_message {_ _} _ _%proto.
Instance: Params (@iProto_message) 3 := {}.

Notation "< a > x1 .. xn , 'MSG' v {{ P } } ; p" :=
  (iProto_message
    a
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,P%I,p%proto)) ..))
  (at level 20, a at level 10, x1 binder, xn binder,
   v at level 20, P, p at level 200) : proto_scope.
Notation "< a > x1 .. xn , 'MSG' v ; p" :=
  (iProto_message
    a
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,True%I,p%proto)) ..))
  (at level 20, a at level 10, x1 binder, xn binder,
   v at level 20, p at level 200) : proto_scope.
Notation "< a > 'MSG' v {{ P } } ; p" :=
  (iProto_message
    a
    (tele_app (TT:=TeleO) (v%V,P%I,p%proto)))
  (at level 20, a at level 10, v at level 20, P, p at level 200) : proto_scope.
Notation "< a > 'MSG' v ; p" :=
  (iProto_message
    a
    (tele_app (TT:=TeleO) (v%V,True%I,p%proto)))
  (at level 20, a at level 10, v at level 20, p at level 200) : proto_scope.

Notation "<!> x1 .. xn , 'MSG' v {{ P } } ; p" :=
  (iProto_message
    Send
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,P%I,p%proto)) ..))
  (at level 20, x1 binder, xn binder, v at level 20, P, p at level 200) : proto_scope.
Notation "<!> x1 .. xn , 'MSG' v ; p" :=
  (iProto_message
    Send
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,True%I,p%proto)) ..))
  (at level 20, x1 binder, xn binder, v at level 20, p at level 200) : proto_scope.
Notation "<!> 'MSG' v {{ P } } ; p" :=
  (iProto_message
    (TT:=TeleO)
    Send
    (tele_app (TT:=TeleO) (v%V,P%I,p%proto)))
  (at level 20, v at level 20, P, p at level 200) : proto_scope.
Notation "<!> 'MSG' v ; p" :=
  (iProto_message
    (TT:=TeleO)
    Send
    (tele_app (TT:=TeleO) (v%V,True%I,p%proto)))
  (at level 20, v at level 20, p at level 200) : proto_scope.

Notation "<?> x1 .. xn , 'MSG' v {{ P } } ; p" :=
  (iProto_message
    Receive
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,P%I,p%proto)) ..))
  (at level 20, x1 binder, xn binder, v at level 20, P, p at level 200) : proto_scope.
Notation "<?> x1 .. xn , 'MSG' v ; p" :=
  (iProto_message
    Receive
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,True%I,p%proto)) ..))
  (at level 20, x1 binder, xn binder, v at level 20, p at level 200) : proto_scope.
Notation "<?> 'MSG' v {{ P } } ; p" :=
  (iProto_message
    Receive
    (tele_app (TT:=TeleO) (v%V,P%I,p%proto)))
  (at level 20, v at level 20, P, p at level 200) : proto_scope.
Notation "<?> 'MSG' v ; p" :=
  (iProto_message
    Receive
    (tele_app (TT:=TeleO) (v%V,True%I,p%proto)))
  (at level 20, v at level 20, p at level 200) : proto_scope.

Notation "'END'" := iProto_end : proto_scope.

(** * Operations *)
Definition iProto_dual {Σ} (p : iProto Σ) : iProto Σ :=
  proto_map action_dual cid cid p.
Arguments iProto_dual {_} _%proto.
Instance: Params (@iProto_dual) 1 := {}.
Definition iProto_dual_if {Σ} (d : bool) (p : iProto Σ) : iProto Σ :=
  if d then iProto_dual p else p.
Arguments iProto_dual_if {_} _ _%proto.
Instance: Params (@iProto_dual_if) 2 := {}.

Definition iProto_branch {Σ} (a : action) (P1 P2 : iProp Σ)
    (p1 p2 : iProto Σ) : iProto Σ :=
  (<a> (b : bool), MSG #b {{ if b then P1 else P2 }}; if b then p1 else p2)%proto.
Typeclasses Opaque iProto_branch.
Arguments iProto_branch {_} _ _%I _%I _%proto _%proto.
Instance: Params (@iProto_branch) 2 := {}.
Infix "<{ P1 }+{ P2 }>" := (iProto_branch Send P1 P2) (at level 85) : proto_scope.
Infix "<{ P1 }&{ P2 }>" := (iProto_branch Receive P1 P2) (at level 85) : proto_scope.
Infix "<+{ P2 }>" := (iProto_branch Send True P2) (at level 85) : proto_scope.
Infix "<&{ P2 }>" := (iProto_branch Receive True P2) (at level 85) : proto_scope.
Infix "<{ P1 }+>" := (iProto_branch Send P1 True) (at level 85) : proto_scope.
Infix "<{ P1 }&>" := (iProto_branch Receive P1 True) (at level 85) : proto_scope.
Infix "<+>" := (iProto_branch Send True True) (at level 85) : proto_scope.
Infix "<&>" := (iProto_branch Receive True True) (at level 85) : proto_scope.

Definition iProto_app {Σ} (p1 p2 : iProto Σ) : iProto Σ := proto_app p1 p2.
Arguments iProto_app {_} _%proto _%proto.
Instance: Params (@iProto_app) 1 := {}.
Infix "<++>" := iProto_app (at level 60) : proto_scope.

(** * Auxiliary definitions and invariants *)
Definition proto_eq_next {Σ} (p : iProto Σ) : laterO (iProto Σ) -n> iPropO Σ :=
  OfeMor (sbi_internal_eq (Next p)).

Program Definition iProto_le_aux `{invG Σ} (rec : iProto Σ -n> iProto Σ -n> iPropO Σ) :
    iProto Σ -n> iProto Σ -n> iPropO Σ := λne p1 p2,
  ((p1 ≡ proto_end ∗ p2 ≡ proto_end) ∨
   (∃ pc1 pc2,
     p1 ≡ proto_message Send pc1 ∗ p2 ≡ proto_message Send pc2 ∗
     ∀ v p2', pc2 v (proto_eq_next p2') -∗
       ∃ p1', ▷ rec p1' p2' ∗ pc1 v (proto_eq_next p1')) ∨
   (∃ pc1 pc2,
     p1 ≡ proto_message Receive pc1 ∗ p2 ≡ proto_message Receive pc2 ∗
     ∀ v p1', pc1 v (proto_eq_next p1') -∗
       ∃ p2', ▷ rec p1' p2' ∗ pc2 v (proto_eq_next p2')))%I.
Solve Obligations with solve_proper.
Local Instance iProto_le_aux_contractive `{invG Σ} : Contractive (@iProto_le_aux Σ _).
Proof. solve_contractive. Qed.
Definition iProto_le `{invG Σ} (p1 p2 : iProto Σ) : iProp Σ :=
  fixpoint iProto_le_aux p1 p2.
Arguments iProto_le {_ _} _%proto _%proto.
Instance: Params (@iProto_le) 2 := {}.

Fixpoint proto_interp {Σ} (vs : list val) (p1 p2 : iProto Σ) : iProp Σ :=
  match vs with
  | [] => iProto_dual p1 ≡ p2
  | v :: vs => ∃ pc p2',
     p2 ≡ proto_message Receive pc ∗
     pc v (proto_eq_next p2') ∗
     proto_interp vs p1 p2'
  end.
Arguments proto_interp {_} _ _%proto _%proto : simpl nomatch.

Record proto_name := ProtName {
  proto_c_name : chan_name;
  proto_l_name : gname;
  proto_r_name : gname
}.

Definition to_pre_proto {Σ} (p : iProto Σ) :
    proto val (iPrePropO Σ) (iPrePropO Σ) :=
  proto_map id iProp_fold iProp_unfold p.

Definition proto_own_frag `{!proto_chanG Σ} (γ : proto_name) (s : side)
    (p : iProto Σ) : iProp Σ :=
  own (side_elim s proto_l_name proto_r_name γ) (◯E (Next (to_pre_proto p))).

Definition proto_own_auth `{!proto_chanG Σ} (γ : proto_name) (s : side)
    (p : iProto Σ) : iProp Σ :=
  own (side_elim s proto_l_name proto_r_name γ) (●E (Next (to_pre_proto p))).

Definition proto_inv `{!invG Σ, proto_chanG Σ} (γ : proto_name) : iProp Σ :=
  ∃ vsl vsr pl pr pl' pr',
    chan_own (proto_c_name γ) Left vsl ∗
    chan_own (proto_c_name γ) Right vsr ∗
    proto_own_auth γ Left pl' ∗
    proto_own_auth γ Right pr' ∗
    ▷ (iProto_le pl pl' ∗
       iProto_le pr pr' ∗
       ((⌜vsr = []⌝ ∗ proto_interp vsl pl pr) ∨
        (⌜vsl = []⌝ ∗ proto_interp vsr pr pl))).

Definition protoN := nroot .@ "proto".

(** * The connective for ownership of channel ends *)
Definition mapsto_proto_def `{!proto_chanG Σ, !heapG Σ}
    (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ s (c1 c2 : val) γ p',
    ⌜ c = side_elim s c1 c2 ⌝ ∗
    iProto_le p' p ∗
    proto_own_frag γ s p' ∗
    is_chan protoN (proto_c_name γ) c1 c2 ∗
    inv protoN (proto_inv γ).
Definition mapsto_proto_aux : seal (@mapsto_proto_def). by eexists. Qed.
Definition mapsto_proto {Σ pΣ hΣ} := mapsto_proto_aux.(unseal) Σ pΣ hΣ.
Definition mapsto_proto_eq :
  @mapsto_proto = @mapsto_proto_def := mapsto_proto_aux.(seal_eq).
Arguments mapsto_proto {_ _ _} _ _%proto.
Instance: Params (@mapsto_proto) 4 := {}.

Notation "c ↣ p" := (mapsto_proto c p)
  (at level 20, format "c  ↣  p").

(** * Proofs *)
Section proto.
  Context `{!proto_chanG Σ, !heapG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  (** ** Non-expansiveness of operators *)
  Lemma iProto_message_contractive {TT} a
      (pc1 pc2 : TT → val * iProp Σ * iProto Σ) n :
    (∀.. x, (pc1 x).1.1 = (pc2 x).1.1) →
    (∀.. x, dist_later n ((pc1 x).1.2) ((pc2 x).1.2)) →
    (∀.. x, dist_later n ((pc1 x).2) ((pc2 x).2)) →
    iProto_message a pc1 ≡{n}≡ iProto_message a pc2.
  Proof.
    rewrite !tforall_forall=> Hv HP Hp.
    rewrite iProto_message_eq /iProto_message_def.
    f_equiv=> v f /=. apply bi.exist_ne=> x.
    repeat (apply Hv || apply HP || apply Hp || f_contractive || f_equiv).
  Qed.
  Lemma iProto_message_ne {TT} a
      (pc1 pc2 : TT → val * iProp Σ * iProto Σ) n :
    (∀.. x, (pc1 x).1.1 = (pc2 x).1.1) →
    (∀.. x, (pc1 x).1.2 ≡{n}≡ (pc2 x).1.2) →
    (∀.. x, (pc1 x).2 ≡{n}≡ (pc2 x).2) →
    iProto_message a pc1 ≡{n}≡ iProto_message a pc2.
  Proof.
    rewrite !tforall_forall=> Hv HP Hp.
    apply iProto_message_contractive; apply tforall_forall; eauto using dist_dist_later.
  Qed.
  Lemma iProto_message_proper {TT} a
      (pc1 pc2 : TT → val * iProp Σ * iProto Σ) :
    (∀.. x, (pc1 x).1.1 = (pc2 x).1.1) →
    (∀.. x, (pc1 x).1.2 ≡ (pc2 x).1.2) →
    (∀.. x, (pc1 x).2 ≡ (pc2 x).2) →
    iProto_message a pc1 ≡ iProto_message a pc2.
  Proof.
    rewrite !tforall_forall=> Hv HP Hp. apply equiv_dist => n.
    apply iProto_message_ne; apply tforall_forall=> x; by try apply equiv_dist.
  Qed.

  Global Instance iProto_branch_contractive n a :
    Proper (dist_later n ==> dist_later n ==>
            dist_later n ==> dist_later n ==> dist n) (@iProto_branch Σ a).
  Proof.
    intros p1 p1' Hp1 p2 p2' Hp2 P1 P1' HP1 P2 P2' HP2.
    apply iProto_message_contractive=> /= -[] //.
  Qed.
  Global Instance iProto_branch_ne n a :
    Proper (dist n ==> dist n ==> dist n ==> dist n ==> dist n) (@iProto_branch Σ a).
  Proof.
    intros p1 p1' Hp1 p2 p2' Hp2 P1 P1' HP1 P2 P2' HP2.
    by apply iProto_message_ne=> /= -[].
  Qed.
  Global Instance iProto_branch_proper a :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (@iProto_branch Σ a).
  Proof.
    intros p1 p1' Hp1 p2 p2' Hp2 P1 P1' HP1 P2 P2' HP2.
    by apply iProto_message_proper=> /= -[].
  Qed.

  (** ** Dual *)
  Global Instance iProto_dual_ne : NonExpansive (@iProto_dual Σ).
  Proof. solve_proper. Qed.
  Global Instance iProto_dual_proper : Proper ((≡) ==> (≡)) (@iProto_dual Σ).
  Proof. apply (ne_proper _). Qed.
  Global Instance iProto_dual_if_ne d : NonExpansive (@iProto_dual_if Σ d).
  Proof. solve_proper. Qed.
  Global Instance iProto_dual_if_proper d : Proper ((≡) ==> (≡)) (@iProto_dual_if Σ d).
  Proof. apply (ne_proper _). Qed.

  Global Instance iProto_dual_involutive : Involutive (≡) (@iProto_dual Σ).
  Proof.
    intros p. rewrite /iProto_dual -proto_map_compose -{2}(proto_map_id p).
    apply: proto_map_ext=> //. by intros [].
  Qed.

  Lemma iProto_dual_end : iProto_dual (Σ:=Σ) END ≡ END%proto.
  Proof. by rewrite iProto_end_eq /iProto_dual proto_map_end. Qed.
  Lemma iProto_dual_message {TT} a (pc : TT → val * iProp Σ * iProto Σ) :
    iProto_dual (iProto_message a pc)
    ≡ iProto_message (action_dual a) (prod_map id iProto_dual ∘ pc).
  Proof.
    rewrite /iProto_dual iProto_message_eq /iProto_message_def proto_map_message.
    by f_equiv=> v f /=.
  Qed.

  Lemma iProto_dual_branch a P1 P2 p1 p2 :
    iProto_dual (iProto_branch a P1 P2 p1 p2)
    ≡ iProto_branch (action_dual a) P1 P2 (iProto_dual p1) (iProto_dual p2).
  Proof.
    rewrite /iProto_branch iProto_dual_message /=.
    by apply iProto_message_proper=> /= -[].
  Qed.

  (** ** Append *)
  Global Instance iProto_app_ne : NonExpansive2 (@iProto_app Σ).
  Proof. apply _. Qed.
  Global Instance iProto_app_proper : Proper ((≡) ==> (≡) ==> (≡)) (@iProto_app Σ).
  Proof. apply (ne_proper_2 _). Qed.

  Lemma iProto_app_message {TT} a (pc : TT → val * iProp Σ * iProto Σ) p2 :
    (iProto_message a pc <++> p2)%proto
    ≡ iProto_message a (prod_map id (flip iProto_app p2) ∘ pc).
  Proof.
    rewrite /iProto_app iProto_message_eq /iProto_message_def proto_app_message.
    by f_equiv=> v f /=.
  Qed.

  Global Instance iProto_app_end_l : LeftId (≡) END%proto (@iProto_app Σ).
  Proof.
    intros p. by rewrite iProto_end_eq /iProto_end_def /iProto_app proto_app_end_l.
  Qed.
  Global Instance iProto_app_end_r : RightId (≡) END%proto (@iProto_app Σ).
  Proof.
    intros p. by rewrite iProto_end_eq /iProto_end_def /iProto_app proto_app_end_r.
  Qed.
  Global Instance iProto_app_assoc : Assoc (≡) (@iProto_app Σ).
  Proof. intros p1 p2 p3. by rewrite /iProto_app proto_app_assoc. Qed.

  Lemma iProto_app_branch a P1 P2 p1 p2 q :
    (iProto_branch a P1 P2 p1 p2 <++> q)%proto
    ≡ (iProto_branch a P1 P2 (p1 <++> q) (p2 <++> q))%proto.
  Proof.
    rewrite /iProto_branch iProto_app_message.
    by apply iProto_message_proper=> /= -[].
  Qed.

  Lemma iProto_dual_app p1 p2 :
    iProto_dual (p1 <++> p2) ≡ (iProto_dual p1 <++> iProto_dual p2)%proto.
  Proof. by rewrite /iProto_dual /iProto_app proto_map_app. Qed.

  (** ** Protocol entailment **)
  Global Instance iProto_le_ne : NonExpansive2 (@iProto_le Σ _).
  Proof. solve_proper. Qed.
  Global Instance iProto_le_proper : Proper ((≡) ==> (≡) ==> (⊣⊢)) (@iProto_le Σ _).
  Proof. solve_proper. Qed.

  Lemma iProto_le_unfold p1 p2 :
    iProto_le p1 p2 ≡ iProto_le_aux (fixpoint iProto_le_aux) p1 p2.
  Proof. apply: (fixpoint_unfold iProto_le_aux). Qed.

  Lemma iProto_le_refl p : ⊢ iProto_le p p.
  Proof.
    iLöb as "IH" forall (p). destruct (proto_case p) as [->|([]&pc&->)].
    - rewrite iProto_le_unfold. iLeft; by auto.
    - rewrite iProto_le_unfold. iRight; iLeft. iExists _, _; do 2 (iSplit; [done|]).
      iIntros (v p') "Hpc". iExists p'. iIntros "{$Hpc} !>". iApply "IH".
    - rewrite iProto_le_unfold. iRight; iRight. iExists _, _; do 2 (iSplit; [done|]).
      iIntros (v p') "Hpc". iExists p'. iIntros "{$Hpc} !>". iApply "IH".
  Qed.

  Lemma iProto_le_end_inv p : iProto_le p proto_end -∗ p ≡ proto_end.
  Proof.
    rewrite iProto_le_unfold. iIntros "[[Hp _]|H] //".
    iDestruct "H" as "[H|H]"; iDestruct "H" as (pc1 pc2) "(_ & Heq & _)";
      by rewrite proto_end_message_equivI.
  Qed.

  Lemma iProto_le_send_inv p1 pc2 :
    iProto_le p1 (proto_message Send pc2) -∗ ∃ pc1,
      p1 ≡ proto_message Send pc1 ∗
      ∀ v p2', pc2 v (proto_eq_next p2') -∗
        ∃ p1', ▷ iProto_le p1' p2' ∗ pc1 v (proto_eq_next p1').
  Proof.
    rewrite iProto_le_unfold. iIntros "[[_ Heq]|[H|H]]".
    - by rewrite proto_message_end_equivI.
    - iDestruct "H" as (pc1 pc2') "(Hp1 & Heq & H)".
      iDestruct (proto_message_equivI with "Heq") as "[_ #Heq]".
      iExists pc1. iIntros "{$Hp1}" (v p2') "Hpc".
      iSpecialize ("Heq" $! v). iDestruct (bi.ofe_morO_equivI with "Heq") as "Heq'".
      iRewrite ("Heq'" $! (proto_eq_next p2')) in "Hpc". by iApply "H".
    - iDestruct "H" as (pc1 pc2') "(_ & Heq & _)".
      by iDestruct (proto_message_equivI with "Heq") as "[% ?]".
  Qed.

  Lemma iProto_le_recv_inv p1 pc2 :
    iProto_le p1 (proto_message Receive pc2) -∗ ∃ pc1,
      p1 ≡ proto_message Receive pc1 ∗
      ∀ v p1', pc1 v (proto_eq_next p1') -∗
        ∃ p2', ▷ iProto_le p1' p2' ∗ pc2 v (proto_eq_next p2').
  Proof.
    rewrite iProto_le_unfold. iIntros "[[_ Heq]|[H|H]]".
    - by rewrite proto_message_end_equivI.
    - iDestruct "H" as (pc1 pc2') "(_ & Heq & _)".
      by iDestruct (proto_message_equivI with "Heq") as "[% ?]".
    - iDestruct "H" as (pc1 pc2') "(Hp1 & Heq & H)".
      iDestruct (proto_message_equivI with "Heq") as "[_ #Heq]".
      iExists pc1. iIntros "{$Hp1}" (v p1') "Hpc".
      iSpecialize ("Heq" $! v). iDestruct (bi.ofe_morO_equivI with "Heq") as "Heq'".
      iDestruct ("H" with "Hpc") as (p2') "[Hle Hpc]".
      iExists p2'. iFrame "Hle". by iRewrite ("Heq'" $! (proto_eq_next p2')).
  Qed.

  Lemma iProto_le_trans p1 p2 p3 :
    iProto_le p1 p2 -∗ iProto_le p2 p3 -∗ iProto_le p1 p3.
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (p1 p2 p3).
    destruct (proto_case p3) as [->|([]&pc3&->)].
    - rewrite iProto_le_end_inv. by iRewrite "H2" in "H1".
    - iDestruct (iProto_le_send_inv with "H2") as (pc2) "[Hp2 H3]".
      iRewrite "Hp2" in "H1".
      iDestruct (iProto_le_send_inv with "H1") as (pc1) "[Hp1 H2]".
      iRewrite "Hp1". rewrite iProto_le_unfold; iRight; iLeft.
      iExists _, _; do 2 (iSplit; [done|]).
      iIntros (v p3') "Hpc".
      iDestruct ("H3" with "Hpc") as (p2') "[Hle Hpc]".
      iDestruct ("H2" with "Hpc") as (p1') "[Hle' Hpc]".
      iExists p1'. iIntros "{$Hpc} !>". by iApply ("IH" with "Hle'").
    - iDestruct (iProto_le_recv_inv with "H2") as (pc2) "[Hp2 H3]".
      iRewrite "Hp2" in "H1".
      iDestruct (iProto_le_recv_inv with "H1") as (pc1) "[Hp1 H2]".
      iRewrite "Hp1". rewrite iProto_le_unfold; iRight; iRight.
      iExists _, _; do 2 (iSplit; [done|]).
      iIntros (v p1') "Hpc".
      iDestruct ("H2" with "Hpc") as (p2') "[Hle Hpc]".
      iDestruct ("H3" with "Hpc") as (p3') "[Hle' Hpc]".
      iExists p3'. iIntros "{$Hpc} !>". by iApply ("IH" with "Hle").
  Qed.

  Lemma iProto_send_le {TT1 TT2} (pc1 : TT1 → val * iProp Σ * iProto Σ)
      (pc2 : TT2 → val * iProp Σ * iProto Σ) :
    (∀.. x2 : TT2, ▷ (pc2 x2).1.2 -∗ ∃.. x1 : TT1,
      ⌜(pc1 x1).1.1 = (pc2 x2).1.1⌝ ∗
      ▷ (pc1 x1).1.2 ∗
      ▷ iProto_le (pc1 x1).2 (pc2 x2).2) -∗
    iProto_le (iProto_message Send pc1) (iProto_message Send pc2).
  Proof.
    iIntros "H". rewrite iProto_le_unfold iProto_message_eq. iRight; iLeft.
    iExists _, _; do 2 (iSplit; [done|]).
    iIntros (v p2') "/=". iDestruct 1 as (x2 ->) "[Hpc #Heq]".
    iDestruct ("H" with "Hpc") as (x1 ?) "[Hpc Hle]".
    iExists (pc1 x1).2. iSplitL "Hle".
    { iIntros "!>". change (fixpoint iProto_le_aux ?p1 ?p2) with (iProto_le p1 p2).
      by iRewrite "Heq". }
    iExists x1. iSplit; [done|]. iSplit; [by iApply "Hpc"|done].
  Qed.

  Lemma iProto_recv_le {TT1 TT2} (pc1 : TT1 → val * iProp Σ * iProto Σ)
      (pc2 : TT2 → val * iProp Σ * iProto Σ) :
    (∀.. x1 : TT1, ▷ (pc1 x1).1.2 -∗ ∃.. x2 : TT2,
      ⌜(pc1 x1).1.1 = (pc2 x2).1.1⌝ ∗
      ▷ (pc2 x2).1.2 ∗
      ▷ iProto_le (pc1 x1).2 (pc2 x2).2) -∗
    iProto_le (iProto_message Receive pc1) (iProto_message Receive pc2).
  Proof.
    iIntros "H". rewrite iProto_le_unfold iProto_message_eq. iRight; iRight.
    iExists _, _; do 2 (iSplit; [done|]).
    iIntros (v p1') "/=". iDestruct 1 as (x1 ->) "[Hpc #Heq]".
    iDestruct ("H" with "Hpc") as (x2 ?) "[Hpc Hle]". iExists (pc2 x2).2. iSplitL "Hle".
    { iIntros "!>". change (fixpoint iProto_le_aux ?p1 ?p2) with (iProto_le p1 p2).
      by iRewrite "Heq". }
    iExists x2. iSplit; [done|]. iSplit; [by iApply "Hpc"|done].
  Qed.

  Lemma iProto_mapsto_le c p1 p2 : c ↣ p1 -∗ iProto_le p1 p2 -∗ c ↣ p2.
  Proof.
    rewrite mapsto_proto_eq. iDestruct 1 as (s c1 c2 γ p1' ->) "[Hle H]".
    iIntros "Hle'". iExists s, c1, c2, γ, p1'. iSplit; first done. iFrame "H".
    by iApply (iProto_le_trans with "Hle").
  Qed.

  (** ** Lemmas about the auxiliary definitions and invariants *)
  Global Instance proto_interp_ne : NonExpansive2 (proto_interp (Σ:=Σ) vs).
  Proof. induction vs; solve_proper. Qed.
  Global Instance proto_interp_proper vs :
    Proper ((≡) ==> (≡) ==> (≡)) (proto_interp (Σ:=Σ) vs).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance to_pre_proto_ne : NonExpansive (to_pre_proto (Σ:=Σ)).
  Proof. solve_proper. Qed.
  Global Instance proto_own_ne γ s : NonExpansive (proto_own_frag γ s).
  Proof. solve_proper. Qed.
  Global Instance mapsto_proto_ne c : NonExpansive (mapsto_proto c).
  Proof. rewrite mapsto_proto_eq. solve_proper. Qed.
  Global Instance mapsto_proto_proper c : Proper ((≡) ==> (≡)) (mapsto_proto c).
  Proof. apply (ne_proper _). Qed.

  Lemma proto_own_auth_agree γ s p p' :
    proto_own_auth γ s p -∗ proto_own_frag γ s p' -∗ ▷ (p ≡ p').
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
    iDestruct (excl_auth_agreeI with "Hvalid") as "Hvalid".
    iDestruct (bi.later_eq_1 with "Hvalid") as "Hvalid"; iNext.
    rewrite /to_pre_proto. assert (∀ p,
      proto_map id iProp_unfold iProp_fold (proto_map id iProp_fold iProp_unfold p) ≡ p) as help.
    { intros p''. rewrite -proto_map_compose -{2}(proto_map_id p'').
      apply proto_map_ext=> // pc /=; by rewrite iProp_fold_unfold. }
    rewrite -{2}(help p). iRewrite "Hvalid". by rewrite help.
  Qed.

  Lemma proto_own_auth_update γ s p p' p'' :
    proto_own_auth γ s p -∗ proto_own_frag γ s p' ==∗
    proto_own_auth γ s p'' ∗ proto_own_frag γ s p''.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_update_2 with "Hauth Hfrag") as "H".
    { eapply (excl_auth_update _ _ (Next (to_pre_proto p''))). }
    by rewrite own_op.
  Qed.

  Lemma proto_eq_next_dual p :
    ofe_mor_map (laterO_map (proto_map action_dual cid cid)) cid (proto_eq_next (iProto_dual p)) ≡
    proto_eq_next p.
  Proof.
    intros lp. iSplit; iIntros "Hlp /="; last by iRewrite -"Hlp".
    destruct (Next_uninj lp) as [p' ->].
    rewrite /later_map /= !bi.later_equivI. iNext.
    rewrite -{2}(involutive iProto_dual p) -{2}(involutive iProto_dual p').
    by iRewrite "Hlp".
  Qed.

  Lemma proto_interp_send v vs pc p1 p2 :
    proto_interp vs (proto_message Send pc) p2 -∗
    pc v (proto_eq_next p1) -∗
    proto_interp (vs ++ [v]) p1 p2.
  Proof.
    iIntros "Heval Hc". iInduction vs as [|v' vs] "IH" forall (p2); simpl.
    - iDestruct "Heval" as "#Heval".
      iExists _, (iProto_dual p1). iSplit.
      { iRewrite -"Heval". by rewrite /iProto_dual proto_map_message. }
      rewrite /= proto_eq_next_dual; auto.
    - iDestruct "Heval" as (pc' p2') "(Heq & Hc' & Heval)".
      iExists pc', p2'. iFrame "Heq Hc'". iApply ("IH" with "Heval Hc").
  Qed.

  Lemma proto_interp_recv v vs p1 pc :
    proto_interp (v :: vs) p1 (proto_message Receive pc) -∗ ∃ p2,
      pc v (proto_eq_next p2) ∗
      proto_interp vs p1 p2.
  Proof.
    simpl. iDestruct 1 as (pc' p2) "(Heq & Hc & Hp2)". iExists p2. iFrame "Hp2".
    iDestruct (@proto_message_equivI with "Heq") as "[_ Heq]".
    iSpecialize ("Heq" $! v). rewrite bi.ofe_morO_equivI.
    by iRewrite ("Heq" $! (proto_eq_next p2)).
  Qed.

  Lemma proto_interp_False p pc v vs :
    proto_interp (v :: vs) p (proto_message Send pc) -∗ False.
  Proof.
    simpl. iDestruct 1 as (pc' p2') "[Heq _]".
    by iDestruct (@proto_message_equivI with "Heq") as "[% _]".
  Qed.

  Lemma proto_interp_nil p1 p2 : proto_interp [] p1 p2 -∗ p1 ≡ iProto_dual p2.
  Proof. iIntros "#H /=". iRewrite -"H". by rewrite involutive. Qed.

  Arguments proto_interp : simpl never.

  (** ** Helper lemma for initialization of a channel *)
  Lemma proto_init E cγ c1 c2 p :
    is_chan protoN cγ c1 c2 -∗
    chan_own cγ Left [] -∗ chan_own cγ Right [] ={E}=∗
    c1 ↣ p ∗ c2 ↣ iProto_dual p.
  Proof.
    iIntros "#Hcctx Hcol Hcor".
    iMod (own_alloc (●E (Next (to_pre_proto p)) ⋅
                     ◯E (Next (to_pre_proto p)))) as (lγ) "[Hlsta Hlstf]".
    { by apply excl_auth_valid. }
    iMod (own_alloc (●E (Next (to_pre_proto (iProto_dual p))) ⋅
                     ◯E (Next (to_pre_proto (iProto_dual p))))) as (rγ) "[Hrsta Hrstf]".
    { by apply excl_auth_valid. }
    pose (ProtName cγ lγ rγ) as pγ.
    iMod (inv_alloc protoN _ (proto_inv pγ) with "[-Hlstf Hrstf Hcctx]") as "#Hinv".
    { iNext. iExists [], [], p, (iProto_dual p), p, (iProto_dual p). iFrame.
      do 2 (iSplitL; [iApply iProto_le_refl|]). auto. }
    iModIntro. rewrite mapsto_proto_eq. iSplitL "Hlstf".
    - iExists Left, c1, c2, pγ, p.
      iFrame "Hlstf Hinv Hcctx". iSplit; [done|]. iApply iProto_le_refl.
    - iExists Right, c1, c2, pγ, (iProto_dual p).
      iFrame "Hrstf Hinv Hcctx". iSplit; [done|]. iApply iProto_le_refl.
  Qed.

  (** ** Accessor style lemmas, used as helpers to prove the specifications of
  [send] and [recv]. *)
  Lemma proto_send_acc {TT} c (pc : TT → val * iProp Σ * iProto Σ) (x : TT) :
    c ↣ iProto_message Send pc -∗
    (pc x).1.2 -∗
    ∃ s c1 c2 γ,
      ⌜ c = side_elim s c1 c2 ⌝ ∗
      is_chan protoN (proto_c_name γ) c1 c2 ∗ |={⊤,⊤∖↑protoN}=> ∃ vs,
        chan_own (proto_c_name γ) s vs ∗
        ▷ (chan_own (proto_c_name γ) s (vs ++ [(pc x).1.1]) ={⊤∖↑protoN,⊤}=∗
           c ↣ (pc x).2).
  Proof.
    rewrite {1}mapsto_proto_eq iProto_message_eq. iIntros "Hc HP".
    iDestruct "Hc" as (s c1 c2 γ p ->) "(Hle & Hst & #[Hcctx Hinv])".
    iExists s, c1, c2, γ. iSplit; first done. iFrame "Hcctx".
    iDestruct (iProto_le_send_inv with "Hle") as (pc') "[Hp H] /=".
    iRewrite "Hp" in "Hst"; clear p.
    iDestruct ("H" with "[HP]") as (p1') "[Hle HP]".
    { iExists _. iFrame "HP". by iSplit. }
    iInv protoN as (vsl vsr pl pr pl' pr')
      "(>Hcl & >Hcr & Hstla & Hstra & Hlel & Hler & Hinv')" "Hclose".
    (* TODO: refactor to avoid twice nearly the same proof *)
    iModIntro. destruct s.
    - iExists _. iIntros "{$Hcl} !> Hcl".
      iDestruct (proto_own_auth_agree with "Hstla Hst") as "#Heq".
      iMod (proto_own_auth_update _ _ _ _ (pc x).2 with "Hstla Hst") as "[Hstla Hst]".
      iMod ("Hclose" with "[-Hst]") as "_".
      { iNext. iRewrite "Heq" in "Hlel". iClear (pl') "Heq".
        iDestruct (iProto_le_send_inv with "Hlel") as (pc'') "[Hpl H] /=".
        iRewrite "Hpl" in "Hinv'"; clear pl.
        iDestruct ("H" with "HP") as (p1'') "[Hlel HP]".
        iExists _, _, _, _, _, _. iFrame "Hcr Hstra Hstla Hcl Hler".
        iNext. iSplitL "Hle Hlel".
        { by iApply (iProto_le_trans with "[$]"). }
        iLeft. iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]".
        { iSplit=> //. iApply (proto_interp_send with "Heval HP"). }
        destruct vsr as [|vr vsr]; last first.
        { iDestruct (proto_interp_False with "Heval") as %[]. }
        iSplit; first done; simpl. iRewrite (proto_interp_nil with "Heval").
        iApply (proto_interp_send _ [] with "[//] HP"). }
      iModIntro. rewrite mapsto_proto_eq. iExists Left, c1, c2, γ, (pc x).2.
      iFrame "Hcctx Hinv Hst". iSplit; [done|]. iApply iProto_le_refl.
    - (* iExists _. iIntros "{$Hcr} !> Hcr".
      iDestruct (proto_own_auth_agree with "Hstra Hst") as "#Heq".
      iMod (proto_own_auth_update _ _ _ _ p1' with "Hstra Hst") as "[Hstra Hst]".
      iMod ("Hclose" with "[-Hst Hle]") as "_".
      { iNext. iExists _, _, _, _. iFrame "Hcl Hstra Hstla Hcr". iRight.
        iRewrite "Heq" in "Hinv'".
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]"; last first.
        { iSplit=> //. by iApply (proto_interp_send with "Heval [HP]"). }
        destruct l as [|vl l]; last first.
        { iDestruct (proto_interp_False with "Heval") as %[]. }
        iSplit; first done; simpl. iRewrite (proto_interp_nil with "Heval").
        iApply (proto_interp_send _ [] with "[//] HP"). }
      iModIntro. rewrite mapsto_proto_eq. iExists Right, c1, c2, γ, p1'.
      by iFrame "Hcctx Hinv Hst Hle". *) admit.
  Admitted.

  Lemma proto_recv_acc {TT} c (pc : TT → val * iProp Σ * iProto Σ) :
    c ↣ iProto_message Receive pc -∗
    ∃ s c1 c2 γ,
      ⌜ c = side_elim s c2 c1 ⌝ ∗
      is_chan protoN (proto_c_name γ) c1 c2 ∗ |={⊤,⊤∖↑protoN}=> ∃ vs,
        chan_own (proto_c_name γ) s vs ∗
        ▷ ((chan_own (proto_c_name γ) s vs ={⊤∖↑protoN,⊤}=∗
             c ↣ iProto_message Receive pc) ∧
           (∀ v vs',
             ⌜ vs = v :: vs' ⌝ -∗
             chan_own (proto_c_name γ) s vs' ={⊤∖↑protoN,⊤,⊤}▷=∗ ▷ ∃ x : TT,
             ⌜ v = (pc x).1.1 ⌝ ∗ c ↣ (pc x).2 ∗ (pc x).1.2)).
  Proof.
    rewrite {1}mapsto_proto_eq iProto_message_eq.
    iDestruct 1 as (s c1 c2 γ p ->) "(Hle & Hst & #[Hcctx Hinv])".
    iDestruct (iProto_le_recv_inv with "Hle") as (pc') "[Hp Hle] /=".
    iRewrite "Hp" in "Hst". clear p.
    iExists (side_elim s Right Left), c1, c2, γ. iSplit; first by destruct s.
    iFrame "Hcctx".
    iInv protoN as (vsl vsr pl pr pl' pr')
      "(>Hcl & >Hcr & Hstla & Hstra & Hlel & Hler & Hinv')" "Hclose".
    iExists (side_elim s vsr vsl). iModIntro.
    (* TODO: refactor to avoid twice nearly the same proof *)
    destruct s; simpl.
    - iIntros "{$Hcr} !>". 
      iDestruct (proto_own_auth_agree with "Hstla Hst") as "#Hpl'".
      iSplit.
      + iIntros "Hcr".
        iMod ("Hclose" with "[-Hst Hle]") as "_".
        { iNext. iExists vsl, vsr, _, _, _, _. iFrame. }
        iModIntro. rewrite mapsto_proto_eq.
        iExists Left, c1, c2, γ, (proto_message Receive pc').
        iFrame "Hcctx Hinv Hst". iSplit; first done.
        rewrite iProto_le_unfold. iRight; auto 10.
      + iIntros (v vs ->) "Hcr".
        iDestruct "Hinv'" as "[[>% _]|[>-> Heval]]"; first done.
        iAssert (▷ iProto_le pl (proto_message Receive pc'))%I with "[Hlel]" as "Hlel".
        { iNext. by iRewrite "Hpl'" in "Hlel". }
        iDestruct (iProto_le_recv_inv with "Hlel") as (pc'') "[#Hpl Hlel] /=".
        iAssert (▷ proto_interp (v :: vs) pr (proto_message Receive pc''))%I
          with "[Heval]" as "Heval".
        { iNext. by iRewrite "Hpl" in "Heval". }
        iDestruct (proto_interp_recv with "Heval") as (q) "[Hpc Heval]".
        iDestruct ("Hlel" with "Hpc") as (p1'') "[Hlel Hpc]".
        iDestruct ("Hle" with "Hpc") as (p1''') "[Hle Hpc]".
        iMod (proto_own_auth_update _ _ _ _ p1''' with "Hstla Hst") as "[Hstla Hst]".
        iMod ("Hclose" with "[-Hst Hpc]") as %_.
        { iExists _, _, q, _, _, _. iFrame "Hcl Hcr Hstra Hstla Hler".
          iIntros "!> !>". iSplitL "Hle Hlel"; last by auto.
          by iApply (iProto_le_trans with "[$]"). }
        iIntros "!> !> !>". iDestruct "Hpc" as (x) "(Hv & HP & #Hf) /=".
        iIntros "!>". iExists x. iFrame "Hv HP". iRewrite -"Hf".
        rewrite mapsto_proto_eq. iExists Left, c1, c2, γ, p1'''.
        iFrame "Hst Hcctx Hinv". iSplit; [done|]. iApply iProto_le_refl.
    - (* iIntros "{$Hcl} !>".
      iDestruct (proto_own_auth_agree with "Hstra Hst") as "#Heq".
      iSplit.
      + iIntros "Hcl".
        iMod ("Hclose" with "[-Hst Hle]") as "_".
        { iNext. iExists l, r, _, _. iFrame. }
        iModIntro. rewrite mapsto_proto_eq.
        iExists Right, c1, c2, γ, (proto_message Receive pc').
        iFrame "Hcctx Hinv Hst". iSplit; first done.
        rewrite iProto_le_unfold. iRight; auto 10.
      + iIntros (v vs ->) "Hcl".
        iDestruct "Hinv'" as "[[-> Heval]|[% _]]"; last done.
        iAssert (▷ proto_interp (v :: vs) pl (proto_message Receive pc'))%I
          with "[Heval]" as "Heval".
        { iNext. by iRewrite "Heq" in "Heval". }
        iDestruct (proto_interp_recv with "Heval") as (q) "[Hpc Heval]".
        iMod (proto_own_auth_update _ _ _ _ q with "Hstra Hst") as "[Hstra Hst]".
        iMod ("Hclose" with "[-Hst Hpc Hle]") as %_.
        { iExists _, _, _, _. eauto 10 with iFrame. }
        iIntros "!> !>". iMod ("Hle" with "Hpc") as (q') "[Hle H]".
        iDestruct "H" as (x) "(Hv & HP & Hf) /=".
        iIntros "!> !>". iExists x. iFrame "Hv HP". iRewrite -"Hf".
        rewrite mapsto_proto_eq. iExists Right, c1, c2, γ, q. iFrame; auto.
  Qed. *) Admitted.

  (** ** Specifications of [send] and [recv] *)
  Lemma new_chan_proto_spec :
    {{{ True }}}
      new_chan #()
    {{{ c1 c2, RET (c1,c2); (∀ p, |={⊤}=> c1 ↣ p ∗ c2 ↣ iProto_dual p) }}}.
  Proof.
    iIntros (Ψ _) "HΨ". iApply wp_fupd. wp_apply new_chan_spec=> //.
    iIntros (c1 c2 γ) "(Hc & Hl & Hr)". iApply "HΨ"; iIntros "!>" (p).
    iApply (proto_init ⊤ γ c1 c2 p with "Hc Hl Hr").
  Qed.

  Lemma start_chan_proto_spec p Ψ (f : val) :
    ▷ (∀ c, c ↣ iProto_dual p -∗ WP f c {{ _, True }}) -∗
    ▷ (∀ c, c ↣ p -∗ Ψ c) -∗
    WP start_chan f {{ Ψ }}.
  Proof.
    iIntros "Hfork HΨ". wp_lam.
    wp_apply (new_chan_proto_spec with "[//]"); iIntros (c1 c2) "Hc".
    iMod ("Hc" $! p) as "[Hc1 Hc2]".
    wp_apply (wp_fork with "[Hfork Hc2]").
    { iNext. wp_apply ("Hfork" with "Hc2"). }
    wp_pures. iApply ("HΨ" with "Hc1").
  Qed.

  Lemma send_proto_spec_packed {TT} c (pc : TT → val * iProp Σ * iProto Σ) (x : TT) :
    {{{ c ↣ iProto_message Send pc ∗ (pc x).1.2 }}}
      send c (pc x).1.1
    {{{ RET #(); c ↣ (pc x).2 }}}.
  Proof.
    iIntros (Ψ) "[Hp HP] HΨ".
    iDestruct (proto_send_acc with "Hp HP") as (γ s c1 c2 ->) "[#Hc Hvs]".
    iApply (send_spec with "[$]"). iMod "Hvs" as (vs) "[Hch H]".
    iModIntro. iExists vs. iFrame "Hch".
    iIntros "!> Hvs". iApply "HΨ".
    iMod ("H" with "Hvs"); auto.
  Qed.

  (** A version written without Texan triples that is more convenient to use
  (via [iApply] in Coq. *)
  Lemma send_proto_spec {TT} Ψ c v (pc : TT → val * iProp Σ * iProto Σ) :
    c ↣ iProto_message Send pc -∗
    (∃.. x : TT,
      ⌜ v = (pc x).1.1 ⌝ ∗ (pc x).1.2 ∗ ▷ (c ↣ (pc x).2 -∗ Ψ #())) -∗
    WP send c v {{ Ψ }}.
  Proof.
    iIntros "Hc H". iDestruct (bi_texist_exist with "H") as (x ->) "[HP HΨ]".
    by iApply (send_proto_spec_packed with "[$]").
  Qed.

  Lemma try_recv_proto_spec_packed {TT} c (pc : TT → val * iProp Σ * iProto Σ) :
    {{{ c ↣ iProto_message Receive pc }}}
      try_recv c
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ c ↣ iProto_message Receive pc) ∨
                  (∃ x : TT, ⌜v = SOMEV ((pc x).1.1)⌝ ∗ c ↣ (pc x).2 ∗ (pc x).1.2) }}}.
  Proof.
    iIntros (Ψ) "Hp HΨ".
    iDestruct (proto_recv_acc with "Hp") as (γ s c1 c2 ->) "[#Hc Hvs]".
    wp_apply (try_recv_spec with "[$]"). iSplit.
    - iMod "Hvs" as (vs) "[Hch [H _]]".
      iIntros "!> !>". iMod ("H" with "Hch") as "Hch". iApply "HΨ"; auto.
    - iMod "Hvs" as (vs) "[Hch [_ H]]".
      iIntros "!>". iExists vs. iIntros "{$Hch} !>" (v vs' ->) "Hch".
      iMod ("H" with "[//] Hch") as "H". iIntros "!> !>". iMod "H".
      iIntros "!> !>". iDestruct "H" as (x ->) "H". iApply "HΨ"; auto.
  Qed.

  Lemma recv_proto_spec_packed {TT} c (pc : TT → val * iProp Σ * iProto Σ) :
    {{{ c ↣ iProto_message Receive pc }}}
      recv c
    {{{ x, RET (pc x).1.1; c ↣ (pc x).2 ∗ (pc x).1.2 }}}.
  Proof.
    iIntros (Ψ) "Hp HΨ".
    iDestruct (proto_recv_acc with "Hp") as (γ s c1 c2 ->) "[#Hc Hvs]".
    wp_apply (recv_spec with "[$]"). iMod "Hvs" as (vs) "[Hch [_ H]]".
    iModIntro. iExists vs. iIntros "{$Hch} !>" (v vs' ->) "Hvs'".
    iMod ("H" with "[//] Hvs'") as "H"; iIntros "!> !>". iMod "H".
    iIntros "!> !>". iDestruct "H" as (x ->) "H". by iApply "HΨ".
  Qed.

  (** A version written without Texan triples that is more convenient to use
  (via [iApply] in Coq. *)
  Lemma recv_proto_spec {TT} Ψ c (pc : TT → val * iProp Σ * iProto Σ) :
    c ↣ iProto_message Receive pc -∗
    ▷ (∀.. x : TT, c ↣ (pc x).2 -∗ (pc x).1.2 -∗ Ψ (pc x).1.1) -∗
    WP recv c {{ Ψ }}.
  Proof.
    iIntros "Hc H". iApply (recv_proto_spec_packed with "[$]").
    iIntros "!>" (x) "[Hc HP]". iDestruct (bi_tforall_forall with "H") as "H".
    iApply ("H" with "[$] [$]").
  Qed.

  (** ** Specifications for branching *)
  Lemma select_spec c (b : bool) P1 P2 p1 p2 :
    {{{ c ↣ (p1 <{P1}+{P2}> p2) ∗ if b then P1 else P2 }}}
      send c #b
    {{{ RET #(); c ↣ (if b then p1 else p2) }}}.
  Proof.
    rewrite /iProto_branch. iIntros (Ψ) "[Hc HP] HΨ".
    iApply (send_proto_spec with "Hc"); simpl; eauto with iFrame.
  Qed.

  Lemma branch_spec c P1 P2 p1 p2 :
    {{{ c ↣ (p1 <{P1}&{P2}> p2) }}}
      recv c
    {{{ b, RET #b; c ↣ (if b : bool then p1 else p2) ∗ if b then P1 else P2 }}}.
  Proof.
    rewrite /iProto_branch. iIntros (Ψ) "Hc HΨ".
    iApply (recv_proto_spec with "Hc"); simpl.
    iIntros "!>" (b) "Hc HP". iApply "HΨ". iFrame.
  Qed.
End proto.
