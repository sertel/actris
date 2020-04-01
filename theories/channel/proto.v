(** This file defines the core of the Actris logic: It defines dependent
separation protocols and the various operations on it like dual, append, and
branching.

Dependent separation protocols are defined by instantiating the parameterized
version in [proto_model] with type of propositions [iProp] of Iris. We define
ways of constructing instances of the instantiated type via two constructors:
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

Lastly, relevant type classes instances are defined for each of the above
notions, such as contractiveness and non-expansiveness, after which the
specifications of the message-passing primitives are defined in terms of the
protocol connectives. *)
From iris.algebra Require Import excl_auth.
From iris.bi Require Import telescopes.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.own.
From actris.channel Require Import proto_model.
Set Default Proof Using "Type".
Export action.

(** * Setup of Iris's cameras *)
Class protoG Σ V :=
  protoG_authG :>
    inG Σ (excl_authR (laterO (proto (leibnizO V) (iPrePropO Σ) (iPrePropO Σ)))).

Definition protoΣ V := #[
  GFunctor (authRF (optionURF (exclRF (laterOF (protoOF (leibnizO V) idOF idOF)))))
].
Instance subG_chanΣ {Σ V} : subG (protoΣ V) Σ → protoG Σ V.
Proof. solve_inG. Qed.

(** * Types *)
Definition iProto Σ V := proto V (iPropO Σ) (iPropO Σ).
Delimit Scope proto_scope with proto.
Bind Scope proto_scope with iProto.

(** * Operators *)
Definition iProto_end_def {Σ V} : iProto Σ V := proto_end.
Definition iProto_end_aux : seal (@iProto_end_def). by eexists. Qed.
Definition iProto_end := iProto_end_aux.(unseal).
Definition iProto_end_eq : @iProto_end = @iProto_end_def := iProto_end_aux.(seal_eq).
Arguments iProto_end {_ _}.

Program Definition iProto_message_def {Σ V} {TT : tele} (a : action)
    (pc : TT → V * iProp Σ * iProto Σ V) : iProto Σ V :=
  proto_message a (λ v, λne p', ∃ x : TT,
    (** We need the later to make [iProto_message] contractive *)
    ⌜ v = (pc x).1.1 ⌝ ∗
    ▷ (pc x).1.2 ∗
    p' ≡ Next (pc x).2)%I.
Next Obligation. solve_proper. Qed.
Definition iProto_message_aux : seal (@iProto_message_def). by eexists. Qed.
Definition iProto_message := iProto_message_aux.(unseal).
Definition iProto_message_eq :
  @iProto_message = @iProto_message_def := iProto_message_aux.(seal_eq).
Arguments iProto_message {_ _ _} _ _%proto.
Instance: Params (@iProto_message) 4 := {}.

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
    Recv
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,P%I,p%proto)) ..))
  (at level 20, x1 binder, xn binder, v at level 20, P, p at level 200) : proto_scope.
Notation "<?> x1 .. xn , 'MSG' v ; p" :=
  (iProto_message
    Recv
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,True%I,p%proto)) ..))
  (at level 20, x1 binder, xn binder, v at level 20, p at level 200) : proto_scope.
Notation "<?> 'MSG' v {{ P } } ; p" :=
  (iProto_message
    Recv
    (tele_app (TT:=TeleO) (v%V,P%I,p%proto)))
  (at level 20, v at level 20, P, p at level 200) : proto_scope.
Notation "<?> 'MSG' v ; p" :=
  (iProto_message
    Recv
    (tele_app (TT:=TeleO) (v%V,True%I,p%proto)))
  (at level 20, v at level 20, p at level 200) : proto_scope.

Notation "'END'" := iProto_end : proto_scope.

(** * Operations *)
Program Definition iProto_map_cont {Σ V}
    (rec : iProto Σ V → iProto Σ V) (pc : laterO (iProto Σ V) -n> iPropO Σ) :
    laterO (iProto Σ V) -n> iPropO Σ :=
  λne p2, (∃ p1, pc (Next p1) ∗ p2 ≡ Next (rec p1))%I.
Next Obligation. solve_proper. Qed.

Program Definition iProto_map_app_aux {Σ V} 
    (f : action → action) (p2 : iProto Σ V)
    (rec : iProto Σ V -n> iProto Σ V) : iProto Σ V -n> iProto Σ V := λne p1,
  match proto_unfold p1 return _ with
  | None => p2
  | Some (a, pc) => proto_message (f a) (iProto_map_cont rec ∘ pc)
  end.
Next Obligation.
  intros Σ V f p2 rec n p1 p1'
    [[??][??] [-> Hf]|]%(ofe_mor_ne _ _ proto_unfold); last done.
  f_equiv=> v pc; rewrite /= /iProto_map_cont /=. by repeat f_equiv.
Qed.

Instance iProto_map_app_aux_contractive {Σ V} f (p2 : iProto Σ V) :
  Contractive (iProto_map_app_aux f p2).
Proof.
  intros n rec1 rec2 Hrec p1. simpl.
  destruct (proto_unfold p1) as [[a c]|]; last done.
  f_equiv=> v p' /=. by repeat (f_contractive || f_equiv).
Qed.

Definition iProto_map_app {Σ V} (f : action → action)
    (p2 : iProto Σ V) : iProto Σ V -n> iProto Σ V :=
  fixpoint (iProto_map_app_aux f p2).

Definition iProto_app_def {Σ V} (p1 p2 : iProto Σ V) : iProto Σ V :=
  iProto_map_app id p2 p1.
Definition iProto_app_aux : seal (@iProto_app_def). by eexists. Qed.
Definition iProto_app := iProto_app_aux.(unseal).
Definition iProto_app_eq : @iProto_app = @iProto_app_def := iProto_app_aux.(seal_eq).
Arguments iProto_app {_ _} _%proto _%proto.
Instance: Params (@iProto_app) 2 := {}.
Infix "<++>" := iProto_app (at level 60) : proto_scope.

Definition iProto_dual_def {Σ V} (p : iProto Σ V) : iProto Σ V :=
  iProto_map_app action_dual proto_end p.
Definition iProto_dual_aux : seal (@iProto_dual_def). by eexists. Qed.
Definition iProto_dual := iProto_dual_aux.(unseal).
Definition iProto_dual_eq :
  @iProto_dual = @iProto_dual_def := iProto_dual_aux.(seal_eq).
Arguments iProto_dual {_ _} _%proto.
Instance: Params (@iProto_dual) 2 := {}.
Definition iProto_dual_if {Σ V} (d : bool) (p : iProto Σ V) : iProto Σ V :=
  if d then iProto_dual p else p.
Arguments iProto_dual_if {_ _} _ _%proto.
Instance: Params (@iProto_dual_if) 3 := {}.

(** * Protocol entailment *)
(* The definition [iProto_le] generalizes the following inductive definition
for subtyping on session types:

                 p1 <: p2           p1 <: p2
----------   ----------------   ----------------
end <: end    !A.p1 <: !A.p2     ?A.p1 <: ?A.p2

 p1 <: !B.p3    ?A.p3 <: p2
----------------------------
       ?A.p1 <: !B.p2

Example:

!R <: !R  ?Q <: ?Q      ?Q <: ?Q
-------------------  --------------
?Q.!R <: !R.?Q       ?P.?Q <: ?P.?Q
------------------------------------
   ?P.?Q.!R <: !R.?P.?Q
*)
Definition iProto_le_pre {Σ V}
    (rec : iProto Σ V → iProto Σ V → iProp Σ) (p1 p2 : iProto Σ V) : iProp Σ :=
  (p1 ≡ proto_end ∗ p2 ≡ proto_end) ∨
  ∃ a1 a2 pc1 pc2,
    p1 ≡ proto_message a1 pc1 ∗
    p2 ≡ proto_message a2 pc2 ∗
    match a1, a2 with
    | Recv, Recv =>
       ∀ v p1', pc1 v (Next p1') -∗
         ∃ p2', ▷ rec p1' p2' ∗ pc2 v (Next p2')
    | Send, Send =>
       ∀ v p2', pc2 v (Next p2') -∗
         ∃ p1', ▷ rec p1' p2' ∗ pc1 v (Next p1')
    | Recv, Send =>
       ∀ v1 v2 p1' p2',
         pc1 v1 (Next p1') -∗ pc2 v2 (Next p2') -∗
         ∃ pc1' pc2' pt,
           ▷ rec p1' (proto_message Send pc1') ∗
           ▷ rec (proto_message Recv pc2') p2' ∗
           pc1' v2 (Next pt) ∗
           pc2' v1 (Next pt)
    | Send, Recv => False
    end.
Instance iProto_le_pre_ne {Σ V} (rec : iProto Σ V → iProto Σ V → iProp Σ) :
  NonExpansive2 (iProto_le_pre rec).
Proof. solve_proper. Qed.

Program Definition iProto_le_pre' {Σ V}
    (rec : iProto Σ V -n> iProto Σ V -n> iPropO Σ) :
    iProto Σ V -n> iProto Σ V -n> iPropO Σ :=
  λne p1 p2, iProto_le_pre (λ p1' p2', rec p1' p2') p1 p2.
Solve Obligations with solve_proper.
Local Instance iProto_le_pre_contractive {Σ V} : Contractive (@iProto_le_pre' Σ V).
Proof.
  intros n rec1 rec2 Hrec p1 p2. rewrite /iProto_le_pre' /iProto_le_pre /=.
  by repeat (f_contractive || f_equiv).
Qed.
Definition iProto_le {Σ V} (p1 p2 : iProto Σ V) : iProp Σ :=
  fixpoint iProto_le_pre' p1 p2.
Arguments iProto_le {_ _} _%proto _%proto.
Instance: Params (@iProto_le) 2 := {}.

Fixpoint iProto_interp_aux {Σ V} (n : nat)
    (vsl vsr : list V) (pl pr : iProto Σ V) : iProp Σ :=
  match n with
  | 0 => ∃ p,
     ⌜ vsl = [] ⌝ ∗
     ⌜ vsr = [] ⌝ ∗
     iProto_le p pl ∗
     iProto_le (iProto_dual p) pr
  | S n =>
     (∃ vl vsl' pc p2',
       ⌜ vsl = vl :: vsl' ⌝ ∗
       iProto_le (proto_message Recv pc) pr ∗
       pc vl (Next p2') ∗
       iProto_interp_aux n vsl' vsr pl p2') ∨
     (∃ vr vsr' pc p1',
       ⌜ vsr = vr :: vsr' ⌝ ∗
       iProto_le (proto_message Recv pc) pl ∗
       pc vr (Next p1') ∗
       iProto_interp_aux n vsl vsr' p1' pr)
  end.
Definition iProto_interp {Σ V} (vsl vsr : list V) (pl pr : iProto Σ V) : iProp Σ :=
  iProto_interp_aux (length vsl + length vsr) vsl vsr pl pr.
Arguments iProto_interp {_ _} _ _ _%proto _%proto : simpl nomatch.

Record proto_name := ProtName { proto_l_name : gname; proto_r_name : gname }.
Instance proto_name_inhabited : Inhabited proto_name :=
  populate (ProtName inhabitant inhabitant).
Instance proto_name_eq_dec : EqDecision proto_name.
Proof. solve_decision. Qed.
Instance proto_name_countable : Countable proto_name.
Proof.
 refine (inj_countable (λ '(ProtName γl γr), (γl,γr))
   (λ '(γl, γr), Some (ProtName γl γr)) _); by intros [].
Qed.

Inductive side := Left | Right.
Instance side_inhabited : Inhabited side := populate Left.
Instance side_eq_dec : EqDecision side.
Proof. solve_decision. Qed.
Instance side_countable : Countable side.
Proof.
 refine (inj_countable (λ s, if s is Left then true else false)
   (λ b, Some (if b then Left else Right)) _); by intros [].
Qed.
Definition side_elim {A} (s : side) (l r : A) : A :=
  match s with Left => l | Right => r end.

Definition iProto_unfold {Σ V} (p : iProto Σ V) : proto V (iPrePropO Σ) (iPrePropO Σ) :=
  proto_map iProp_fold iProp_unfold p.
Definition iProto_own_frag `{!protoG Σ V} (γ : proto_name) (s : side)
    (p : iProto Σ V) : iProp Σ :=
  own (side_elim s proto_l_name proto_r_name γ) (◯E (Next (iProto_unfold p))).
Definition iProto_own_auth `{!protoG Σ V} (γ : proto_name) (s : side)
    (p : iProto Σ V) : iProp Σ :=
  own (side_elim s proto_l_name proto_r_name γ) (●E (Next (iProto_unfold p))).

Definition iProto_ctx `{protoG Σ V}
    (γ : proto_name) (vsl vsr : list V) : iProp Σ :=
  ∃ pl pr,
    iProto_own_auth γ Left pl ∗
    iProto_own_auth γ Right pr ∗
    ▷ iProto_interp vsl vsr pl pr.

(** * The connective for ownership of channel ends *)
Definition iProto_own `{!protoG Σ V}
    (γ : proto_name) (s : side) (p : iProto Σ V) : iProp Σ :=
  ∃ p', ▷ iProto_le p' p ∗ iProto_own_frag γ s p'.
Arguments iProto_own {_ _ _} _ _%proto.
Instance: Params (@iProto_own) 3 := {}.

(** * Proofs *)
Section proto.
  Context `{!protoG Σ V}.
  Implicit Types p pl pr : iProto Σ V.
  Implicit Types TT : tele.

  (** ** Non-expansiveness of operators *)
  Lemma iProto_message_contractive {TT} a
      (pc1 pc2 : TT → V * iProp Σ * iProto Σ V) n :
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
  Lemma iProto_message_ne {TT} a (pc1 pc2 : TT → V * iProp Σ * iProto Σ V) n :
    (∀.. x, (pc1 x).1.1 = (pc2 x).1.1) →
    (∀.. x, (pc1 x).1.2 ≡{n}≡ (pc2 x).1.2) →
    (∀.. x, (pc1 x).2 ≡{n}≡ (pc2 x).2) →
    iProto_message a pc1 ≡{n}≡ iProto_message a pc2.
  Proof.
    rewrite !tforall_forall=> Hv HP Hp.
    apply iProto_message_contractive; apply tforall_forall; eauto using dist_dist_later.
  Qed.
  Lemma iProto_message_proper {TT} a (pc1 pc2 : TT → V * iProp Σ * iProto Σ V) :
    (∀.. x, (pc1 x).1.1 = (pc2 x).1.1) →
    (∀.. x, (pc1 x).1.2 ≡ (pc2 x).1.2) →
    (∀.. x, (pc1 x).2 ≡ (pc2 x).2) →
    iProto_message a pc1 ≡ iProto_message a pc2.
  Proof.
    rewrite !tforall_forall=> Hv HP Hp. apply equiv_dist => n.
    apply iProto_message_ne; apply tforall_forall=> x; by try apply equiv_dist.
  Qed.

  (** ** Dual *)
  Global Instance iProto_dual_ne : NonExpansive (@iProto_dual Σ V).
  Proof. rewrite iProto_dual_eq. solve_proper. Qed.
  Global Instance iProto_dual_proper : Proper ((≡) ==> (≡)) (@iProto_dual Σ V).
  Proof. apply (ne_proper _). Qed.
  Global Instance iProto_dual_if_ne d : NonExpansive (@iProto_dual_if Σ V d).
  Proof. solve_proper. Qed.
  Global Instance iProto_dual_if_proper d :
    Proper ((≡) ==> (≡)) (@iProto_dual_if Σ V d).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_dual_end' : iProto_dual (Σ:=Σ) (V:=V) proto_end ≡ proto_end.
  Proof.
    rewrite iProto_dual_eq /iProto_dual_def /iProto_map_app.
    etrans; [eapply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    pose proof (proto_unfold_fold (V:=V)
      (PROP:=iPropO Σ) (PROPn:=iPropO Σ) None) as Hfold.
    by destruct (proto_unfold (proto_fold None))
      as [[??]|] eqn:E; rewrite E; inversion Hfold.
  Qed.
  Lemma iProto_dual_message' a pc :
    iProto_dual (Σ:=Σ) (V:=V) (proto_message a pc)
    ≡ proto_message (action_dual a) (iProto_map_cont iProto_dual ∘ pc).
  Proof.
    rewrite iProto_dual_eq /iProto_dual_def /iProto_map_app /proto_message.
    etrans; [eapply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    pose proof (proto_unfold_fold (V:=V) (PROP:=iPropO Σ)
      (PROPn:=iPropO Σ) (Some (a,pc))) as Hfold.
    destruct (proto_unfold (proto_fold (Some (a, pc))))
      as [[??]|] eqn:E; inversion Hfold as [?? [Ha Hpc]|]; simplify_eq/=.
    rewrite /proto_message. do 3 f_equiv; intros v p'; simpl. by repeat f_equiv.
  Qed.

  Lemma iProto_dual_end : iProto_dual (Σ:=Σ) (V:=V) END ≡ END%proto.
  Proof. rewrite iProto_end_eq. apply iProto_dual_end'. Qed.

  Lemma iProto_dual_message {TT} a (pc : TT → V * iProp Σ * iProto Σ V) :
    iProto_dual (iProto_message a pc)
    ≡ iProto_message (action_dual a) (prod_map id iProto_dual ∘ pc).
  Proof.
    rewrite iProto_message_eq /iProto_message_def iProto_dual_message' /=.
    do 2 f_equiv; intros p'; simpl. iSplit.
    - iDestruct 1 as (pd) "[H Hp']". iDestruct "H" as (x ->) "[Hpc Hpd]".
      iExists x. iSplit; [done|]; iFrame. iRewrite "Hp'". iNext. by iRewrite "Hpd".
    - iDestruct 1 as (x ->) "[Hpc Hpd]"; auto 10.
  Qed.

  Global Instance iProto_dual_involutive : Involutive (≡) (@iProto_dual Σ V).
  Proof.
    intros p. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p). destruct (proto_case p) as [->|(a&pc&->)].
    { by rewrite !iProto_dual_end'. }
    rewrite !iProto_dual_message' involutive.
    iApply proto_message_equivI; iSplit; [done|]; iIntros (v p') "/=".
    iApply prop_ext; iIntros "!>"; iSplit.
    - iDestruct 1 as (pd) "[H Hp']". iRewrite "Hp'".
      iDestruct "H" as (pdd) "[H #Hpd]".
      iApply (bi.internal_eq_rewrite); [|done]; iModIntro.
      iRewrite "Hpd". by iRewrite ("IH" $! pdd).
    - iIntros "H". destruct (Next_uninj p') as [p'' Hp']. iExists (iProto_dual p'').
      rewrite Hp'. iSplitL; [by auto|]. iNext. by iRewrite ("IH" $! p'').
  Qed.

  (** ** Append *)
  Lemma iProto_app_end' p : (proto_end <++> p)%proto ≡ p.
  Proof.
    rewrite iProto_app_eq /iProto_app_def /iProto_map_app.
    etrans; [eapply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    pose proof (proto_unfold_fold (V:=V)
      (PROP:=iPropO Σ) (PROPn:=iPropO Σ) None) as Hfold.
    by destruct (proto_unfold (proto_fold None))
      as [[??]|] eqn:E; rewrite E; inversion Hfold.
  Qed.
  Lemma iProto_app_message' a pc p2 :
    (proto_message a pc <++> p2)%proto
    ≡ proto_message a (iProto_map_cont (flip iProto_app p2) ∘ pc).
  Proof.
    rewrite iProto_app_eq /iProto_app_def /iProto_map_app /proto_message.
    etrans; [eapply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    pose proof (proto_unfold_fold (V:=V) (PROP:=iPropO Σ)
      (PROPn:=iPropO Σ) (Some (a,pc))) as Hfold.
    destruct (proto_unfold (proto_fold (Some (a, pc))))
      as [[??]|] eqn:E; inversion Hfold as [?? [Ha Hpc]|]; simplify_eq/=.
    rewrite /proto_message. do 3 f_equiv; intros v p'; simpl. by repeat f_equiv.
  Qed.

  Global Instance iProto_app_ne : NonExpansive2 (@iProto_app Σ V).
  Proof.
    assert (∀ n, Proper (dist n ==> (=) ==> dist n) (@iProto_app Σ V)).
    { intros n p1 p1' Hp1 p2 p2' <-. by rewrite iProto_app_eq /iProto_app_def Hp1. }
    assert (Proper ((≡) ==> (=) ==> (≡)) (@iProto_app Σ V)).
    { intros p1 p1' Hp1 p2 p2' <-. by rewrite iProto_app_eq /iProto_app_def Hp1. }
    intros n p1 p1' Hp1 p2 p2' Hp2. rewrite Hp1. clear p1 Hp1.
    revert p1'. induction (lt_wf n) as [n _ IH]; intros p1.
    destruct (proto_case p1) as [->|(a&pc&->)].
    { by rewrite !iProto_app_end'. }
    rewrite !iProto_app_message'. f_equiv=> v p' /=. f_equiv=> p12.
    do 2 f_equiv. f_contractive. apply IH; eauto using dist_le with lia.
  Qed.
  Global Instance iProto_app_proper : Proper ((≡) ==> (≡) ==> (≡)) (@iProto_app Σ V).
  Proof. apply (ne_proper_2 _). Qed.

  Lemma iProto_app_message {TT} a (pc : TT → V * iProp Σ * iProto Σ V) p2 :
    (iProto_message a pc <++> p2)%proto
    ≡ iProto_message a (prod_map id (flip iProto_app p2) ∘ pc).
  Proof.
    rewrite iProto_message_eq /iProto_message_def iProto_app_message' /=.
    f_equiv=> v ps /=. iSplit.
    - iDestruct 1 as (p1') "[H Hps]". iDestruct "H" as (x ->) "[Hpc #Hp1']".
      iExists x. iSplit; [done|]. iFrame. iRewrite "Hps". iNext. by iRewrite "Hp1'".
    - iDestruct 1 as (x ->) "[Hpc Hps]". auto 10.
  Qed.

  Global Instance iProto_app_end_l : LeftId (≡) END%proto (@iProto_app Σ V).
  Proof. intros p. by rewrite iProto_end_eq /iProto_end_def iProto_app_end'. Qed.
  Global Instance iProto_app_end_r : RightId (≡) END%proto (@iProto_app Σ V).
  Proof.
    rewrite iProto_end_eq /iProto_end_def.
    intros p. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p). destruct (proto_case p) as [->|(a&pc&->)].
    { by rewrite iProto_app_end'. }
    rewrite iProto_app_message'.
    iApply proto_message_equivI; iSplit; [done|]; iIntros (v p') "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (p1') "[H Hp']". iRewrite "Hp'".
      iApply (bi.internal_eq_rewrite); [|done]; iModIntro.
      by iRewrite ("IH" $! p1').
    - iIntros "H". destruct (Next_uninj p') as [p'' Hp']. iExists p''.
      rewrite Hp'. iFrame "H". iNext. by iRewrite ("IH" $! p'').
  Qed.
  Global Instance iProto_app_assoc : Assoc (≡) (@iProto_app Σ V).
  Proof.
    intros p1 p2 p3. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p1). destruct (proto_case p1) as [->|(a&pc&->)].
    { by rewrite !iProto_app_end'. }
    rewrite !iProto_app_message'.
    iApply proto_message_equivI; iSplit; [done|]; iIntros (v p123) "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (p1') "[H #Hp']".
      iExists (p1' <++> p2)%proto. iSplitL; [by auto|].
      iRewrite "Hp'". iNext. iApply "IH".
    - iDestruct 1 as (p12) "[H #Hp123]". iDestruct "H" as (p1') "[H #Hp12]".
      iExists p1'. iFrame "H". iRewrite "Hp123".
      iNext. iRewrite "Hp12". by iRewrite ("IH" $! p1').
  Qed.

  Lemma iProto_dual_app p1 p2 :
    iProto_dual (p1 <++> p2) ≡ (iProto_dual p1 <++> iProto_dual p2)%proto.
  Proof.
    apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p1 p2). destruct (proto_case p1) as [->|(a&pc&->)].
    { by rewrite iProto_dual_end' !iProto_app_end'. }
    rewrite iProto_dual_message' !iProto_app_message' iProto_dual_message' /=.
    iApply proto_message_equivI; iSplit; [done|]; iIntros (v p12) "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (p12d) "[H #Hp12]". iDestruct "H" as (p1') "[H #Hp12d]".
      iExists (iProto_dual p1'). iSplitL; [by auto|].
      iRewrite "Hp12". iNext. iRewrite "Hp12d". iApply "IH".
    - iDestruct 1 as (p1') "[H #Hp12]". iDestruct "H" as (p1d) "[H #Hp1']".
      iExists (p1d <++> p2)%proto. iSplitL; [by auto|].
      iRewrite "Hp12". iNext. iRewrite "Hp1'". by iRewrite ("IH" $! p1d p2).
  Qed.

  (** ** Protocol entailment **)
  Global Instance iProto_le_ne : NonExpansive2 (@iProto_le Σ V).
  Proof. solve_proper. Qed.
  Global Instance iProto_le_proper : Proper ((≡) ==> (≡) ==> (⊣⊢)) (@iProto_le Σ V).
  Proof. solve_proper. Qed.

  Lemma iProto_le_unfold p1 p2 : iProto_le p1 p2 ≡ iProto_le_pre iProto_le p1 p2.
  Proof. apply: (fixpoint_unfold iProto_le_pre'). Qed.

  Lemma iProto_le_refl p : ⊢ iProto_le p p.
  Proof.
    iLöb as "IH" forall (p). destruct (proto_case p) as [->|([]&pc&->)].
    - rewrite iProto_le_unfold. iLeft; by auto.
    - rewrite iProto_le_unfold. iRight. iExists _, _, _, _; do 2 (iSplit; [done|]).
      iIntros (v p') "Hpc". iExists p'. iIntros "{$Hpc} !>". iApply "IH".
    - rewrite iProto_le_unfold. iRight. iExists _, _, _, _; do 2 (iSplit; [done|]).
      iIntros (v p') "Hpc". iExists p'. iIntros "{$Hpc} !>". iApply "IH".
  Qed.

  Lemma iProto_le_end_inv p : iProto_le p proto_end -∗ p ≡ proto_end.
  Proof.
    rewrite iProto_le_unfold. iIntros "[[Hp _]|H] //".
    iDestruct "H" as (a1 a2 pc1 pc2) "(_ & Heq & _)".
    by iDestruct (proto_end_message_equivI with "Heq") as %[].
  Qed.

  Lemma iProto_le_send_inv p1 pc2 :
    iProto_le p1 (proto_message Send pc2) -∗ ∃ a1 pc1,
      p1 ≡ proto_message a1 pc1 ∗
      match a1 with
      | Send =>
         ∀ v p2', pc2 v (Next p2') -∗
           ∃ p1', ▷ iProto_le p1' p2' ∗ pc1 v (Next p1')
      | Recv =>
         ∀ v1 v2 p1' p2',
           pc1 v1 (Next p1') -∗ pc2 v2 (Next p2') -∗
           ∃ pc1' pc2' pt,
             ▷ iProto_le p1' (proto_message Send pc1') ∗
             ▷ iProto_le (proto_message Recv pc2') p2' ∗
             pc1' v2 (Next pt) ∗
             pc2' v1 (Next pt)
      end.
  Proof.
    rewrite iProto_le_unfold. iIntros "[[_ Heq]|H]".
    { by iDestruct (proto_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 pc1 pc2') "(Hp1 & Hp2 & H)".
    iDestruct (proto_message_equivI with "Hp2") as (<-) "{Hp2} #Hpc".
    iExists _, _; iSplit; [done|]. destruct a1. 
    - iIntros (v p2'). by iRewrite ("Hpc" $! v (Next p2')).
    - iIntros (v1 v2 p1' p2'). by iRewrite ("Hpc" $! v2 (Next p2')).
  Qed.

  Lemma iProto_le_recv_inv p1 pc2 :
    iProto_le p1 (proto_message Recv pc2) -∗ ∃ pc1,
      p1 ≡ proto_message Recv pc1 ∗
      ∀ v p1', pc1 v (Next p1') -∗
        ∃ p2', ▷ iProto_le p1' p2' ∗ pc2 v (Next p2').
  Proof.
    rewrite iProto_le_unfold. iIntros "[[_ Heq]|H]".
    { by iDestruct (proto_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 pc1 pc2') "(Hp1 & Hp2 & H)".
    iDestruct (proto_message_equivI with "Hp2") as (<-) "{Hp2} #Hpc2".

    destruct a1; [done|]. iExists _; iSplit; [done|].
    iIntros (v p1') "Hpc". iDestruct ("H" with "Hpc") as (p2') "[Hle Hpc]".
    iExists p2'. iFrame "Hle". by iRewrite ("Hpc2" $! v (Next p2')).
  Qed.

  Lemma iProto_le_trans p1 p2 p3 :
    iProto_le p1 p2 -∗ iProto_le p2 p3 -∗ iProto_le p1 p3.
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (p1 p2 p3).
    destruct (proto_case p3) as [->|([]&pc3&->)].
    - by iRewrite (iProto_le_end_inv with "H2") in "H1".
    - iDestruct (iProto_le_send_inv with "H2") as (a2 pc2) "[Hp2 H2]".
      iRewrite "Hp2" in "H1"; clear p2. destruct a2.
      + iDestruct (iProto_le_send_inv with "H1") as (a1 pc1) "[Hp1 H1]".
        iRewrite "Hp1"; clear p1. rewrite iProto_le_unfold; iRight.
        iExists _, _, _, _; do 2 (iSplit; [done|]). destruct a1.
        * iIntros (v p3') "Hpc".
          iDestruct ("H2" with "Hpc") as (p2') "[Hle Hpc]".
          iDestruct ("H1" with "Hpc") as (p1') "[Hle' Hpc]".
          iExists p1'. iIntros "{$Hpc} !>". by iApply ("IH" with "Hle'").
        * iIntros (v1 v3 p1' p3') "Hpc1 Hpc3".
          iDestruct ("H2" with "Hpc3") as (p2') "[Hle Hpc2]".
          iDestruct ("H1" with "Hpc1 Hpc2") as (pc1' pc2' pt) "(Hp1' & Hp2' & Hpc)".
          iExists pc1', pc2', pt. iFrame "Hp1' Hpc".
          by iApply ("IH" with "Hp2'").
      + iDestruct (iProto_le_recv_inv with "H1") as (pc1) "[Hp1 H1]".
        iRewrite "Hp1"; clear p1. rewrite iProto_le_unfold; iRight.
        iExists _, _, _, _; do 2 (iSplit; [done|]); simpl.
        iIntros (v1 v3 p1' p3') "Hpc1 Hpc3".
        iDestruct ("H1" with "Hpc1") as (p2') "[Hle Hpc2]".
        iDestruct ("H2" with "Hpc2 Hpc3") as (pc2' pc3' pt) "(Hp2' & Hp3' & Hpc)".
        iExists pc2', pc3', pt. iFrame "Hp3' Hpc".
        by iApply ("IH" with "Hle").
    - iDestruct (iProto_le_recv_inv with "H2") as (pc2) "[Hp2 H3]".
      iRewrite "Hp2" in "H1".
      iDestruct (iProto_le_recv_inv with "H1") as (pc1) "[Hp1 H2]".
      iRewrite "Hp1". rewrite iProto_le_unfold. iRight.
      iExists _, _, _, _; do 2 (iSplit; [done|]).
      iIntros (v p1') "Hpc".
      iDestruct ("H2" with "Hpc") as (p2') "[Hle Hpc]".
      iDestruct ("H3" with "Hpc") as (p3') "[Hle' Hpc]".
      iExists p3'. iIntros "{$Hpc} !>". by iApply ("IH" with "Hle").
  Qed.

  Lemma iProto_le_send {TT1 TT2} (pc1 : TT1 → V * iProp Σ * iProto Σ V)
      (pc2 : TT2 → V * iProp Σ * iProto Σ V) :
    (∀.. x2 : TT2, ▷ (pc2 x2).1.2 -∗ ∃.. x1 : TT1,
      ⌜(pc1 x1).1.1 = (pc2 x2).1.1⌝ ∗
      ▷ (pc1 x1).1.2 ∗
      ▷ iProto_le (pc1 x1).2 (pc2 x2).2) -∗
    iProto_le (iProto_message Send pc1) (iProto_message Send pc2).
  Proof.
    iIntros "H". rewrite iProto_le_unfold iProto_message_eq.
    iRight. iExists _, _, _, _; do 2 (iSplit; [done|]).
    iIntros (v p2') "/=". iDestruct 1 as (x2 ->) "[Hpc #Heq]".
    iDestruct ("H" with "Hpc") as (x1 ?) "[Hpc Hle]".
    iExists (pc1 x1).2. iSplitL "Hle".
    { iIntros "!>". by iRewrite "Heq". }
    iExists x1. iSplit; [done|]. iSplit; [by iApply "Hpc"|done].
  Qed.
  (* The following derived rule is weaker, but the positions of the laters
  make more sense intuitively and practically. *)
  (* Lemma iProto_le_send' {TT1 TT2} (pc1 : TT1 → V * iProp Σ * iProto Σ V) *)
  (*     (pc2 : TT2 → V * iProp Σ * iProto Σ V) : *)
  (*   ▷ (∀.. x2 : TT2, (pc2 x2).1.2 -∗ ∃.. x1 : TT1, *)
  (*     ⌜(pc1 x1).1.1 = (pc2 x2).1.1⌝ ∗ *)
  (*     (pc1 x1).1.2 ∗ *)
  (*     iProto_le (pc1 x1).2 (pc2 x2).2) -∗ *)
  (*   iProto_le (iProto_message Send pc1) (iProto_message Send pc2). *)
  (* Proof. *)
  (*   iIntros "H". iApply iProto_le_send. iIntros (x2) "Hpc". *)
  (*   rewrite bi_tforall_forall. iDestruct ("H" with "Hpc") as "H". *)
  (*   rewrite bi_texist_exist bi.later_exist_except_0. *)
  (*   iDestruct "H" as (x1) "(>% & Hpc & Hle)". iExists x1. by iFrame. *)
  (* Qed. *)

  Lemma iProto_le_recv {TT1 TT2} (pc1 : TT1 → V * iProp Σ * iProto Σ V)
      (pc2 : TT2 → V * iProp Σ * iProto Σ V) :
    (∀.. x1 : TT1, ▷ (pc1 x1).1.2 -∗ ∃.. x2 : TT2,
      ⌜(pc1 x1).1.1 = (pc2 x2).1.1⌝ ∗
      ▷ (pc2 x2).1.2 ∗
      ▷ iProto_le (pc1 x1).2 (pc2 x2).2) -∗
    iProto_le (iProto_message Recv pc1) (iProto_message Recv pc2).
  Proof.
    iIntros "H". rewrite iProto_le_unfold iProto_message_eq.
    iRight. iExists _, _, _, _; do 2 (iSplit; [done|]).
    iIntros (v p1') "/=". iDestruct 1 as (x1 ->) "[Hpc #Heq]".
    iDestruct ("H" with "Hpc") as (x2 ?) "[Hpc Hle]". iExists (pc2 x2).2. iSplitL "Hle".
    { iIntros "!>". by iRewrite "Heq". }
    iExists x2. iSplit; [done|]. iSplit; [by iApply "Hpc"|done].
  Qed.
  (* Lemma iProto_le_recv' {TT1 TT2} (pc1 : TT1 → V * iProp Σ * iProto Σ V) *)
  (*     (pc2 : TT2 → V * iProp Σ * iProto Σ V) : *)
  (*   ▷ (∀.. x1 : TT1, (pc1 x1).1.2 -∗ ∃.. x2 : TT2, *)
  (*     ⌜(pc1 x1).1.1 = (pc2 x2).1.1⌝ ∗ *)
  (*     (pc2 x2).1.2 ∗ *)
  (*     iProto_le (pc1 x1).2 (pc2 x2).2) -∗ *)
  (*   iProto_le (iProto_message Recv pc1) (iProto_message Recv pc2). *)
  (* Proof. *)
  (*   iIntros "H". iApply iProto_le_recv. iIntros (x2) "Hpc". *)
  (*   rewrite bi_tforall_forall. iDestruct ("H" with "Hpc") as "H". *)
  (*   rewrite bi_texist_exist bi.later_exist_except_0. *)
  (*   iMod "H" as (x1) "(>% & Hpc & Hle)". iExists x1. by iFrame. *)
  (* Qed. *)

  Lemma iProto_le_swap {TT1 TT2} (pc1 : TT1 → V * iProp Σ * iProto Σ V)
      (pc2 : TT2 → V * iProp Σ * iProto Σ V) :
    (∀.. (x1 : TT1) (x2 : TT2),
      ▷ (pc1 x1).1.2 -∗ ▷ (pc2 x2).1.2 -∗
      ∃ {TT3 TT4} (pc3 : TT3 → V * iProp Σ * iProto Σ V)
          (pc4 : TT4 → V * iProp Σ * iProto Σ V), ∃.. (x3 : TT3) (x4 : TT4),
        ⌜(pc1 x1).1.1 = (pc4 x4).1.1⌝ ∗
        ⌜(pc2 x2).1.1 = (pc3 x3).1.1⌝ ∗
        ▷ iProto_le (pc1 x1).2 (iProto_message Send pc3) ∗
        ▷ iProto_le (iProto_message Recv pc4) (pc2 x2).2 ∗
        ▷ (pc3 x3).1.2 ∗ ▷ (pc4 x4).1.2 ∗
        ▷ ((pc3 x3).2 ≡ (pc4 x4).2)) -∗
    iProto_le (iProto_message Recv pc1) (iProto_message Send pc2).
  Proof.
    iIntros "H". rewrite iProto_le_unfold iProto_message_eq.
    iRight. iExists _, _, _, _; do 2 (iSplit; [done|]); simpl.
    iIntros (v1 v2 p1 p2).
    iDestruct 1 as (x1 ->) "[Hpc1 #Heq1]"; iDestruct 1 as (x2 ->) "[Hpc2 #Heq2]".
    iDestruct ("H" with "Hpc1 Hpc2")
      as (TT3 TT4 pc3 pc4 x3 x4 ??) "(H1 & H2 & Hpc1 & Hpc2 & #H)".
    iExists _, _, (pc3 x3).2. iSplitL "H1"; [iNext; by iRewrite "Heq1"|].
    iSplitL "H2"; [iNext; by iRewrite "Heq2"|]. simpl.
    iSplitL "Hpc1"; [by auto|]. iExists x4. rewrite !bi.later_equivI. auto.
  Qed.
  (* Lemma iProto_le_swap' {TT1 TT2} (pc1 : TT1 → V * iProp Σ * iProto Σ V) *)
  (*     (pc2 : TT2 → V * iProp Σ * iProto Σ V) : *)
  (*   ▷ (∀.. (x1 : TT1) (x2 : TT2), *)
  (*     (pc1 x1).1.2 -∗ (pc2 x2).1.2 -∗ *)
  (*     ∃ {TT3 TT4} (pc3 : TT3 → V * iProp Σ * iProto Σ V) *)
  (*         (pc4 : TT4 → V * iProp Σ * iProto Σ V), ∃.. (x3 : TT3) (x4 : TT4), *)
  (*       ⌜(pc1 x1).1.1 = (pc4 x4).1.1⌝ ∗ *)
  (*       ⌜(pc2 x2).1.1 = (pc3 x3).1.1⌝ ∗ *)
  (*       iProto_le (pc1 x1).2 (iProto_message Send pc3) ∗ *)
  (*       iProto_le (iProto_message Recv pc4) (pc2 x2).2 ∗ *)
  (*       (pc3 x3).1.2 ∗ (pc4 x4).1.2 ∗ *)
  (*       ((pc3 x3).2 ≡ (pc4 x4).2)) -∗ *)
  (*   iProto_le (iProto_message Recv pc1) (iProto_message Send pc2). *)
  (* Proof. *)
  (*   iIntros "H". iApply iProto_le_swap. iIntros (x1 x2) "Hpc1 Hpc2". *)
  (*   repeat setoid_rewrite bi_tforall_forall. iDestruct ("H" with "Hpc1 Hpc2") as "H". *)
  (*   iMod (bi.later_exist_except_0 with "H") as (TT3) "H". *)
  (*   iMod (bi.later_exist_except_0 with "H") as (TT4) "H". *)
  (*   iMod (bi.later_exist_except_0 with "H") as (pc3) "H". *)
  (*   iMod (bi.later_exist_except_0 with "H") as (pc4) "H". *)
  (*   rewrite bi_texist_exist bi.later_exist_except_0. iMod "H" as (x3) "H". *)
  (*   rewrite bi_texist_exist bi.later_exist_except_0. iMod "H" as (x4) "H". *)
  (*   iDestruct "H" as "(>% & >% & H1 & H2 & Hpc1 & Hpc2 & #H)". *)
  (*   iExists TT3, TT4, pc3, pc4, x3, x4. iFrame. auto. *)
  (* Qed. *)

  Lemma iProto_le_swap_simple {TT1 TT2} (v1 : TT1 → V) (v2 : TT2 → V)
      (P1 : TT1 → iProp Σ) (P2 : TT2 → iProp Σ) (p : TT1 → TT2 → iProto Σ V) :
    ⊢ iProto_le
        (iProto_message Recv (λ x1,
          (v1 x1, P1 x1, iProto_message Send (λ x2, (v2 x2, P2 x2, p x1 x2)))))
        (iProto_message Send (λ x2,
          (v2 x2, P2 x2, iProto_message Recv (λ x1, (v1 x1, P1 x1, p x1 x2))))).
  Proof.
    iApply iProto_le_swap. iIntros (x1 x2) "/= HP1 HP2".
    iExists TT2, TT1, (λ x2, (v2 x2, P2 x2, p x1 x2)),
      (λ x1, (v1 x1, P1 x1, p x1 x2)), x2, x1; simpl.
    do 2 (iSplit; [done|]). do 2 (iSplitR; [iApply iProto_le_refl|]). by iFrame.
  Qed.

  Lemma iProto_le_dual p1 p2 :
    iProto_le p2 p1 -∗ iProto_le (iProto_dual p1) (iProto_dual p2).
  Proof.
    iIntros "H". iLöb as "IH" forall (p1 p2).
    destruct (proto_case p1) as [->|([]&pc1&->)].
    - iRewrite (iProto_le_end_inv with "H"). iApply iProto_le_refl.
    - iDestruct (iProto_le_send_inv with "H") as (a2 pc2) "[Hp2 H]".
      iRewrite "Hp2"; clear p2. iEval (rewrite !iProto_dual_message').
      rewrite iProto_le_unfold; iRight.
      iExists _, _, _, _; do 2 (iSplit; [done|]); simpl. destruct a2; simpl.
      + iIntros (v p1d). iDestruct 1 as (p1') "[Hpc #Hp1d]".
        iDestruct ("H" with "Hpc") as (p2') "[H Hpc]".
        iDestruct ("IH" with "H") as "H".
        iExists (iProto_dual p2'). iSplitR "Hpc"; [|by auto].
        iNext. by iRewrite "Hp1d".
      + iIntros (v1 v2 p1d p2d).
        iDestruct 1 as (p1') "[Hpc1 #Hp1d]". iDestruct 1 as (p2') "[Hpc2 #Hp2d]".
        iDestruct ("H" with "Hpc2 Hpc1") as (pc1' pc2' pt) "(H1 & H2 & Hpc1 & Hpc2)".
        iDestruct ("IH" with "H1") as "H1". iDestruct ("IH" with "H2") as "H2 {IH}".
        rewrite !iProto_dual_message' /=. iExists _, _, (iProto_dual pt).
        iSplitL "H2"; [iNext; by iRewrite "Hp1d"|].
        iSplitL "H1"; [iNext; by iRewrite "Hp2d"|].
        iSplitL "Hpc2"; simpl; auto.
    - iDestruct (iProto_le_recv_inv with "H") as (pc2) "[Hp2 H]".
      iRewrite "Hp2"; clear p2. iEval (rewrite !iProto_dual_message' /=).
      rewrite iProto_le_unfold; iRight.
      iExists _, _, _, _; do 2 (iSplit; [done|]); simpl.
      iIntros (v p2d). iDestruct 1 as (p2') "[Hpc #Hp2d]".
      iDestruct ("H" with "Hpc") as (p1') "[H Hpc]".
      iDestruct ("IH" with "H") as "H".
      iExists (iProto_dual p1'). iSplitR "Hpc"; [|by auto].
      iNext. by iRewrite "Hp2d".
  Qed.

  Lemma iProto_le_app p1 p2 p3 p4 :
    iProto_le p1 p2 -∗ iProto_le p3 p4 -∗ iProto_le (p1 <++> p3) (p2 <++> p4).
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (p1 p2 p3 p4).
    destruct (proto_case p2) as [->|([]&pc2&->)].
    - iRewrite (iProto_le_end_inv with "H1"). by rewrite !iProto_app_end'.
    - iDestruct (iProto_le_send_inv with "H1") as (a1 pc1) "[Hp1 H1]".
      iRewrite "Hp1"; clear p1.
      rewrite !iProto_app_message'. iEval (rewrite iProto_le_unfold).
      iRight. iExists _, _, _, _; do 2 (iSplit; [done|]). destruct a1; simpl.
      + iIntros (v p24). iDestruct 1 as (p2') "[Hpc #Hp24]".
        iDestruct ("H1" with "Hpc") as (p1') "[H1 Hpc]".
        iExists (p1' <++> p3)%proto. iSplitR "Hpc"; [|eauto].
        iIntros "!>". iRewrite "Hp24". by iApply ("IH" with "H1").
      + iIntros (v1 v2 p13 p24).
        iDestruct 1 as (p1') "[Hpc1 #Hp13]"; iDestruct 1 as (p2') "[Hpc2 #Hp24]".
        iDestruct ("H1" with "Hpc1 Hpc2") as (pc1' pc2' pt) "(H1 & H1' & Hpc1 & Hpc2)".
        iExists (iProto_map_cont (flip iProto_app p3) ∘ pc1'),
          (iProto_map_cont (flip iProto_app p3) ∘ pc2'), (pt <++> p3)%proto.
        rewrite -!iProto_app_message' /=. iSplitL "H1".
        { iIntros "!>". iRewrite "Hp13". iApply ("IH" with "H1").
          iApply iProto_le_refl. }
        iSplitL "H2 H1'".
        { iIntros "!>". iRewrite "Hp24". iApply ("IH" with "H1' H2"). }
        iSplitL "Hpc1"; auto.
    - iDestruct (iProto_le_recv_inv with "H1") as (pc1) "[Hp1 H1]".
      iRewrite "Hp1"; clear p1.
      rewrite !iProto_app_message'. iEval (rewrite iProto_le_unfold).
      iRight. iExists _, _, _, _; do 2 (iSplit; [done|]); simpl.
      iIntros (v p13). iDestruct 1 as (p1') "[Hpc #Hp13]".
      iDestruct ("H1" with "Hpc") as (p2'') "[H1 Hpc]".
      iExists (p2'' <++> p4)%proto. iSplitR "Hpc"; [|eauto].
      iIntros "!>". iRewrite "Hp13". by iApply ("IH" with "H1").
  Qed.

  (** ** Lemmas about the auxiliary definitions and invariants *)
  Global Instance iProto_interp_aux_ne n vsl vsr :
    NonExpansive2 (iProto_interp_aux (Σ:=Σ) (V:=V) n vsl vsr).
  Proof. revert vsl vsr. induction n; solve_proper. Qed.
  Global Instance iProto_interp_aux_proper n vsl vsr :
    Proper ((≡) ==> (≡) ==> (≡)) (iProto_interp_aux (Σ:=Σ) (V:=V) n vsl vsr).
  Proof. apply (ne_proper_2 _). Qed.
  Global Instance iProto_interp_ne vsl vsr :
    NonExpansive2 (iProto_interp (Σ:=Σ) (V:=V) vsl vsr).
  Proof. solve_proper. Qed.
  Global Instance iProto_interp_proper vsl vsr :
    Proper ((≡) ==> (≡) ==> (≡)) (iProto_interp (Σ:=Σ) (V:=V) vsl vsr).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance iProto_unfold_ne : NonExpansive (iProto_unfold (Σ:=Σ) (V:=V)).
  Proof. solve_proper. Qed.
  Global Instance iProto_own_frag_ne γ s : NonExpansive (iProto_own_frag γ s).
  Proof. solve_proper. Qed.

  Lemma iProto_own_auth_agree γ s p p' :
    iProto_own_auth γ s p -∗ iProto_own_frag γ s p' -∗ ▷ (p ≡ p').
  Proof.
    iIntros "H● H◯". iDestruct (own_valid_2 with "H● H◯") as "H✓".
    iDestruct (excl_auth_agreeI with "H✓") as "H✓".
    iDestruct (bi.later_eq_1 with "H✓") as "H✓"; iNext.
    rewrite /iProto_unfold. assert (∀ p, proto_map iProp_unfold iProp_fold
        (proto_map iProp_fold iProp_unfold p) ≡ p) as help.
    { intros p''. rewrite -proto_map_compose -{2}(proto_map_id p'').
      apply proto_map_ext=> // pc /=; by rewrite iProp_fold_unfold. }
    rewrite -{2}(help p). iRewrite "H✓". by rewrite help.
  Qed.

  Lemma iProto_own_auth_update γ s p p' p'' :
    iProto_own_auth γ s p -∗ iProto_own_frag γ s p' ==∗
    iProto_own_auth γ s p'' ∗ iProto_own_frag γ s p''.
  Proof.
    iIntros "H● H◯". iDestruct (own_update_2 with "H● H◯") as "H".
    { eapply (excl_auth_update _ _ (Next (iProto_unfold p''))). }
    by rewrite own_op.
  Qed.

  (* TODO: Move somewhere else *)
  Lemma false_disj_cong (P Q Q' : iProp Σ) :
    (P ⊢ False) → (Q ⊣⊢ Q') → (P ∨ Q ⊣⊢ Q').
  Proof. intros HP ->. apply (anti_symm _). by rewrite HP left_id. auto. Qed.

  Lemma pure_sep_cong (φ1 φ2 : Prop) (P1 P2 : iProp Σ) :
    (φ1 ↔ φ2) → (φ1 → φ2 → P1 ⊣⊢ P2) → (⌜φ1⌝ ∗ P1) ⊣⊢ (⌜φ2⌝ ∗ P2).
  Proof. intros -> HP. iSplit; iDestruct 1 as (Hϕ) "H"; rewrite HP; auto. Qed.

  Lemma iProto_interp_unfold vsl vsr pl pr :
    iProto_interp vsl vsr pl pr ⊣⊢
      (∃ p,
        ⌜ vsl = [] ⌝ ∗
        ⌜ vsr = [] ⌝ ∗
        iProto_le p pl ∗
        iProto_le (iProto_dual p) pr) ∨
      (∃ vl vsl' pc pr',
        ⌜ vsl = vl :: vsl' ⌝ ∗
        iProto_le (proto_message Recv pc) pr ∗
        pc vl (Next pr') ∗
        iProto_interp vsl' vsr pl pr') ∨
      (∃ vr vsr' pc pl',
        ⌜ vsr = vr :: vsr' ⌝ ∗
        iProto_le (proto_message Recv pc) pl ∗
        pc vr (Next pl') ∗
        iProto_interp vsl vsr' pl' pr).
  Proof.
    rewrite {1}/iProto_interp. destruct vsl as [|vl vsl]; simpl.
    - destruct vsr as [|vr vsr]; simpl.
      + iSplit; first by auto.
        iDestruct 1 as "[H | [H | H]]"; first by auto.
        * iDestruct "H" as (? ? ? ? [=]) "_".
        * iDestruct "H" as (? ? ? ? [=]) "_".
      + symmetry. apply false_disj_cong.
        { iDestruct 1 as (? _ [=]) "_". }
        repeat first [apply pure_sep_cong; intros; simplify_eq/= | f_equiv];
          by rewrite ?Nat.add_succ_r.
    - symmetry. apply false_disj_cong.
      { iDestruct 1 as (? [=]) "_". }
      repeat first [apply pure_sep_cong; intros; simplify_eq/= | f_equiv];
        by rewrite ?Nat.add_succ_r.
  Qed.

  Lemma iProto_interp_nil p : ⊢ iProto_interp [] [] p (iProto_dual p).
  Proof.
    rewrite iProto_interp_unfold. iLeft. iExists p. do 2 (iSplit; [done|]).
    iSplitL; iApply iProto_le_refl.
  Qed.

  Lemma iProto_interp_flip vsl vsr pl pr :
    iProto_interp vsl vsr pl pr -∗ iProto_interp vsr vsl pr pl.
  Proof.
    remember (length vsl + length vsr) as n eqn:Hn.
    iInduction (lt_wf n) as [n _] "IH" forall (vsl vsr pl pr Hn); subst.
    rewrite !iProto_interp_unfold. iIntros "[H|[H|H]]".
    - iClear "IH". iDestruct "H" as (p -> ->) "[Hp Hp'] /=".
      iLeft. iExists (iProto_dual p). rewrite involutive. iFrame; auto.
    - iDestruct "H" as (vl vsl' pc' pr' ->) "(Hpr & Hpc' & H)".
      iRight; iRight. iExists vl, vsl', pc', pr'. iSplit; [done|]; iFrame.
      iApply ("IH" with "[%] [//] H"); simpl; lia.
    - iDestruct "H" as (vr vsr' pc' pl' ->) "(Hpl & Hpc' & H)".
      iRight; iLeft. iExists vr, vsr', pc', pl'. iSplit; [done|]; iFrame.
      iApply ("IH" with "[%] [//] H"); simpl; lia.
  Qed.

  Lemma iProto_interp_le_l vsl vsr pl pl' pr :
    iProto_interp vsl vsr pl pr -∗ iProto_le pl pl' -∗ iProto_interp vsl vsr pl' pr.
  Proof.
    remember (length vsl + length vsr) as n eqn:Hn.
    iInduction (lt_wf n) as [n _] "IH" forall (vsl vsr pl pr Hn); subst.
    rewrite !iProto_interp_unfold. iIntros "[H|[H|H]] Hle".
    - iClear "IH". iDestruct "H" as (p -> ->) "[Hp Hp'] /=".
      iLeft. iExists p. do 2 (iSplit; [done|]). iFrame "Hp'".
      by iApply (iProto_le_trans with "Hp").
    - iDestruct "H" as (vl vsl' pc' pr' ->) "(Hpr & Hpc' & H)".
      iRight; iLeft. iExists vl, vsl', pc', pr'. iSplit; [done|]; iFrame.
      iApply ("IH" with "[%] [//] H Hle"); simpl; lia.
    - iClear "IH". iDestruct "H" as (vr vsr' pc' pl'' ->) "(Hpl & Hpc' & H)".
      iRight; iRight. iExists vr, vsr', pc', pl''. iSplit; [done|]; iFrame.
      by iApply (iProto_le_trans with "Hpl").
  Qed.
  Lemma iProto_interp_le_r vsl vsr pl pr pr' :
    iProto_interp vsl vsr pl pr -∗ iProto_le pr pr' -∗ iProto_interp vsl vsr pl pr'.
  Proof.
    iIntros "H Hle". iApply iProto_interp_flip.
    iApply (iProto_interp_le_l with "[H] Hle"). by iApply iProto_interp_flip.
  Qed.

  Lemma iProto_interp_send vl pcl vsl vsr pl pr pl' :
    iProto_interp vsl vsr pl pr -∗
    iProto_le pl (proto_message Send pcl) -∗
    pcl vl (Next pl') -∗
    ▷^(length vsr) iProto_interp (vsl ++ [vl]) vsr pl' pr.
  Proof.
    iIntros "H Hle". iDestruct (iProto_interp_le_l with "H Hle") as "H".
    clear pl. iIntros "Hpcl". remember (length vsl + length vsr) as n eqn:Hn.
    iInduction (lt_wf n) as [n _] "IH" forall (pcl vsl vsr pr pl' Hn); subst.
    rewrite {1}iProto_interp_unfold. iDestruct "H" as "[H|[H|H]]".
    - iClear "IH". iDestruct "H" as (p -> ->) "[Hp Hp'] /=".
      iDestruct (iProto_le_dual with "Hp") as "Hp".
      iDestruct (iProto_le_trans with "Hp Hp'") as "Hp".
      rewrite iProto_dual_message' /=.
      iApply iProto_interp_unfold. iRight; iLeft.
      iExists vl, [], _, (iProto_dual pl'). iSplit; [done|]. iFrame "Hp"; simpl.
      iSplitL; [by auto|]. iApply iProto_interp_nil.
    - iDestruct "H" as (vl' vsl' pc' pr' ->) "(Hpr & Hpc' & H)".
      iDestruct ("IH" with "[%] [//] H Hpcl") as "H"; [simpl; lia|].
      iNext. iApply (iProto_interp_le_r with "[-Hpr] Hpr"); clear pr.
      iApply iProto_interp_unfold. iRight; iLeft.
      iExists vl', (vsl' ++ [vl]), pc', pr'. iFrame.
      iSplit; [done|]. iApply iProto_le_refl.
    - iDestruct "H" as (vr' vsr' pc' pl'' ->) "(Hle & Hpcl' & H) /=".
      iDestruct (iProto_le_send_inv with "Hle") as (a pcl') "[Hpc Hle]".
      iDestruct (proto_message_equivI with "Hpc") as (<-) "Hpc".
      iRewrite ("Hpc" $! vr' (Next pl'')) in "Hpcl'"; clear pc'.
      iDestruct ("Hle" with "Hpcl' Hpcl")
        as (pc1 pc2 pt) "(Hpl'' & Hpl' & Hpc1 & Hpc2)".
      iNext. iDestruct (iProto_interp_le_l with "H Hpl''") as "H".
      iDestruct ("IH" with "[%] [//] H Hpc1") as "H"; [simpl; lia|..].
      iNext. iApply iProto_interp_unfold. iRight; iRight.
      iExists vr', vsr', _, pt. iSplit; [done|]. by iFrame.
  Qed.

  Lemma iProto_interp_recv vl vsl vsr pl pr pcr :
    iProto_interp (vl :: vsl) vsr pl pr -∗
    iProto_le pr (proto_message Recv pcr) -∗
    ∃ pr, pcr vl (Next pr) ∗ ▷ iProto_interp vsl vsr pl pr.
  Proof.
    iIntros "H Hle". iDestruct (iProto_interp_le_r with "H Hle") as "H".
    clear pr. remember (length vsr) as n eqn:Hn.
    iInduction (lt_wf n) as [n _] "IH" forall (vsr pl Hn); subst.
    rewrite !iProto_interp_unfold. iDestruct "H" as "[H|[H|H]]".
    - iClear "IH". iDestruct "H" as (p [=]) "_".
    - iClear "IH". iDestruct "H" as (vl' vsl' pc' pr' [= -> ->]) "(Hpr & Hpc' & Hinterp)".
      iDestruct (iProto_le_recv_inv with "Hpr") as (pc'') "[Hpc Hpr]".
      iDestruct (proto_message_equivI with "Hpc") as (_) "{Hpc} #Hpc".
      iDestruct ("Hpr" $! vl' pr' with "[Hpc']") as (pr'') "[Hler Hpr]".
      { by iRewrite -("Hpc" $! vl' (Next pr')). }
      iExists pr''. iFrame "Hpr".
      by iApply (iProto_interp_le_r with "Hinterp").
    - iDestruct "H" as (vr vsr' pc' pl'' ->) "(Hpl & Hpc' & Hinterp)".
      iDestruct ("IH" with "[%] [//] Hinterp") as (pr) "[Hpc Hinterp]"; [simpl; lia|].
      iExists pr. iFrame "Hpc".
      iApply iProto_interp_unfold. iRight; iRight. eauto 20 with iFrame.
  Qed.

  Global Instance iProto_own_ne γ s : NonExpansive (iProto_own γ s).
  Proof. solve_proper. Qed.
  Global Instance iProto_own_proper γ s : Proper ((≡) ==> (≡)) (iProto_own γ s).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_own_le γ s p1 p2 :
    iProto_own γ s p1 -∗ ▷ iProto_le p1 p2 -∗ iProto_own γ s p2.
  Proof.
    iDestruct 1 as (p1') "[Hle H]". iIntros "Hle'".
    iExists p1'. iFrame "H". by iApply (iProto_le_trans with "Hle").
  Qed.

  Lemma iProto_init p :
    ⊢ |==> ∃ γ,
      iProto_ctx γ [] [] ∗
      iProto_own γ Left p ∗ iProto_own γ Right (iProto_dual p).
  Proof.
    iMod (own_alloc (●E (Next (iProto_unfold p)) ⋅
      ◯E (Next (iProto_unfold p)))) as (lγ) "[H●l H◯l]".
    { by apply excl_auth_valid. }
    iMod (own_alloc (●E (Next (iProto_unfold (iProto_dual p))) ⋅
      ◯E (Next (iProto_unfold (iProto_dual p))))) as (rγ) "[H●r H◯r]".
    { by apply excl_auth_valid. }
    pose (ProtName lγ rγ) as γ. iModIntro. iExists γ. iSplitL "H●l H●r".
    { iExists p, (iProto_dual p). iFrame. iApply iProto_interp_nil. }
    iSplitL "H◯l"; iExists _; iFrame; iApply iProto_le_refl.
  Qed.

  Lemma iProto_send_l {TT} γ (pc : TT → V * iProp Σ * iProto Σ V) (x : TT) vsr vsl :
    iProto_ctx γ vsl vsr -∗
    iProto_own γ Left (iProto_message Send pc) -∗
    (pc x).1.2 ==∗
      ▷^(length vsr) iProto_ctx γ (vsl ++ [(pc x).1.1]) vsr ∗
      iProto_own γ Left (pc x).2.
  Proof.
    rewrite iProto_message_eq. iDestruct 1 as (pl pr) "(H●l & H●r & Hinterp)".
    iDestruct 1 as (p) "[Hle H◯]". iIntros "Hpc".
    iDestruct (iProto_own_auth_agree with "H●l H◯") as "#Hp".
    iAssert (▷ iProto_le pl (iProto_message_def Send pc))%I
      with "[Hle]" as "{Hp} Hle"; first (iNext; by iRewrite "Hp").
    iDestruct (iProto_interp_send ((pc x).1.1) with "Hinterp Hle [Hpc]") as "Hinterp".
    { simpl. auto. }
    iMod (iProto_own_auth_update _ _ _ _ (pc x).2 with "H●l H◯") as "[H●l H◯]".
    iIntros "!>". iSplitR "H◯".
    - iIntros "!>". iExists (pc x).2, pr. iFrame.
    - iExists (pc x).2. iFrame. iApply iProto_le_refl.
  Qed.

  Lemma iProto_send_r {TT} γ (pc : TT → V * iProp Σ * iProto Σ V) (x : TT) vsr vsl :
    iProto_ctx γ vsl vsr -∗
    iProto_own γ Right (iProto_message Send pc) -∗
    (pc x).1.2 ==∗
      ▷^(length vsl) iProto_ctx γ vsl (vsr ++ [(pc x).1.1]) ∗
      iProto_own γ Right (pc x).2.
  Proof.
    rewrite iProto_message_eq. iDestruct 1 as (pl pr) "(H●l & H●r & Hinterp)".
    iDestruct 1 as (p) "[Hle H◯]". iIntros "Hpc".
    iDestruct (iProto_own_auth_agree with "H●r H◯") as "#Hp".
    iAssert (▷ iProto_le pr (iProto_message_def Send pc))%I
      with "[Hle]" as "{Hp} Hle"; first (iNext; by iRewrite "Hp").
    iDestruct (iProto_interp_flip with "Hinterp") as "Hinterp".
    iDestruct (iProto_interp_send ((pc x).1.1) with "Hinterp Hle [Hpc]") as "Hinterp".
    { simpl. auto. }
    iMod (iProto_own_auth_update _ _ _ _ (pc x).2 with "H●r H◯") as "[H●r H◯]".
    iIntros "!>". iSplitR "H◯".
    - iIntros "!>". iExists pl, (pc x).2. iFrame. by iApply iProto_interp_flip.
    - iExists (pc x).2. iFrame. iApply iProto_le_refl.
  Qed.

  Lemma iProto_recv_l {TT} γ (pc : TT → V * iProp Σ * iProto Σ V) vr vsr vsl :
    iProto_ctx γ vsl (vr :: vsr) -∗
    iProto_own γ Left (iProto_message Recv pc) ==∗
    ▷ (iProto_ctx γ vsl vsr ∗
       ∃ (x : TT),
         ⌜ vr = (pc x).1.1 ⌝ ∗
         iProto_own γ Left (pc x).2 ∗
         ▷ (pc x).1.2).
  Proof.
    rewrite iProto_message_eq. iDestruct 1 as (pl pr) "(H●l & H●r & Hinterp)".
    iDestruct 1 as (p) "[Hle H◯]".
    iDestruct (iProto_own_auth_agree with "H●l H◯") as "#Hp".
    iDestruct (iProto_interp_flip with "Hinterp") as "Hinterp".
    iDestruct (iProto_interp_recv with "Hinterp [Hle]") as (q) "[Hpc Hinterp]".
    { iNext. by iRewrite "Hp". }
    iMod (iProto_own_auth_update _ _ _ _ q with "H●l H◯") as "[H●l H◯]".
    iIntros "!> !>". iDestruct "Hpc" as (x ->) "[Hpc #Hq] /=".
    iSplitR "H◯ Hpc".
    - iExists q, pr. iFrame. by iApply iProto_interp_flip.
    - iExists x. iSplit; [done|]. iFrame "Hpc".
      iExists q. iIntros "{$H◯} !>". iRewrite "Hq". iApply iProto_le_refl.
  Qed.

  Lemma iProto_recv_r {TT} γ (pc : TT → V * iProp Σ * iProto Σ V) vl vsr vsl :
    iProto_ctx γ (vl :: vsl) vsr -∗
    iProto_own γ Right (iProto_message Recv pc) ==∗
    ▷ (iProto_ctx γ vsl vsr ∗
       ∃ (x : TT),
         ⌜ vl = (pc x).1.1 ⌝ ∗
         iProto_own γ Right (pc x).2 ∗
         ▷ (pc x).1.2).
  Proof.
    rewrite iProto_message_eq. iDestruct 1 as (pl pr) "(H●l & H●r & Hinterp)".
    iDestruct 1 as (p) "[Hle H◯]".
    iDestruct (iProto_own_auth_agree with "H●r H◯") as "#Hp".
    iDestruct (iProto_interp_recv with "Hinterp [Hle]") as (q) "[Hpc Hinterp]".
    { iNext. by iRewrite "Hp". }
    iMod (iProto_own_auth_update _ _ _ _ q with "H●r H◯") as "[H●r H◯]".
    iIntros "!> !>". iDestruct "Hpc" as (x ->) "[Hpc #Hq] /=".
    iSplitR "H◯ Hpc".
    - iExists pl, q. iFrame.
    - iExists x. iSplit; [done|]. iFrame "Hpc".
      iExists q. iIntros "{$H◯} !>". iRewrite "Hq". iApply iProto_le_refl.
  Qed.
End proto.

Typeclasses Opaque iProto_ctx iProto_own.