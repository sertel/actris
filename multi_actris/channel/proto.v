(** This file defines the core of the Actris logic: It defines dependent
separation protocols and the various operations on it like dual, append, and
branching.

Dependent separation protocols [iProto] are defined by instantiating the
parameterized version in [proto_model] with the type of propositions [iProp] of Iris.
We define ways of constructing instances of the instantiated type via two
constructors:
- [iProto_end], which is identical to [proto_end].
- [iProto_message], which takes an [action] and an [iMsg]. The type [iMsg] is a
  sequence of binders [iMsg_exist], terminated by the payload constructed with
  [iMsg_base] based on arguments [v], [P] and [prot], which are the value, the
  carried proposition and the [iProto] tail, respectively.

For convenience sake, we provide the following notations:
- [END], which is simply [iProto_end].
- [∃ x, m], which is [iMsg_exist] with argument [m].
- [MSG v {{ P }}; prot], which is [iMsg_Base] with arguments [v], [P] and [prot].
- [<a> m], which is [iProto_message] with arguments [a] and [m].

We also include custom notation to more easily construct complete constructions:
- [<a x1 .. xn> m], which is [<a> ∃ x1, .. ∃ xn, m].
- [<a x1 .. xn> MSG v; {{ P }}; prot], which constructs a full protocol.

Futhermore, we define the following operations:
- [iProto_dual], which turns all [Send] of a protocol into [Recv] and vice-versa.
- [iProto_app], which appends two protocols.

In addition we define the subprotocol relation [iProto_le] [⊑], which generalises
the following inductive definition for asynchronous subtyping on session types:

                 p1 <: p2           p1 <: p2          p1 <: !B.p3    ?A.p3 <: p2
----------   ----------------   ----------------     ----------------------------
end <: end    !A.p1 <: !A.p2     ?A.p1 <: ?A.p2             ?A.p1 <: !B.p2

Example:

!R <: !R  ?Q <: ?Q      ?Q <: ?Q
-------------------  --------------
?Q.!R <: !R.?Q       ?P.?Q <: ?P.?Q
------------------------------------
   ?P.?Q.!R <: !R.?P.?Q

Lastly, relevant type classes instances are defined for each of the above
notions, such as contractiveness and non-expansiveness, after which the
specifications of the message-passing primitives are defined in terms of the
protocol connectives. *)
From iris.algebra Require Import gmap excl_auth gmap_view.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export lib.iprop.
From iris.base_logic Require Import lib.own.
From iris.program_logic Require Import language.
From multi_actris.channel Require Import proto_model.
Set Default Proof Using "Type".
Export action.

(** * Setup of Iris's cameras *)
Class protoG Σ V :=
  protoG_authG ::
    inG Σ (gmap_viewR natO
      (optionUR (exclR (laterO (proto (leibnizO V) (iPropO Σ) (iPropO Σ)))))).

Definition protoΣ V := #[
  GFunctor ((gmap_viewRF natO (optionRF (exclRF (laterOF (protoOF (leibnizO V) idOF idOF))))))
].
Global Instance subG_chanΣ {Σ V} : subG (protoΣ V) Σ → protoG Σ V.
Proof. solve_inG. Qed.

(** * Types *)
Definition iProto Σ V := proto V (iPropO Σ) (iPropO Σ).
Declare Scope proto_scope.
Delimit Scope proto_scope with proto.
Bind Scope proto_scope with iProto.
Local Open Scope proto.

(** * Messages *)
Section iMsg.
  Set Primitive Projections.
  Record iMsg Σ V := IMsg { iMsg_car : V → laterO (iProto Σ V) -n> iPropO Σ }.
End iMsg.
Arguments IMsg {_ _} _.
Arguments iMsg_car {_ _} _.

Declare Scope msg_scope.
Delimit Scope msg_scope with msg.
Bind Scope msg_scope with iMsg.
Global Instance iMsg_inhabited {Σ V} : Inhabited (iMsg Σ V) := populate (IMsg inhabitant).

Section imsg_ofe.
  Context {Σ : gFunctors} {V : Type}.

  Instance iMsg_equiv : Equiv (iMsg Σ V) := λ m1 m2,
    ∀ w p, iMsg_car m1 w p ≡ iMsg_car m2 w p.
  Instance iMsg_dist : Dist (iMsg Σ V) := λ n m1 m2,
    ∀ w p, iMsg_car m1 w p ≡{n}≡ iMsg_car m2 w p.

  Lemma iMsg_ofe_mixin : OfeMixin (iMsg Σ V).
  Proof. by apply (iso_ofe_mixin (iMsg_car : _ → V -d> _ -n> _)). Qed.
  Canonical Structure iMsgO := Ofe (iMsg Σ V) iMsg_ofe_mixin.

  Global Instance iMsg_cofe : Cofe iMsgO.
  Proof. by apply (iso_cofe (IMsg : (V -d> _ -n> _) → _) iMsg_car). Qed.
End imsg_ofe.

Program Definition iMsg_base_def {Σ V}
    (v : V) (P : iProp Σ) (p : iProto Σ V) : iMsg Σ V :=
  IMsg (λ v', λne p', ⌜ v = v' ⌝ ∗ Next p ≡ p' ∗ P)%I.
Next Obligation. solve_proper. Qed.
Definition iMsg_base_aux : seal (@iMsg_base_def). by eexists. Qed.
Definition iMsg_base := iMsg_base_aux.(unseal).
Definition iMsg_base_eq : @iMsg_base = @iMsg_base_def := iMsg_base_aux.(seal_eq).
Arguments iMsg_base {_ _} _%V _%I _%proto.
Global Instance: Params (@iMsg_base) 3 := {}.

Program Definition iMsg_exist_def {Σ V A} (m : A → iMsg Σ V) : iMsg Σ V :=
  IMsg (λ v', λne p', ∃ x, iMsg_car (m x) v' p')%I.
Next Obligation. solve_proper. Qed.
Definition iMsg_exist_aux : seal (@iMsg_exist_def). by eexists. Qed.
Definition iMsg_exist := iMsg_exist_aux.(unseal).
Definition iMsg_exist_eq : @iMsg_exist = @iMsg_exist_def := iMsg_exist_aux.(seal_eq).
Arguments iMsg_exist {_ _ _} _%msg.
Global Instance: Params (@iMsg_exist) 3 := {}.

Definition iMsg_texist {Σ V} {TT : tele} (m : TT → iMsg Σ V) : iMsg Σ V :=
  tele_fold (@iMsg_exist Σ V) (λ x, x) (tele_bind m).
Arguments iMsg_texist {_ _ !_} _%msg /.

Notation "'MSG' v {{ P } } ; p" := (iMsg_base v P p)
  (at level 200, v at level 20, right associativity,
   format "MSG  v  {{  P  } } ;  p") : msg_scope.
Notation "'MSG' v ; p" := (iMsg_base v True p)
  (at level 200, v at level 20, right associativity,
   format "MSG  v ;  p") : msg_scope.
Notation "∃ x .. y , m" :=
  (iMsg_exist (λ x, .. (iMsg_exist (λ y, m)) ..)%msg) : msg_scope.
Notation "'∃..' x .. y , m" :=
  (iMsg_texist (λ x, .. (iMsg_texist (λ y, m)) .. )%msg)
  (at level 200, x binder, y binder, right associativity,
   format "∃..  x  ..  y ,  m") : msg_scope.

Lemma iMsg_texist_exist {Σ V} {TT : tele} w lp (m : TT → iMsg Σ V) :
  iMsg_car (∃.. x, m x)%msg w lp ⊣⊢ (∃.. x, iMsg_car (m x) w lp).
Proof.
  rewrite /iMsg_texist iMsg_exist_eq.
  induction TT as [|T TT IH]; simpl; [done|]. f_equiv=> x. apply IH.
Qed.

(** * Operators *)
Definition iProto_end_def {Σ V} : iProto Σ V := proto_end.
Definition iProto_end_aux : seal (@iProto_end_def). by eexists. Qed.
Definition iProto_end := iProto_end_aux.(unseal).
Definition iProto_end_eq : @iProto_end = @iProto_end_def := iProto_end_aux.(seal_eq).
Arguments iProto_end {_ _}.

Definition iProto_message_def {Σ V} (a : action) (m : iMsg Σ V) : iProto Σ V :=
  proto_message a (iMsg_car m).
Definition iProto_message_aux : seal (@iProto_message_def). by eexists. Qed.
Definition iProto_message := iProto_message_aux.(unseal).
Definition iProto_message_eq :
  @iProto_message = @iProto_message_def := iProto_message_aux.(seal_eq).
Arguments iProto_message {_ _} _ _%msg.
Global Instance: Params (@iProto_message) 3 := {}.

Notation "'END'" := iProto_end : proto_scope.

Notation "< a > m" := (iProto_message a m)
  (at level 200, a at level 10, m at level 200,
   format "< a >  m") : proto_scope.
Notation "< a @ x1 .. xn > m" := (iProto_message a (∃ x1, .. (∃ xn, m) ..))
  (at level 200, a at level 10, x1 closed binder, xn closed binder, m at level 200,
   format "< a  @  x1  ..  xn >  m") : proto_scope.
Notation "< a @.. x1 .. xn > m" := (iProto_message a (∃.. x1, .. (∃.. xn, m) ..))
  (at level 200, a at level 10, x1 closed binder, xn closed binder, m at level 200,
   format "< a  @..  x1  ..  xn >  m") : proto_scope.

Class MsgTele {Σ V} {TT : tele} (m : iMsg Σ V)
    (tv : TT -t> V) (tP : TT -t> iProp Σ) (tp : TT -t> iProto Σ V) :=
  msg_tele : m ≡ (∃.. x, MSG tele_app tv x {{ tele_app tP x }}; tele_app tp x)%msg.
Global Hint Mode MsgTele ! ! - ! - - - : typeclass_instances.

(** * Operations *)
Program Definition iMsg_map {Σ V}
    (rec : iProto Σ V → iProto Σ V) (m : iMsg Σ V) : iMsg Σ V :=
  IMsg (λ v, λne p1', ∃ p1, iMsg_car m v (Next p1) ∗ p1' ≡ Next (rec p1))%I.
Next Obligation. solve_proper. Qed.

Program Definition iProto_map_app_aux {Σ V}
    (f : action → action) (p2 : iProto Σ V)
    (rec : iProto Σ V -n> iProto Σ V) : iProto Σ V -n> iProto Σ V := λne p,
  proto_elim p2 (λ a m,
    proto_message (f a) (iMsg_car (iMsg_map rec (IMsg m)))) p.
Next Obligation.
  intros Σ V f p2 rec n p1 p1' Hp. apply proto_elim_ne=> // a m1 m2 Hm.
  apply proto_message_ne=> v p' /=. by repeat f_equiv.
Qed.

Global Instance iProto_map_app_aux_contractive {Σ V} f (p2 : iProto Σ V) :
  Contractive (iProto_map_app_aux f p2).
Proof.
  intros n rec1 rec2 Hrec p1; simpl. apply proto_elim_ne=> // a m1 m2 Hm.
  apply proto_message_ne=> v p' /=. by repeat (f_contractive || f_equiv).
Qed.

Definition iProto_map_app {Σ V} (f : action → action)
    (p2 : iProto Σ V) : iProto Σ V -n> iProto Σ V :=
  fixpoint (iProto_map_app_aux f p2).

Definition iProto_app_def {Σ V} (p1 p2 : iProto Σ V) : iProto Σ V :=
  iProto_map_app id p2 p1.
Definition iProto_app_aux : seal (@iProto_app_def). Proof. by eexists. Qed.
Definition iProto_app := iProto_app_aux.(unseal).
Definition iProto_app_eq : @iProto_app = @iProto_app_def := iProto_app_aux.(seal_eq).
Arguments iProto_app {_ _} _%proto _%proto.
Global Instance: Params (@iProto_app) 2 := {}.
Infix "<++>" := iProto_app (at level 60) : proto_scope.
Notation "m <++> p" := (iMsg_map (flip iProto_app p) m) : msg_scope.

Definition iProto_dual_def {Σ V} (p : iProto Σ V) : iProto Σ V :=
  iProto_map_app action_dual proto_end p.
Definition iProto_dual_aux : seal (@iProto_dual_def). Proof. by eexists. Qed.
Definition iProto_dual := iProto_dual_aux.(unseal).
Definition iProto_dual_eq :
  @iProto_dual = @iProto_dual_def := iProto_dual_aux.(seal_eq).
Arguments iProto_dual {_ _} _%proto.
Global Instance: Params (@iProto_dual) 2 := {}.
Notation iMsg_dual := (iMsg_map iProto_dual).

Definition iProto_dual_if {Σ V} (d : bool) (p : iProto Σ V) : iProto Σ V :=
  if d then iProto_dual p else p.
Arguments iProto_dual_if {_ _} _ _%proto.
Global Instance: Params (@iProto_dual_if) 3 := {}.

(** * Proofs *)
Section proto.
  Context `{!protoG Σ V}.
  Implicit Types v : V.
  Implicit Types p pl pr : iProto Σ V.
  Implicit Types m : iMsg Σ V.

  (** ** Equality *)
  Lemma iProto_case p : p ≡ END ∨ ∃ t n m, p ≡ <(t,n)> m.
  Proof.
    rewrite iProto_message_eq iProto_end_eq.
    destruct (proto_case p) as [|([a n]&m&?)]; [by left|right].
    by exists a, n, (IMsg m).
  Qed.
  Lemma iProto_message_equivI `{!BiInternalEq SPROP} a1 a2 m1 m2 :
    (<a1> m1) ≡ (<a2> m2) ⊣⊢@{SPROP} ⌜ a1 = a2 ⌝ ∧
      (∀ v lp, iMsg_car m1 v lp ≡ iMsg_car m2 v lp).
  Proof. rewrite iProto_message_eq. apply proto_message_equivI. Qed.

  Lemma iProto_message_end_equivI `{!BiInternalEq SPROP} a m :
    (<a> m) ≡ END ⊢@{SPROP} False.
  Proof. rewrite iProto_message_eq iProto_end_eq. apply proto_message_end_equivI. Qed.
  Lemma iProto_end_message_equivI `{!BiInternalEq SPROP} a m :
    END ≡ (<a> m) ⊢@{SPROP} False.
  Proof. by rewrite internal_eq_sym iProto_message_end_equivI. Qed.

  (** ** Non-expansiveness of operators *)
  Global Instance iMsg_car_proper :
    Proper (iMsg_equiv ==> (=) ==> (≡) ==> (≡)) (iMsg_car (Σ:=Σ) (V:=V)).
  Proof.
    intros m1 m2 meq v1 v2 veq p1 p2 peq. rewrite meq.
    f_equiv; [ by f_equiv | done ].
  Qed.
  Global Instance iMsg_car_ne n :
    Proper (iMsg_dist n ==> (=) ==> (dist n) ==> (dist n)) (iMsg_car (Σ:=Σ) (V:=V)).
  Proof.
    intros m1 m2 meq v1 v2 veq p1 p2 peq. rewrite meq.
    f_equiv; [ by f_equiv | done ].
  Qed.

  Global Instance iMsg_contractive v n :
    Proper (dist n ==> dist_later n ==> dist n) (iMsg_base (Σ:=Σ) (V:=V) v).
  Proof. rewrite iMsg_base_eq=> P1 P2 HP p1 p2 Hp w q /=. solve_contractive. Qed.
  Global Instance iMsg_ne v : NonExpansive2 (iMsg_base (Σ:=Σ) (V:=V) v).
  Proof. rewrite iMsg_base_eq=> P1 P2 HP p1 p2 Hp w q /=. solve_proper. Qed.
  Global Instance iMsg_proper v :
    Proper ((≡) ==> (≡) ==> (≡)) (iMsg_base (Σ:=Σ) (V:=V) v).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance iMsg_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (@iMsg_exist Σ V A).
  Proof. rewrite iMsg_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.
  Global Instance iMsg_exist_proper A :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@iMsg_exist Σ V A).
  Proof. rewrite iMsg_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.

  Global Instance msg_tele_base (v:V) (P : iProp Σ) (p : iProto Σ V) :
    MsgTele (TT:=TeleO) (MSG v {{ P }}; p) v P p.
  Proof. done. Qed.
  Global Instance msg_tele_exist {A} {TT : A → tele} (m : A → iMsg Σ V) tv tP tp :
  (∀ x, MsgTele (TT:=TT x) (m x) (tv x) (tP x) (tp x)) →
  MsgTele (TT:=TeleS TT) (∃ x, m x) tv tP tp.
  Proof. intros Hm. rewrite /MsgTele /=. f_equiv=> x. apply Hm. Qed.

  Global Instance iProto_message_ne a :
    NonExpansive (iProto_message (Σ:=Σ) (V:=V) a).
  Proof. rewrite iProto_message_eq. solve_proper. Qed.
  Global Instance iProto_message_proper a :
    Proper ((≡) ==> (≡)) (iProto_message (Σ:=Σ) (V:=V) a).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_message_equiv {TT1 TT2 : tele} a1 a2
        (m1 m2 : iMsg Σ V)
        (v1 : TT1 -t> V) (v2 : TT2 -t> V)
        (P1 : TT1 -t> iProp Σ) (P2 : TT2 -t> iProp Σ)
        (prot1 : TT1 -t> iProto Σ V) (prot2 : TT2 -t> iProto Σ V) :
    MsgTele m1 v1 P1 prot1 →
    MsgTele m2 v2 P2 prot2 →
    ⌜ a1 = a2 ⌝ -∗
    (■ ∀.. (xs1 : TT1), tele_app P1 xs1 -∗
       ∃.. (xs2 : TT2), ⌜tele_app v1 xs1 = tele_app v2 xs2⌝ ∗
                        ▷ (tele_app prot1 xs1 ≡ tele_app prot2 xs2) ∗
                        tele_app P2 xs2) -∗
    (■ ∀.. (xs2 : TT2), tele_app P2 xs2 -∗
       ∃.. (xs1 : TT1), ⌜tele_app v1 xs1 = tele_app v2 xs2⌝ ∗
                        ▷ (tele_app prot1 xs1 ≡ tele_app prot2 xs2) ∗
                        tele_app P1 xs1) -∗
      (<a1> m1) ≡ (<a2> m2).
  Proof.
    iIntros (Hm1 Hm2 Heq) "#Heq1 #Heq2".
    unfold MsgTele in Hm1. rewrite Hm1. clear Hm1.
    unfold MsgTele in Hm2. rewrite Hm2. clear Hm2.
    rewrite iProto_message_eq proto_message_equivI.
    iSplit; [ done | ].
    iIntros (v p').
    do 2 rewrite iMsg_texist_exist.
    rewrite iMsg_base_eq /=.
    iApply prop_ext.
    iIntros "!>". iSplit.
    - iDestruct 1 as (xs1 Hveq1) "[Hrec1 HP1]".
      iDestruct ("Heq1" with "HP1") as (xs2 Hveq2) "[Hrec2 HP2]".
      iExists xs2. rewrite -Hveq1 Hveq2.
      iSplitR; [ done | ]. iSplitR "HP2"; [ | done ].
      iRewrite -"Hrec1". iApply later_equivI. iIntros "!>". by iRewrite "Hrec2".
    - iDestruct 1 as (xs2 Hveq2) "[Hrec2 HP2]".
      iDestruct ("Heq2" with "HP2") as (xs1 Hveq1) "[Hrec1 HP1]".
      iExists xs1. rewrite -Hveq2 Hveq1.
      iSplitR; [ done | ]. iSplitR "HP1"; [ | done ].
      iRewrite -"Hrec2". iApply later_equivI. iIntros "!>". by iRewrite "Hrec1".
  Qed.

  (** Helpers *)
  Lemma iMsg_map_base f v P p :
    NonExpansive f →
    iMsg_map f (MSG v {{ P }}; p) ≡ (MSG v {{ P }}; f p)%msg.
  Proof.
    rewrite iMsg_base_eq. intros ? v' p'; simpl. iSplit.
    - iDestruct 1 as (p'') "[(->&Hp&$) Hp']". iSplit; [done|].
      iRewrite "Hp'". iIntros "!>". by iRewrite "Hp".
    - iIntros "(->&Hp'&$)". iExists p. iRewrite -"Hp'". auto.
  Qed.
  Lemma iMsg_map_exist {A} f (m : A → iMsg Σ V) :
    iMsg_map f (∃ x, m x) ≡ (∃ x, iMsg_map f (m x))%msg.
  Proof.
    rewrite iMsg_exist_eq. intros v' p'; simpl. iSplit.
    - iDestruct 1 as (p'') "[H Hp']". iDestruct "H" as (x) "H"; auto.
    - iDestruct 1 as (x p'') "[Hm Hp']". auto.
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

  Lemma iProto_dual_end : iProto_dual (Σ:=Σ) (V:=V) END ≡ END.
  Proof.
    rewrite iProto_end_eq iProto_dual_eq /iProto_dual_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    by rewrite proto_elim_end.
  Qed.
  Lemma iProto_dual_message a m :
    iProto_dual (<a> m) ≡ <action_dual a> iMsg_dual m.
  Proof.
    rewrite iProto_message_eq iProto_dual_eq /iProto_dual_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    rewrite /iProto_message_def. rewrite ->proto_elim_message; [done|].
    intros a' m1 m2 Hm; f_equiv; solve_proper.
  Qed.
  Lemma iMsg_dual_base v P p :
    iMsg_dual (MSG v {{ P }}; p) ≡ (MSG v {{ P }}; iProto_dual p)%msg.
  Proof. apply iMsg_map_base, _. Qed.
  Lemma iMsg_dual_exist {A} (m : A → iMsg Σ V) :
    iMsg_dual (∃ x, m x) ≡ (∃ x, iMsg_dual (m x))%msg.
  Proof. apply iMsg_map_exist. Qed.

  Global Instance iProto_dual_involutive : Involutive (≡) (@iProto_dual Σ V).
  Proof.
    intros p. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p). destruct (iProto_case p) as [->|(a&n&m&->)].
    { by rewrite !iProto_dual_end. }
    rewrite !iProto_dual_message involutive.
    iApply iProto_message_equivI; iSplit; [done|]; iIntros (v p') "/=".
    iApply prop_ext; iIntros "!>"; iSplit.
    - iDestruct 1 as (pd) "[H Hp']". iRewrite "Hp'".
      iDestruct "H" as (pdd) "[H #Hpd]".
      iApply (internal_eq_rewrite); [|done]; iIntros "!>".
      iRewrite "Hpd". by iRewrite ("IH" $! pdd).
    - iIntros "H". destruct (Next_uninj p') as [p'' Hp']. iExists _.
      rewrite Hp'. iSplitL; [by auto|]. iIntros "!>". by iRewrite ("IH" $! p'').
  Qed.

  (** ** Append *)
  Global Instance iProto_app_end_l : LeftId (≡) END (@iProto_app Σ V).
  Proof.
    intros p. rewrite iProto_end_eq iProto_app_eq /iProto_app_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    by rewrite proto_elim_end.
  Qed.
  Lemma iProto_app_message a m p2 : (<a> m) <++> p2 ≡ <a> m <++> p2.
  Proof.
    rewrite iProto_message_eq iProto_app_eq /iProto_app_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    rewrite /iProto_message_def. rewrite ->proto_elim_message; [done|].
    intros a' m1 m2 Hm. f_equiv; solve_proper.
  Qed.

  Global Instance iProto_app_ne : NonExpansive2 (@iProto_app Σ V).
  Proof.
    assert (∀ n, Proper (dist n ==> (=) ==> dist n) (@iProto_app Σ V)).
    { intros n p1 p1' Hp1 p2 p2' <-. by rewrite iProto_app_eq /iProto_app_def Hp1. }
    assert (Proper ((≡) ==> (=) ==> (≡)) (@iProto_app Σ V)).
    { intros p1 p1' Hp1 p2 p2' <-. by rewrite iProto_app_eq /iProto_app_def Hp1. }
    intros n p1 p1' Hp1 p2 p2' Hp2. rewrite Hp1. clear p1 Hp1.
    revert p1'. induction (lt_wf n) as [n _ IH]; intros p1.
    destruct (iProto_case p1) as [->|(a&i&m&->)].
    { by rewrite !left_id. }
    rewrite !iProto_app_message. f_equiv=> v p' /=. do 4 f_equiv.
    f_contractive. apply IH; eauto using dist_le with lia.
  Qed.
  Global Instance iProto_app_proper : Proper ((≡) ==> (≡) ==> (≡)) (@iProto_app Σ V).
  Proof. apply (ne_proper_2 _). Qed.

  Lemma iMsg_app_base v P p1 p2 :
    ((MSG v {{ P }}; p1) <++> p2)%msg ≡ (MSG v {{ P }}; p1 <++> p2)%msg.
  Proof. apply: iMsg_map_base. Qed.
  Lemma iMsg_app_exist {A} (m : A → iMsg Σ V) p2 :
    ((∃ x, m x) <++> p2)%msg ≡ (∃ x, m x <++> p2)%msg.
  Proof. apply iMsg_map_exist. Qed.

  Global Instance iProto_app_end_r : RightId (≡) END (@iProto_app Σ V).
  Proof.
    intros p. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p). destruct (iProto_case p) as [->|(a&i&m&->)].
    { by rewrite left_id. }
    rewrite iProto_app_message.
    iApply iProto_message_equivI; iSplit; [done|]; iIntros (v p') "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (p1') "[H Hp']". iRewrite "Hp'".
      iApply (internal_eq_rewrite); [|done]; iIntros "!>".
      by iRewrite ("IH" $! p1').
    - iIntros "H". destruct (Next_uninj p') as [p'' Hp']. iExists p''.
      rewrite Hp'. iSplitL; [by auto|]. iIntros "!>". by iRewrite ("IH" $! p'').
  Qed.
  Global Instance iProto_app_assoc : Assoc (≡) (@iProto_app Σ V).
  Proof.
    intros p1 p2 p3. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p1). destruct (iProto_case p1) as [->|(a&i&m&->)].
    { by rewrite !left_id. }
    rewrite !iProto_app_message.
    iApply iProto_message_equivI; iSplit; [done|]; iIntros (v p123) "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (p1') "[H #Hp']".
      iExists (p1' <++> p2). iSplitL; [by auto|].
      iRewrite "Hp'". iIntros "!>". iApply "IH".
    - iDestruct 1 as (p12) "[H #Hp123]". iDestruct "H" as (p1') "[H #Hp12]".
      iExists p1'. iFrame "H". iRewrite "Hp123".
      iIntros "!>". iRewrite "Hp12". by iRewrite ("IH" $! p1').
  Qed.

  Lemma iProto_dual_app p1 p2 :
    iProto_dual (p1 <++> p2) ≡ iProto_dual p1 <++> iProto_dual p2.
  Proof.
    apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (p1 p2). destruct (iProto_case p1) as [->|(a&i&m&->)].
    { by rewrite iProto_dual_end !left_id. }
    rewrite iProto_dual_message !iProto_app_message iProto_dual_message /=.
    iApply iProto_message_equivI; iSplit; [done|]; iIntros (v p12) "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (p12d) "[H #Hp12]". iDestruct "H" as (p1') "[H #Hp12d]".
      iExists (iProto_dual p1'). iSplitL; [by auto|].
      iRewrite "Hp12". iIntros "!>". iRewrite "Hp12d". iApply "IH".
    - iDestruct 1 as (p1') "[H #Hp12]". iDestruct "H" as (p1d) "[H #Hp1']".
      iExists (p1d <++> p2). iSplitL; [by auto|].
      iRewrite "Hp12". iIntros "!>". iRewrite "Hp1'". by iRewrite ("IH" $! p1d p2).
  Qed.

End proto.

Global Instance iProto_inhabited {Σ V} : Inhabited (iProto Σ V) := populate END.

Definition can_step {Σ V} (rec : list (iProto Σ V) → iProp Σ)
           (ps : list (iProto Σ V)) (i j : nat) : iProp Σ :=
  ∀ m1 m2,
    (ps !!! i ≡ (<(Send, j)> m1)) -∗
    (ps !!! j ≡ (<(Recv, i)> m2)) -∗
    ∀ v p1, iMsg_car m1 v (Next p1) -∗
            ∃ p2, iMsg_car m2 v (Next p2) ∗
                  ▷ (rec (<[i:=p1]>(<[j:=p2]>ps))).

Definition valid_target {Σ V} (ps : list (iProto Σ V)) (i j : nat) : iProp Σ :=
  ∀ a m, (ps !!! i ≡ (<(a, j)> m)) -∗ ⌜is_Some (ps !! j)⌝.

Definition iProto_consistent_pre {Σ V} (rec : list (iProto Σ V) → iProp Σ)
  (ps : list (iProto Σ V)) : iProp Σ :=
  (∀ i j, valid_target ps i j) ∗ (∀ i j, can_step rec ps i j).

Global Instance iProto_consistent_pre_ne {Σ V}
       (rec : listO (iProto Σ V) -n> iPropO Σ) :
  NonExpansive (iProto_consistent_pre rec).
Proof. rewrite /iProto_consistent_pre /can_step /valid_target. solve_proper. Qed.

Program Definition iProto_consistent_pre' {Σ V}
  (rec : listO (iProto Σ V) -n> iPropO Σ) :
  listO (iProto Σ V) -n> iPropO Σ :=
  λne ps, iProto_consistent_pre (λ ps, rec ps) ps.

Local Instance iProto_consistent_pre_contractive {Σ V} : Contractive (@iProto_consistent_pre' Σ V).
Proof.
  rewrite /iProto_consistent_pre' /iProto_consistent_pre /can_step.
  solve_contractive.
Qed.

Definition iProto_consistent {Σ V} (ps : list (iProto Σ V)) : iProp Σ :=
  fixpoint iProto_consistent_pre' ps.

Arguments iProto_consistent {_ _} _%proto.
Global Instance: Params (@iProto_consistent) 1 := {}.

Global Instance iProto_consistent_ne {Σ V} : NonExpansive (@iProto_consistent Σ V).
Proof. solve_proper. Qed.
Global Instance iProto_consistent_proper {Σ V} : Proper ((≡) ==> (⊣⊢)) (@iProto_consistent Σ V).
Proof. solve_proper. Qed.

Lemma iProto_consistent_unfold {Σ V} (ps : list (iProto Σ V)) :
  iProto_consistent ps ≡ (iProto_consistent_pre iProto_consistent) ps.
Proof.
  apply: (fixpoint_unfold iProto_consistent_pre').
Qed.

(** * Protocol entailment *)
Definition iProto_le_pre {Σ V}
    (rec : iProto Σ V → iProto Σ V → iProp Σ) (p1 p2 : iProto Σ V) : iProp Σ :=
  (p1 ≡ END ∗ p2 ≡ END) ∨
  ∃ a1 a2 m1 m2,
    (p1 ≡ <a1> m1) ∗ (p2 ≡ <a2> m2) ∗
    match a1, a2 with
    | (Recv,i), (Recv,j) => ⌜i = j⌝ ∗ ∀ v p1',
       iMsg_car m1 v (Next p1') -∗ ∃ p2', ▷ rec p1' p2' ∗ iMsg_car m2 v (Next p2')
    | (Send,i), (Send,j) => ⌜i = j⌝ ∗ ∀ v p2',
       iMsg_car m2 v (Next p2') -∗ ∃ p1', ▷ rec p1' p2' ∗ iMsg_car m1 v (Next p1')
    | _, _ => False
    end.
Global Instance iProto_le_pre_ne {Σ V} (rec : iProto Σ V → iProto Σ V → iProp Σ) :
  NonExpansive2 (iProto_le_pre rec).
Proof. solve_proper. Qed.

Program Definition iProto_le_pre' {Σ V}
    (rec : iProto Σ V -n> iProto Σ V -n> iPropO Σ) :
    iProto Σ V -n> iProto Σ V -n> iPropO Σ := λne p1 p2,
  iProto_le_pre (λ p1' p2', rec p1' p2') p1 p2.
Solve Obligations with solve_proper.
Local Instance iProto_le_pre_contractive {Σ V} : Contractive (@iProto_le_pre' Σ V).
Proof.
  intros n rec1 rec2 Hrec p1 p2. rewrite /iProto_le_pre' /iProto_le_pre /=.
  by repeat (f_contractive || f_equiv).
Qed.
Definition iProto_le {Σ V} (p1 p2 : iProto Σ V) : iProp Σ :=
  fixpoint iProto_le_pre' p1 p2.
Arguments iProto_le {_ _} _%proto _%proto.
Global Instance: Params (@iProto_le) 2 := {}.
Notation "p ⊑ q" := (iProto_le p q) : bi_scope.

Global Instance iProto_le_ne {Σ V} : NonExpansive2 (@iProto_le Σ V).
Proof. solve_proper. Qed.
Global Instance iProto_le_proper {Σ V} : Proper ((≡) ==> (≡) ==> (⊣⊢)) (@iProto_le Σ V).
Proof. solve_proper. Qed.

Record proto_name := ProtName { proto_names : gmap nat gname }.
Global Instance proto_name_inhabited : Inhabited proto_name :=
  populate (ProtName inhabitant).
Global Instance proto_name_eq_dec : EqDecision proto_name.
Proof. solve_decision. Qed.
Global Instance proto_name_countable : Countable proto_name.
Proof.
 refine (inj_countable (λ '(ProtName γs), (γs))
   (λ '(γs), Some (ProtName γs)) _); by intros [].
Qed.

Definition iProto_own_frag `{!protoG Σ V} (γ : gname)
    (i : nat) (p : iProto Σ V) : iProp Σ :=
  own γ (gmap_view_frag i (DfracOwn 1) (Excl' (Next p))).

Definition iProto_own_auth `{!protoG Σ V} (γ : gname)
    (ps : list (iProto Σ V)) : iProp Σ :=
  own γ (gmap_view_auth (DfracOwn 1) ((λ p, Excl' (Next p)) <$> map_seq 0 ps)).

Definition iProto_ctx `{protoG Σ V}
    (γ : gname) (ps_len : nat) : iProp Σ :=
  ∃ ps, ⌜length ps = ps_len⌝ ∗ iProto_own_auth γ ps ∗ ▷ iProto_consistent ps.

(** * The connective for ownership of channel ends *)
Definition iProto_own `{!protoG Σ V}
    (γ : gname) (i : nat) (p : iProto Σ V) : iProp Σ :=
  ∃ p', ▷ (p' ⊑ p) ∗ iProto_own_frag γ i p'.
Arguments iProto_own {_ _ _} _ _ _%proto.
Global Instance: Params (@iProto_own) 3 := {}.

Global Instance iProto_own_frag_contractive `{protoG Σ V} γ i :
  Contractive (iProto_own_frag γ i).
Proof. solve_contractive. Qed.

Global Instance iProto_own_contractive `{protoG Σ V} γ i :
  Contractive (iProto_own γ i).
Proof. solve_contractive. Qed.
Global Instance iProto_own_ne `{protoG Σ V} γ s : NonExpansive (iProto_own γ s).
Proof. solve_proper. Qed.
Global Instance iProto_own_proper `{protoG Σ V} γ s :
  Proper ((≡) ==> (≡)) (iProto_own γ s).
Proof. apply (ne_proper _). Qed.

(** * Proofs *)
Section proto.
  Context `{!protoG Σ V}.
  Implicit Types v : V.
  Implicit Types p pl pr : iProto Σ V.
  Implicit Types m : iMsg Σ V.

  Lemma own_prot_idx γ i j (p1 p2 : iProto Σ V) :
    own γ (gmap_view_frag i (DfracOwn 1) (Excl' (Next p1))) -∗
    own γ (gmap_view_frag j (DfracOwn 1) (Excl' (Next p2))) -∗
    ⌜i ≠ j⌝.
  Proof.
    iIntros "Hown Hown'" (->).
    iDestruct (own_valid_2 with "Hown Hown'") as "H".
    rewrite uPred.cmra_valid_elim.
    by iDestruct "H" as %[]%gmap_view_frag_op_validN.
  Qed.

  Lemma own_prot_excl γ i (p1 p2 : iProto Σ V) :
    own γ (gmap_view_frag i (DfracOwn 1) (Excl' (Next p1))) -∗
    own γ (gmap_view_frag i (DfracOwn 1) (Excl' (Next p2))) -∗
    False.
  Proof. iIntros "Hi Hj". by iDestruct (own_prot_idx with "Hi Hj") as %?. Qed.

  (** ** Protocol entailment **)
  Lemma iProto_le_unfold p1 p2 : iProto_le p1 p2 ≡ iProto_le_pre iProto_le p1 p2.
  Proof. apply: (fixpoint_unfold iProto_le_pre'). Qed.

  Lemma iProto_le_end : ⊢ END ⊑ (END : iProto Σ V).
  Proof. rewrite iProto_le_unfold. iLeft. auto 10. Qed.

  Lemma iProto_le_end_inv_r p : p ⊑ END -∗ (p ≡ END).
  Proof.
    rewrite iProto_le_unfold. iIntros "[[Hp _]|H] //".
    iDestruct "H" as (a1 a2 m1 m2) "(_ & Heq & _)".
    by iDestruct (iProto_end_message_equivI with "Heq") as %[].
  Qed.

  Lemma iProto_le_end_inv_l p : END ⊑ p -∗ (p ≡ END).
  Proof.
    rewrite iProto_le_unfold. iIntros "[[_ Hp]|H] //".
    iDestruct "H" as (a1 a2 m1 m2) "(Heq & _ & _)".
    iDestruct (iProto_end_message_equivI with "Heq") as %[].
  Qed.

  Lemma iProto_le_send_inv i p1 m2 :
    p1 ⊑ (<(Send,i)> m2) -∗ ∃ m1,
      (p1 ≡ <(Send,i)> m1) ∗
      ∀ v p2', iMsg_car m2 v (Next p2') -∗
               ∃ p1', ▷ (p1' ⊑ p2') ∗ iMsg_car m1 v (Next p1').
  Proof.
    rewrite iProto_le_unfold.
    iIntros "[[_ Heq]|H]".
    { by iDestruct (iProto_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 m1 m2') "(Hp1 & Hp2 & H)".
    rewrite iProto_message_equivI. iDestruct "Hp2" as "[%Heq Hm2]".
    simplify_eq.
    destruct a1 as [[]]; [|done].
    iDestruct "H" as (->) "H". iExists m1. iFrame "Hp1".
    iIntros (v p2). iSpecialize ("Hm2" $! v (Next p2)). by iRewrite "Hm2".
  Qed.

  Lemma iProto_le_send_send_inv i m1 m2 v p2' :
    (<(Send,i)> m1) ⊑ (<(Send,i)> m2) -∗
    iMsg_car m2 v (Next p2') -∗ ∃ p1', ▷ (p1' ⊑ p2') ∗ iMsg_car m1 v (Next p1').
  Proof.
    iIntros "H Hm2". iDestruct (iProto_le_send_inv with "H") as (m1') "[Hm1 H]".
    iDestruct (iProto_message_equivI with "Hm1") as (Heq) "Hm1".
    iDestruct ("H" with "Hm2") as (p1') "[Hle Hm]".
    iRewrite -("Hm1" $! v (Next p1')) in "Hm". auto with iFrame.
  Qed.

  Lemma iProto_le_recv_inv_l i m1 p2 :
    (<(Recv,i)> m1) ⊑ p2 -∗ ∃ m2,
      (p2 ≡ <(Recv,i)> m2) ∗
      ∀ v p1', iMsg_car m1 v (Next p1') -∗
               ∃ p2', ▷ (p1' ⊑ p2') ∗ iMsg_car m2 v (Next p2').
  Proof.
    rewrite iProto_le_unfold.
    iIntros "[[Heq _]|H]".
    { iDestruct (iProto_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 m1' m2) "(Hp1 & Hp2 & H)".
    rewrite iProto_message_equivI. iDestruct "Hp1" as "[%Heq Hm1]".
    simplify_eq.
    destruct a2 as [[]]; [done|].
    iDestruct "H" as (->) "H". iExists m2. iFrame "Hp2".
    iIntros (v p1). iSpecialize ("Hm1" $! v (Next p1)). by iRewrite "Hm1".
  Qed.

  Lemma iProto_le_recv_inv_r i p1 m2 :
    (p1 ⊑ <(Recv,i)> m2) -∗ ∃ m1,
      (p1 ≡ <(Recv,i)> m1) ∗
      ∀ v p1', iMsg_car m1 v (Next p1') -∗
               ∃ p2', ▷ (p1' ⊑ p2') ∗ iMsg_car m2 v (Next p2').
  Proof.
    rewrite iProto_le_unfold.
    iIntros "[[_ Heq]|H]".
    { iDestruct (iProto_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 m1 m2') "(Hp1 & Hp2 & H)".
    rewrite iProto_message_equivI.
    iDestruct "Hp2" as "[%Heq Hm2]".
    simplify_eq.
    destruct a1 as [[]]; [done|].
    iDestruct "H" as (->) "H".
    iExists m1. iFrame.
    iIntros (v p2).
    iIntros "Hm1". iDestruct ("H" with "Hm1") as (p2') "[Hle H]".
    iSpecialize ("Hm2" $! v (Next p2')).
    iExists p2'. iFrame.
    iRewrite "Hm2". iApply "H".
  Qed.

  Lemma iProto_le_recv_recv_inv i m1 m2 v p1' :
    (<(Recv, i)> m1) ⊑ (<(Recv, i)> m2) -∗
    iMsg_car m1 v (Next p1') -∗ ∃ p2', ▷ (p1' ⊑ p2') ∗ iMsg_car m2 v (Next p2').
  Proof.
    iIntros "H Hm2". iDestruct (iProto_le_recv_inv_r with "H") as (m1') "[Hm1 H]".
    iApply "H". iDestruct (iProto_message_equivI with "Hm1") as (_) "Hm1".
    by iRewrite -("Hm1" $! v (Next p1')).
  Qed.

  Lemma iProto_le_msg_inv_l i a m1 p2 :
    (<(a,i)> m1) ⊑ p2 -∗ ∃ m2, p2 ≡ <(a,i)> m2.
  Proof.
    rewrite iProto_le_unfold /iProto_le_pre.
    iIntros "[[Heq _]|H]".
    { iDestruct (iProto_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 m1' m2) "(Hp1 & Hp2 & H)".
    destruct a1 as [t1 ?], a2 as [t2 ?].
    destruct t1,t2; [|done|done|].
    - rewrite iProto_message_equivI.
      iDestruct "Hp1" as (Heq) "Hp1". simplify_eq.
      iDestruct "H" as (->) "H". by iExists _.
    - rewrite iProto_message_equivI.
      iDestruct "Hp1" as (Heq) "Hp1". simplify_eq.
      iDestruct "H" as (->) "H". by iExists _.
  Qed.

  Lemma iProto_le_msg_inv_r j a p1 m2 :
    (p1 ⊑ <(a,j)> m2) -∗ ∃ m1, p1 ≡ <(a,j)> m1.
  Proof.
    rewrite iProto_le_unfold /iProto_le_pre.
    iIntros "[[_ Heq]|H]".
    { iDestruct (iProto_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 m1 m2') "(Hp1 & Hp2 & H)".
    destruct a1 as [t1 ?], a2 as [t2 ?].
    destruct t1,t2; [|done|done|].
    - rewrite iProto_message_equivI.
      iDestruct "Hp2" as (Heq) "Hp2". simplify_eq.
      iDestruct "H" as (->) "H". by iExists _.
    - rewrite iProto_message_equivI.
      iDestruct "Hp2" as (Heq) "Hp2". simplify_eq.
      iDestruct "H" as (->) "H". by iExists _.
  Qed.
  
  Lemma iProto_le_send i m1 m2 :
    (∀ v p2', iMsg_car m2 v (Next p2') -∗ ∃ p1',
      ▷ (p1' ⊑ p2') ∗ iMsg_car m1 v (Next p1')) -∗
    (<(Send,i)> m1) ⊑ (<(Send,i)> m2).
  Proof.
    iIntros "Hle". rewrite iProto_le_unfold.
    iRight. iExists (Send, i), (Send, i), m1, m2. by eauto.
  Qed.

  Lemma iProto_le_recv i m1 m2 :
    (∀ v p1', iMsg_car m1 v (Next p1') -∗ ∃ p2',
      ▷ (p1' ⊑ p2') ∗ iMsg_car m2 v (Next p2')) -∗
    (<(Recv,i)> m1) ⊑ (<(Recv,i)> m2).
  Proof.
    iIntros "Hle". rewrite iProto_le_unfold.
    iRight. iExists (Recv, i), (Recv, i), m1, m2. by eauto.
  Qed.

  Lemma iProto_le_base a v P p1 p2 :
    ▷ (p1 ⊑ p2) -∗
    (<a> MSG v {{ P }}; p1) ⊑ (<a> MSG v {{ P }}; p2).
  Proof.
    rewrite iMsg_base_eq. iIntros "H". destruct a as [[]].
    - iApply iProto_le_send. iIntros (v' p') "(->&Hp&$)".
      iExists p1. iSplit; [|by auto]. iIntros "!>". by iRewrite -"Hp".
    - iApply iProto_le_recv. iIntros (v' p') "(->&Hp&$)".
      iExists p2. iSplit; [|by auto]. iIntros "!>". by iRewrite -"Hp".
  Qed.

  Lemma iProto_le_trans p1 p2 p3 : p1 ⊑ p2 -∗ p2 ⊑ p3 -∗ p1 ⊑ p3.
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (p1 p2 p3).
    destruct (iProto_case p3) as [->|([]&i&m3&->)].
    - iDestruct (iProto_le_end_inv_r with "H2") as "H2". by iRewrite "H2" in "H1".
    - iDestruct (iProto_le_send_inv with "H2") as (m2) "[Hp2 H2]".
      iRewrite "Hp2" in "H1"; clear p2.
      iDestruct (iProto_le_send_inv with "H1") as (m1) "[Hp1 H1]".
      iRewrite "Hp1"; clear p1.
      iApply iProto_le_send. iIntros (v p3') "Hm3".
      iDestruct ("H2" with "Hm3") as (p2') "[Hle Hm2]".
      iDestruct ("H1" with "Hm2") as (p1') "[Hle' Hm1]".
      iExists p1'. iIntros "{$Hm1} !>". by iApply ("IH" with "Hle'").
    - iDestruct (iProto_le_recv_inv_r with "H2") as (m2) "[Hp2 H3]".
      iRewrite "Hp2" in "H1".
      iDestruct (iProto_le_recv_inv_r with "H1") as (m1) "[Hp1 H2]".
      iRewrite "Hp1". iApply iProto_le_recv. iIntros (v p1') "Hm1".
      iDestruct ("H2" with "Hm1") as (p2') "[Hle Hm2]".
      iDestruct ("H3" with "Hm2") as (p3') "[Hle' Hm3]".
      iExists p3'. iIntros "{$Hm3} !>". by iApply ("IH" with "Hle").
  Qed.

  Lemma iProto_le_refl p : ⊢ p ⊑ p.
  Proof.
    iLöb as "IH" forall (p). destruct (iProto_case p) as [->|([]&i&m&->)].
    - iApply iProto_le_end.
    - iApply iProto_le_send. auto 10 with iFrame.
    - iApply iProto_le_recv. auto 10 with iFrame.
  Qed.


  Global Instance iProto_own_frag_ne γ s : NonExpansive (iProto_own_frag γ s).
  Proof. solve_proper. Qed.

  Lemma iProto_own_auth_agree γ ps i p :
    iProto_own_auth γ ps -∗ iProto_own_frag γ i p -∗ ▷ (ps !! i ≡ Some p).
  Proof.    
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as "H✓".
    rewrite gmap_view_both_validI.
    iDestruct "H✓" as "[_ [H1 H2]]".
    rewrite lookup_fmap.
    simpl.
    rewrite lookup_map_seq_0.    
    destruct (ps !! i) eqn:Heqn; last first.
    { rewrite Heqn. rewrite !option_equivI. done. }
    rewrite Heqn.
    simpl. rewrite !option_equivI excl_equivI. by iNext.
  Qed.

  Lemma iProto_own_auth_agree_Some γ ps i p :
    iProto_own_auth γ ps -∗ iProto_own_frag γ i p -∗ ⌜is_Some (ps !! i)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as "H✓".
    rewrite gmap_view_both_validI.
    iDestruct "H✓" as "[_ [H1 H2]]".
    rewrite lookup_fmap.
    simpl.
    rewrite lookup_map_seq_0.    
    destruct (ps !! i) eqn:Heqn; last first.
    { rewrite Heqn. rewrite !option_equivI. done. }
    rewrite Heqn.
    simpl. rewrite !option_equivI excl_equivI. done. 
  Qed.

  Lemma iProto_own_auth_update γ ps i p p' :
    iProto_own_auth γ ps -∗ iProto_own_frag γ i p ==∗
    iProto_own_auth γ (<[i := p']>ps) ∗ iProto_own_frag γ i p'.
  Proof.
    iIntros "H● H◯".
    iDestruct (iProto_own_auth_agree_Some with "H● H◯") as %HSome.
    iMod (own_update_2 with "H● H◯") as "[H1 H2]"; [|iModIntro].
    { eapply (gmap_view_replace _ _ _ (Excl' (Next p'))). done. }
    iFrame. rewrite -fmap_insert.
    rewrite /iProto_own_auth. 
    rewrite insert_map_seq_0; [done|].
    by apply lookup_lt_is_Some_1.
  Qed.
  
  Lemma iProto_own_auth_alloc ps :
    ⊢ |==> ∃ γ, iProto_own_auth γ ps ∗ [∗ list] i ↦p ∈ ps, iProto_own γ i p.
  Proof.
    iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γ) "Hauth".
    { apply gmap_view_auth_valid. }
    iExists γ.
    iInduction ps as [|p ps] "IH" using rev_ind.
    { iModIntro. iFrame. done. }
    iMod ("IH" with "Hauth") as "[Hauth Hfrags]".
    iFrame "Hfrags".
    iMod (own_update with "Hauth") as "[Hauth Hfrag]".
    { apply (gmap_view_alloc _ (length ps) (DfracOwn 1) (Excl' (Next p))); [|done|done].
      rewrite fmap_map_seq.
      rewrite lookup_map_seq_0.
      apply lookup_ge_None_2. rewrite fmap_length. done. }
    simpl.
    iModIntro. 
    rewrite right_id_L. 
    rewrite -fmap_insert. iFrame.
    iSplitL "Hauth".
    - rewrite /iProto_own_auth.
      rewrite map_seq_snoc. simpl. done.
    - iSplit; [|done].
      iExists _. iFrame. by iApply iProto_le_refl.
  Qed.

  Lemma list_lookup_Some_le (ps : list $ iProto Σ V) (i : nat) (p1 : iProto Σ V) :
    ⊢@{iProp Σ} ps !! i ≡ Some p1 -∗ ⌜i < length ps⌝.
  Proof.
    iIntros "HSome".
    rewrite option_equivI.
    destruct (ps !! i) eqn:Heqn; [|done].
    iPureIntro.
    by apply lookup_lt_is_Some_1.
  Qed.

  Lemma valid_target_le ps i p1 p2 :
    (∀ i' j', valid_target ps i' j') -∗
    ps !! i ≡ Some p1 -∗
    p1 ⊑ p2 -∗
    (∀ i' j', valid_target (<[i := p2]>ps) i' j') ∗ p1 ⊑ p2.
  Proof.
    iIntros "Hprot #HSome Hle".
    iDestruct (list_lookup_Some_le with "HSome") as %Hi.
    pose proof (iProto_case p1) as [Hend|Hmsg].
    { rewrite Hend. iDestruct (iProto_le_end_inv_l with "Hle") as "#H".
      iFrame "Hle".
      iIntros (i' j' a m) "Hm".
      destruct (decide (i = j')) as [->|Hneqj].
      { rewrite list_lookup_insert; [done|]. done. }
      rewrite (list_lookup_insert_ne _ i j'); [|done].
      destruct (decide (i = i')) as [->|Hneqi].
      { rewrite list_lookup_total_insert; [|done]. iRewrite "H" in "Hm".
        by iDestruct (iProto_end_message_equivI with "Hm") as "Hm". }
      rewrite list_lookup_total_insert_ne; [|done].
      by iApply "Hprot". }
    destruct Hmsg as (t & n & m & Hmsg).
    setoid_rewrite Hmsg.
    iDestruct (iProto_le_msg_inv_l with "Hle") as (m2) "#Heq". iFrame "Hle".
    iIntros (i' j' a m') "Hm".
    destruct (decide (i = j')) as [->|Hneqj].
    { by rewrite list_lookup_insert. }
    rewrite (list_lookup_insert_ne _ i j'); [|done].
    destruct (decide (i = i')) as [->|Hneqi].
    { rewrite list_lookup_total_insert; [|done]. iRewrite "Heq" in "Hm".
      iDestruct (iProto_message_equivI with "Hm") as (Heq) "Hm".
      simplify_eq. iApply ("Hprot" $! i'). 
      rewrite list_lookup_total_alt. iRewrite "HSome". done. }
    rewrite list_lookup_total_insert_ne; [|done].
    by iApply "Hprot".
  Qed.

  Lemma iProto_consistent_le ps i p1 p2 :
    iProto_consistent ps -∗
    ps !! i ≡ Some p1 -∗
    p1 ⊑ p2 -∗
    iProto_consistent (<[i := p2]>ps).
  Proof.
    iIntros "Hprot #HSome Hle".
    iRevert "HSome".
    iLöb as "IH" forall (p1 p2 ps).
    iIntros "#HSome".
    iDestruct (list_lookup_Some_le with "HSome") as %Hi.
    rewrite !iProto_consistent_unfold.
    iDestruct "Hprot" as "(Htar & Hprot)".
    iDestruct (valid_target_le with "Htar HSome Hle") as "[Htar Hle]".
    iFrame.
    iIntros (i' j' m1 m2) "#Hm1 #Hm2".
    destruct (decide (i = i')) as [<-|Hneq].
    { rewrite list_lookup_total_insert; [|done].
      pose proof (iProto_case p2) as [Hend|Hmsg].
      { setoid_rewrite Hend.
        rewrite !option_equivI. rewrite iProto_end_message_equivI. done. }
      destruct Hmsg as (a&?&m&Hmsg).
      setoid_rewrite Hmsg.
      destruct a; last first.
      { rewrite !option_equivI. rewrite iProto_message_equivI.
        iDestruct "Hm1" as "[%Htag Hm1]". done. }
      rewrite iProto_message_equivI.
      iDestruct "Hm1" as "[%Htag Hm1]".
      inversion Htag. simplify_eq.
      iIntros (v p) "Hm1'".
      iSpecialize ("Hm1" $! v (Next p)).
      iDestruct (iProto_le_send_inv with "Hle") as "Hle".
      iRewrite -"Hm1" in "Hm1'".
      iDestruct "Hle" as (m') "[#Heq H]".
      iDestruct ("H" with "Hm1'") as (p') "[Hle H]".
      destruct (decide (i = j')) as [<-|Hneq].
      { rewrite list_lookup_total_insert; [|done].
        rewrite iProto_message_equivI.
        iDestruct "Hm2" as "[%Heq _]". done. }
      iDestruct ("Hprot" $!i j' with "[] [] H") as "Hprot".
      { iRewrite -"Heq". iEval (rewrite list_lookup_total_alt). 
        iRewrite "HSome". done. }
      { rewrite list_lookup_total_insert_ne; [|done]. done. }
      iDestruct "Hprot" as (p'') "[Hm Hprot]".
      iExists p''. iFrame.
      iNext.
      iDestruct ("IH" with "Hprot Hle [HSome]") as "HI".
      { rewrite list_lookup_insert; [done|].
        by rewrite insert_length. }
      iClear "IH Hm1 Hm2 Heq".
      rewrite list_insert_insert.
      rewrite (list_insert_commute _ j' i); [|done].
      rewrite list_insert_insert. done. }
    rewrite list_lookup_total_insert_ne; [|done].
    destruct (decide (i = j')) as [<-|Hneq'].
    { rewrite list_lookup_total_insert; [|done].
      pose proof (iProto_case p2) as [Hend|Hmsg].
      { setoid_rewrite Hend.
        rewrite !option_equivI.
        rewrite iProto_end_message_equivI. done. }
      destruct Hmsg as (a&?&m&Hmsg).
      setoid_rewrite Hmsg.
      destruct a.
      { rewrite !option_equivI.
        rewrite iProto_message_equivI.
        iDestruct "Hm2" as "[%Htag Hm2]". done. }
      rewrite iProto_message_equivI.
      iDestruct "Hm2" as "[%Htag Hm2]".
      inversion Htag. simplify_eq.
      iIntros (v p) "Hm1'".
      iDestruct (iProto_le_recv_inv_r with "Hle") as "Hle".
      iDestruct "Hle" as (m') "[#Heq Hle]".
      iDestruct ("Hprot" $!i' with "[] [] Hm1'") as "Hprot".
      { done. }
      { iEval (rewrite list_lookup_total_alt). iRewrite "HSome". done. }
      iDestruct ("Hprot") as (p') "[Hm1' Hprot]".
      iDestruct ("Hle" with "Hm1'") as (p2') "[Hle Hm']".
      iSpecialize ("Hm2" $! v (Next p2')).
      iExists p2'.
      iRewrite -"Hm2". iFrame.
      iDestruct ("IH" with "Hprot Hle []") as "HI".
      { iPureIntro. rewrite list_lookup_insert_ne; [|done].
        by rewrite list_lookup_insert. }
      rewrite list_insert_commute; [|done].
      rewrite !list_insert_insert. done. }
    rewrite list_lookup_total_insert_ne; [|done].
    iIntros (v p) "Hm1'".
    iDestruct ("Hprot" $!i' j' with "[//] [//] Hm1'") as "Hprot".
    iDestruct "Hprot" as (p') "[Hm2' Hprot]".
    iExists p'. iFrame.
    iNext.
    rewrite (list_insert_commute _ j' i); [|done].
    rewrite (list_insert_commute _ i' i); [|done].
    iApply ("IH" with "Hprot Hle []").
    rewrite list_lookup_insert_ne; [|done].
    rewrite list_lookup_insert_ne; [|done].
    done.
  Qed.

  Lemma iProto_le_dual p1 p2 : p2 ⊑ p1 -∗ iProto_dual p1 ⊑ iProto_dual p2.
  Proof.
    iIntros "H". iLöb as "IH" forall (p1 p2).
    destruct (iProto_case p1) as [->|([]&i&m1&->)].
    - iDestruct (iProto_le_end_inv_r with "H") as "H".
      iRewrite "H". iApply iProto_le_refl.
    - iDestruct (iProto_le_send_inv with "H") as (m2) "[Hp2 H]".
      iRewrite "Hp2"; clear p2. iEval (rewrite !iProto_dual_message).
      iApply iProto_le_recv. iIntros (v p1d).
      iDestruct 1 as (p1') "[Hm1 #Hp1d]".
      iDestruct ("H" with "Hm1") as (p2') "[H Hm2]".
      iDestruct ("IH" with "H") as "H". iExists (iProto_dual p2').
      iSplitL "H"; [iIntros "!>"; by iRewrite "Hp1d"|]. simpl; auto.
    - iDestruct (iProto_le_recv_inv_r with "H") as (m2) "[Hp2 H]".
      iRewrite "Hp2"; clear p2. iEval (rewrite !iProto_dual_message /=).
      iApply iProto_le_send. iIntros (v p2d).
      iDestruct 1 as (p2') "[Hm2 #Hp2d]".
      iDestruct ("H" with "Hm2") as (p1') "[H Hm1]".
      iDestruct ("IH" with "H") as "H". iExists (iProto_dual p1').
      iSplitL "H"; [iIntros "!>"; by iRewrite "Hp2d"|]. simpl; auto.
  Qed.

  Lemma iProto_le_dual_l p1 p2 : iProto_dual p2 ⊑ p1 ⊢ iProto_dual p1 ⊑ p2.
  Proof.
    iIntros "H". iEval (rewrite -(involutive iProto_dual p2)).
    by iApply iProto_le_dual.
  Qed.
  Lemma iProto_le_dual_r p1 p2 : p2 ⊑ iProto_dual p1 ⊢ p1 ⊑ iProto_dual p2.
  Proof.
    iIntros "H". iEval (rewrite -(involutive iProto_dual p1)).
    by iApply iProto_le_dual.
  Qed.

  Lemma iProto_le_app p1 p2 p3 p4 :
    p1 ⊑ p2 -∗ p3 ⊑ p4 -∗ p1 <++> p3 ⊑ p2 <++> p4.
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (p1 p2 p3 p4).
    destruct (iProto_case p2) as [->|([]&i&m2&->)].
    - iDestruct (iProto_le_end_inv_r with "H1") as "H1".
      iRewrite "H1". by rewrite !left_id.
    - iDestruct (iProto_le_send_inv with "H1") as (m1) "[Hp1 H1]".
      iRewrite "Hp1"; clear p1. rewrite !iProto_app_message.
      iApply iProto_le_send. iIntros (v p24).
      iDestruct 1 as (p2') "[Hm2 #Hp24]".
      iDestruct ("H1" with "Hm2") as (p1') "[H1 Hm1]".
      iExists (p1' <++> p3). iSplitR "Hm1"; [|by simpl; eauto].
      iIntros "!>". iRewrite "Hp24". by iApply ("IH" with "H1").
    - iDestruct (iProto_le_recv_inv_r with "H1") as (m1) "[Hp1 H1]".
      iRewrite "Hp1"; clear p1. rewrite !iProto_app_message.
      iApply iProto_le_recv.
      iIntros (v p13). iDestruct 1 as (p1') "[Hm1 #Hp13]".
      iDestruct ("H1" with "Hm1") as (p2'') "[H1 Hm2]".
      iExists (p2'' <++> p4). iSplitR "Hm2"; [|by simpl; eauto].
      iIntros "!>". iRewrite "Hp13". by iApply ("IH" with "H1").
  Qed.

  Lemma iProto_le_payload_elim_l i m v P p :
    (P -∗ (<(Recv,i)> MSG v; p) ⊑ (<(Recv,i)> m)) ⊢
    (<(Recv,i)> MSG v {{ P }}; p) ⊑ <(Recv,i)> m.
  Proof.
    rewrite iMsg_base_eq. iIntros "H".
    iApply iProto_le_recv. iIntros (v' p') "(->&Hp&HP)".
    iApply (iProto_le_recv_recv_inv with "(H HP)"); simpl; auto.
  Qed.
  Lemma iProto_le_payload_elim_r i m v P p :
    (P -∗ (<(Send, i)> m) ⊑ (<(Send, i)> MSG v; p)) ⊢
    (<(Send,i)> m) ⊑ (<(Send,i)> MSG v {{ P }}; p).
  Proof.
    rewrite iMsg_base_eq. iIntros "H".
    iApply iProto_le_send. iIntros (v' p') "(->&Hp&HP)".
    iApply (iProto_le_send_send_inv with "(H HP)"); simpl; auto.
  Qed.
  Lemma iProto_le_payload_intro_l i v P p :
    P -∗ (<(Send,i)> MSG v {{ P }}; p) ⊑ (<(Send,i)> MSG v; p).
  Proof.
    rewrite iMsg_base_eq.
    iIntros "HP". iApply iProto_le_send. iIntros (v' p') "(->&Hp&_) /=".
    iExists p'. iSplitR; [iApply iProto_le_refl|]. auto.
  Qed.
  Lemma iProto_le_payload_intro_r i v P p :
    P -∗ (<(Recv,i)> MSG v; p) ⊑ (<(Recv,i)> MSG v {{ P }}; p).
  Proof.
    rewrite iMsg_base_eq.
    iIntros "HP". iApply iProto_le_recv. iIntros (v' p') "(->&Hp&_) /=".
    iExists p'. iSplitR; [iApply iProto_le_refl|]. auto.
  Qed.
  Lemma iProto_le_exist_elim_l {A} i (m1 : A → iMsg Σ V) m2 :
    (∀ x, (<(Recv,i)> m1 x) ⊑ (<(Recv,i)> m2)) ⊢
    (<(Recv,i) @ x> m1 x) ⊑ (<(Recv,i)> m2).
  Proof.
    rewrite iMsg_exist_eq. iIntros "H".
    iApply iProto_le_recv. iIntros (v p1') "/=". iDestruct 1 as (x) "Hm".
    by iApply (iProto_le_recv_recv_inv with "H").
  Qed.
  Lemma iProto_le_exist_elim_r {A} i m1 (m2 : A → iMsg Σ V) :
    (∀ x, (<(Send,i)> m1) ⊑ (<(Send,i)> m2 x)) ⊢
    (<(Send,i)> m1) ⊑ (<(Send,i) @ x> m2 x).
  Proof.
    rewrite iMsg_exist_eq. iIntros "H".
    iApply iProto_le_send. iIntros (v p2'). iDestruct 1 as (x) "Hm".
    by iApply (iProto_le_send_send_inv with "H").
  Qed.
  Lemma iProto_le_exist_intro_l {A} i (m : A → iMsg Σ V) a :
    ⊢ (<(Send,i) @ x> m x) ⊑ (<(Send,i)> m a).
  Proof.
    rewrite iMsg_exist_eq. iApply iProto_le_send. iIntros (v p') "Hm /=".
    iExists p'. iSplitR; last by auto. iApply iProto_le_refl.
  Qed.
  Lemma iProto_le_exist_intro_r {A} i (m : A → iMsg Σ V) a :
    ⊢ (<(Recv,i)> m a) ⊑ (<(Recv,i) @ x> m x).
  Proof.
    rewrite iMsg_exist_eq. iApply iProto_le_recv. iIntros (v p') "Hm /=".
    iExists p'. iSplitR; last by auto. iApply iProto_le_refl.
  Qed.

  Lemma iProto_le_texist_elim_l {TT : tele} i (m1 : TT → iMsg Σ V) m2 :
    (∀ x, (<(Recv,i)> m1 x) ⊑ (<(Recv,i)> m2)) ⊢
    (<(Recv,i) @.. x> m1 x) ⊑ (<(Recv,i)> m2).
  Proof.
    iIntros "H". iInduction TT as [|T TT] "IH"; simpl; [done|].
    iApply iProto_le_exist_elim_l; iIntros (x).
    iApply "IH". iIntros (xs). iApply "H".
  Qed.
  Lemma iProto_le_texist_elim_r {TT : tele} i m1 (m2 : TT → iMsg Σ V) :
    (∀ x, (<(Send,i)> m1) ⊑ (<(Send,i)> m2 x)) -∗
    (<(Send,i)> m1) ⊑ (<(Send,i) @.. x> m2 x).
  Proof.
    iIntros "H". iInduction TT as [|T TT] "IH"; simpl; [done|].
    iApply iProto_le_exist_elim_r; iIntros (x).
    iApply "IH". iIntros (xs). iApply "H".
  Qed.

  Lemma iProto_le_texist_intro_l {TT : tele} i (m : TT → iMsg Σ V) x :
    ⊢ (<(Send,i) @.. x> m x) ⊑ (<(Send,i)> m x).
  Proof.
    induction x as [|T TT x xs IH] using tele_arg_ind; simpl.
    { iApply iProto_le_refl. }
    iApply iProto_le_trans; [by iApply iProto_le_exist_intro_l|]. iApply IH.
  Qed.
  Lemma iProto_le_texist_intro_r {TT : tele} i (m : TT → iMsg Σ V) x :
    ⊢ (<(Recv,i)> m x) ⊑ (<(Recv,i) @.. x> m x).
  Proof.
    induction x as [|T TT x xs IH] using tele_arg_ind; simpl.
    { iApply iProto_le_refl. }
    iApply iProto_le_trans; [|by iApply iProto_le_exist_intro_r]. iApply IH.
  Qed.

  Lemma iProto_consistent_target ps m a i j :
    iProto_consistent ps -∗
    ps !! i ≡ Some (<(a, j)> m) -∗
    ⌜is_Some (ps !! j)⌝.
  Proof.
    rewrite iProto_consistent_unfold. iDestruct 1 as "[Htar _]".
    iIntros "H". iApply ("Htar" $! i).
    rewrite list_lookup_total_alt. iRewrite "H". done.
  Qed.

  Lemma iProto_consistent_step ps m1 m2 i j v p1 :
    iProto_consistent ps -∗
    ps !! i ≡ Some (<(Send, j)> m1) -∗
    ps !! j ≡ Some (<(Recv, i)> m2) -∗
    iMsg_car m1 v (Next p1) -∗
    ∃ p2, iMsg_car m2 v (Next p2) ∗
          ▷ iProto_consistent (<[i := p1]>(<[j := p2]>ps)).
  Proof.
    iIntros "Hprot #Hi #Hj Hm1".
    rewrite iProto_consistent_unfold /iProto_consistent_pre.
    iDestruct "Hprot" as "[_ Hprot]".
    iDestruct ("Hprot" $! i j with "[Hi] [Hj] Hm1") as (p2) "[Hm2 Hprot]".
    { rewrite list_lookup_total_alt. iRewrite "Hi". done. }
    { rewrite list_lookup_total_alt. iRewrite "Hj". done. }
    iExists p2. iFrame.
  Qed.

  Lemma iProto_own_le γ s p1 p2 :
    iProto_own γ s p1 -∗ ▷ (p1 ⊑ p2) -∗ iProto_own γ s p2.
  Proof.
    iDestruct 1 as (p1') "[Hle H]". iIntros "Hle'".
    iExists p1'. iFrame "H". by iApply (iProto_le_trans with "Hle").
  Qed.

  Lemma iProto_own_excl γ i (p1 p2 : iProto Σ V) :
    iProto_own γ i p1 -∗ iProto_own γ i p2 -∗ False.
  Proof.
    rewrite /iProto_own.
    iDestruct 1 as (p1') "[_ Hp1]".
    iDestruct 1 as (p2') "[_ Hp2]".
    iDestruct (own_prot_excl with "Hp1 Hp2") as %[].
  Qed.

  Lemma iProto_ctx_agree γ n i p :
    iProto_ctx γ n -∗
    iProto_own γ i p -∗
    ⌜i < n⌝.
  Proof. 
      iIntros "Hctx Hown".
      rewrite /iProto_ctx /iProto_own.
      iDestruct "Hctx" as (ps <-) "[Hauth Hps]".
      iDestruct "Hown" as (p') "[Hle Hown]".
      iDestruct (iProto_own_auth_agree_Some with "Hauth Hown") as %HSome.
      iPureIntro.
      by apply lookup_lt_is_Some_1.
  Qed.

  Lemma iProto_init ps :
    ▷ iProto_consistent ps -∗
    |==> ∃ γ, iProto_ctx γ (length ps) ∗ [∗ list] i ↦p ∈ ps, iProto_own γ i p.
  Proof.
    iIntros "Hconsistent".
    iMod iProto_own_auth_alloc as (γ) "[Hauth Hfrags]".
    iExists γ. iFrame. iExists _. by iFrame.
  Qed.

  Lemma iProto_step γ ps_dom i j m1 m2 p1 v :
    iProto_ctx γ ps_dom -∗
    iProto_own γ i (<(Send, j)> m1) -∗
    iProto_own γ j (<(Recv, i)> m2) -∗
    iMsg_car m1 v (Next p1) ==∗
    ▷ ∃ p2, iMsg_car m2 v (Next p2) ∗ iProto_ctx γ ps_dom ∗
            iProto_own γ i p1 ∗ iProto_own γ j p2.
  Proof.
    iIntros "Hctx Hi Hj Hm".
    iDestruct (iProto_ctx_agree with "Hctx Hi") as %Hi.
    iDestruct (iProto_ctx_agree with "Hctx Hj") as %Hij.
    iDestruct "Hi" as (pi) "[Hile Hi]".
    iDestruct "Hj" as (pj) "[Hjle Hj]".
    iDestruct "Hctx" as (ps Hdom) "[Hauth Hconsistent]".
    iDestruct (iProto_own_auth_agree with "Hauth Hi") as "#Hpi".
    iDestruct (iProto_own_auth_agree with "Hauth Hj") as "#Hpj".
    iDestruct (own_prot_idx with "Hi Hj") as %Hneq.
    iAssert (▷ (<[i:=<(Send, j)> m1]>ps !! j ≡ Some pj))%I as "Hpj'".
    { by rewrite list_lookup_insert_ne. }
    iAssert (▷ (⌜is_Some (ps !! i)⌝ ∗ (pi ⊑ (<(Send, j)> m1))))%I with "[Hile]"
      as "[Hi' Hile]".
    { iNext. iDestruct (iProto_le_msg_inv_r with "Hile") as (m) "#Heq".
      iFrame. iRewrite "Heq" in "Hpi". destruct (ps !! i); [done|].
      by rewrite option_equivI. }
    iAssert (▷ (⌜is_Some (ps !! j)⌝ ∗ (pj ⊑ (<(Recv, i)> m2))))%I with "[Hjle]"
      as "[Hj' Hjle]".
    { iNext. iDestruct (iProto_le_msg_inv_r with "Hjle") as (m) "#Heq".
      iFrame. iRewrite "Heq" in "Hpj".
      destruct (ps !! j); [done|]. by rewrite !option_equivI. }
    iDestruct (iProto_consistent_le with "Hconsistent Hpi Hile") as "Hconsistent".
    iDestruct (iProto_consistent_le with "Hconsistent Hpj' Hjle") as "Hconsistent".
    iDestruct (iProto_consistent_step _ _ _ i j with "Hconsistent [] [] [Hm //]") as
      (p2) "[Hm2 Hconsistent]".
    { rewrite list_lookup_insert_ne; [|done].
      rewrite list_lookup_insert_ne; [|done].
      rewrite list_lookup_insert; [done|]. lia. }
    { rewrite list_lookup_insert_ne; [|done].
      rewrite list_lookup_insert; [done|]. rewrite insert_length. lia. }
    iMod (iProto_own_auth_update _ _ _ _ p2 with "Hauth Hj") as "[Hauth Hj]".
    iMod (iProto_own_auth_update _ _ _ _ p1 with "Hauth Hi") as "[Hauth Hi]".
    iIntros "!>!>". iExists p2. iFrame "Hm2".
    iDestruct "Hi'" as %Hi'. iDestruct "Hj'" as %Hj'.
    iSplitL "Hconsistent Hauth".
    { iExists (<[i:=p1]> (<[j:=p2]> ps)).
      iSplit.
      { iPureIntro. rewrite !insert_length. done. } 
      iFrame. rewrite list_insert_insert.
      rewrite list_insert_commute; [|done]. rewrite list_insert_insert.
      by rewrite list_insert_commute; [|done]. }
    iSplitL "Hi"; iExists _; iFrame; iApply iProto_le_refl.
  Qed.

  Lemma iProto_target γ ps_dom i a j m :
    iProto_ctx γ ps_dom -∗
    iProto_own γ i (<(a, j)> m) -∗
    ▷ (⌜j < ps_dom⌝).
  Proof.
    iIntros "Hctx Hown".
    rewrite /iProto_ctx /iProto_own.
    iDestruct "Hctx" as (ps Hdom) "[Hauth Hps]".
    iDestruct "Hown" as (p') "[Hle Hown]".
    iDestruct (iProto_own_auth_agree with "Hauth Hown") as "#Hi".
    iDestruct (iProto_le_msg_inv_r with "Hle") as (m') "#Heq".
    iDestruct (iProto_consistent_target with "Hps []") as "#H".
    { iNext. iRewrite "Heq" in "Hi". done. }
    iNext. iDestruct "H" as %HSome.
    iPureIntro. subst. by apply lookup_lt_is_Some_1.
  Qed.

  (* (** The instances below make it possible to use the tactics [iIntros], *)
  (* [iExist], [iSplitL]/[iSplitR], [iFrame] and [iModIntro] on [iProto_le] goals. *) *)
  Global Instance iProto_le_from_forall_l {A} i (m1 : A → iMsg Σ V) m2 name :
    AsIdentName m1 name →
    FromForall (iProto_message (Recv,i) (iMsg_exist m1) ⊑ (<(Recv,i)> m2))
               (λ x, (<(Recv, i)> m1 x) ⊑ (<(Recv, i)> m2))%I name | 10.
  Proof. intros _. apply iProto_le_exist_elim_l. Qed.
  Global Instance iProto_le_from_forall_r {A} i m1 (m2 : A → iMsg Σ V) name :
    AsIdentName m2 name →
    FromForall ((<(Send,i)> m1) ⊑ iProto_message (Send,i) (iMsg_exist m2))
               (λ x, (<(Send,i)> m1) ⊑ (<(Send,i)> m2 x))%I name | 11.
  Proof. intros _. apply iProto_le_exist_elim_r. Qed.

  Global Instance iProto_le_from_wand_l i m v P p :
    TCIf (TCEq P True%I) False TCTrue →
    FromWand ((<(Recv,i)> MSG v {{ P }}; p) ⊑ (<(Recv,i)> m)) P ((<(Recv,i)> MSG v; p) ⊑ (<(Recv,i)> m)) | 10.
  Proof. intros _. apply iProto_le_payload_elim_l. Qed.
  Global Instance iProto_le_from_wand_r i m v P p :
    FromWand ((<(Send,i)> m) ⊑ (<(Send,i)> MSG v {{ P }}; p)) P ((<(Send,i)> m) ⊑ (<(Send,i)> MSG v; p)) | 11.
  Proof. apply iProto_le_payload_elim_r. Qed.

  Global Instance iProto_le_from_exist_l {A} i (m : A → iMsg Σ V) p :
    FromExist ((<(Send,i) @ x> m x) ⊑ p) (λ a, (<(Send,i)> m a) ⊑ p)%I | 10.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (iProto_le_trans with "[] H"). iApply iProto_le_exist_intro_l.
  Qed.
  Global Instance iProto_le_from_exist_r {A} i (m : A → iMsg Σ V) p :
    FromExist (p ⊑ <(Recv,i) @ x> m x) (λ a, p ⊑ (<(Recv,i)> m a))%I | 11.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (iProto_le_trans with "H"). iApply iProto_le_exist_intro_r.
  Qed.

  Global Instance iProto_le_from_sep_l i m v P p :
    FromSep ((<(Send,i)> MSG v {{ P }}; p) ⊑ (<(Send,i)> m)) P ((<(Send,i)> MSG v; p) ⊑ (<(Send,i)> m)) | 10.
  Proof.
    rewrite /FromSep. iIntros "[HP H]".
    iApply (iProto_le_trans with "[HP] H"). by iApply iProto_le_payload_intro_l.
  Qed.
  Global Instance iProto_le_from_sep_r i m v P p :
    FromSep ((<(Recv,i)> m) ⊑ (<(Recv,i)> MSG v {{ P }}; p)) P ((<(Recv,i)> m) ⊑ (<(Recv,i)> MSG v; p)) | 11.
  Proof.
    rewrite /FromSep. iIntros "[HP H]".
    iApply (iProto_le_trans with "H"). by iApply iProto_le_payload_intro_r.
  Qed.

  Global Instance iProto_le_frame_l i q m v R P Q p :
    Frame q R P Q →
    Frame q R ((<(Send,i)> MSG v {{ P }}; p) ⊑ (<(Send,i)> m))
              ((<(Send,i)> MSG v {{ Q }}; p) ⊑ (<(Send,i)> m)) | 10.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (iProto_le_trans with "[HR] H"). iApply iProto_le_payload_elim_r.
    iIntros "HQ". iApply iProto_le_payload_intro_l. iApply HP; iFrame.
  Qed.
  Global Instance iProto_le_frame_r i q m v R P Q p :
    Frame q R P Q →
    Frame q R ((<(Recv,i)> m) ⊑ (<(Recv,i)> MSG v {{ P }}; p))
              ((<(Recv,i)> m) ⊑ (<(Recv,i)> MSG v {{ Q }}; p)) | 11.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (iProto_le_trans with "H"). iApply iProto_le_payload_elim_l.
    iIntros "HQ". iApply iProto_le_payload_intro_r. iApply HP; iFrame.
  Qed.

  Global Instance iProto_le_from_modal a v p1 p2 :
    FromModal True (modality_instances.modality_laterN 1) (p1 ⊑ p2)
              ((<a> MSG v; p1) ⊑ (<a> MSG v; p2)) (p1 ⊑ p2).
  Proof. intros _. iApply iProto_le_base. Qed.

End proto.

Typeclasses Opaque iProto_ctx iProto_own.

Global Hint Extern 0 (environments.envs_entails _ (?x ⊑ ?y)) =>
  first [is_evar x; fail 1 | is_evar y; fail 1|iApply iProto_le_refl] : core.
