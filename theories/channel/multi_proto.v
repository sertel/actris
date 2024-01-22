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
From iris.algebra Require Import gmap excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export lib.iprop.
From iris.base_logic Require Import lib.own.
From iris.program_logic Require Import language.
From actris.channel Require Import multi_proto_model.
Set Default Proof Using "Type".
Export action.

(** * Setup of Iris's cameras *)
Class protoG Σ V :=
  protoG_authG ::
    inG Σ (authUR (gmapR natO
      (optionUR (exclR (laterO (proto (leibnizO V) (iPropO Σ) (iPropO Σ))))))).

Definition protoΣ V := #[
  GFunctor (authRF (gmapURF natO (optionRF (exclRF (laterOF (protoOF (leibnizO V) idOF idOF))))))
].
Global Instance subG_chanΣ {Σ V} : subG (protoΣ V) Σ → protoG Σ V.
Proof. solve_inG. Qed.

(* (** * Setup of Iris's cameras *) *)
(* Class protoG Σ V := *)
(*   protoG_authG :: *)
(*     inG Σ (gmapR natO *)
(*       (excl_authR (laterO (proto (leibnizO V) (iPropO Σ) (iPropO Σ))))). *)

(* Definition protoΣ V := #[ *)
(*   GFunctor (gmapRF natO (authRF (optionURF (exclRF (laterOF (protoOF (leibnizO V) idOF idOF)))))) *)
(* ]. *)
(* Global Instance subG_chanΣ {Σ V} : subG (protoΣ V) Σ → protoG Σ V. *)
(* Proof. solve_inG. Qed. *)


(* (** * Setup of Iris's cameras *) *)
(* Class protoG Σ V := *)
(*   protoG_authG :: *)
(*     inG Σ (excl_authR (laterO (proto (leibnizO V) (iPropO Σ) (iPropO Σ)))). *)

(* Definition protoΣ V := #[ *)
(*   GFunctor (authRF (optionURF (exclRF (laterOF (protoOF (leibnizO V) idOF idOF))))) *)
(* ]. *)
(* Global Instance subG_chanΣ {Σ V} : subG (protoΣ V) Σ → protoG Σ V. *)
(* Proof. solve_inG. Qed. *)

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

Notation "<!> m" := (<Send> m) (at level 200, m at level 200) : proto_scope.
Notation "<! x1 .. xn > m" := (<!> ∃ x1, .. (∃ xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<!  x1  ..  xn >  m") : proto_scope.
Notation "<!.. x1 .. xn > m" := (<!> ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<!..  x1  ..  xn >  m") : proto_scope.

Notation "<?> m" := (<Recv> m) (at level 200, m at level 200) : proto_scope.
Notation "<? x1 .. xn > m" := (<?> ∃ x1, .. (∃ xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<?  x1  ..  xn >  m") : proto_scope.
Notation "<?.. x1 .. xn > m" := (<?> ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<?..  x1  ..  xn >  m") : proto_scope.

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
  Lemma iProto_case p : p ≡ END ∨ ∃ a m, p ≡ <a> m.
  Proof.
    rewrite iProto_message_eq iProto_end_eq.
    destruct (proto_case p) as [|(a&m&?)]; [by left|right].
    by exists a, (IMsg m).
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
    iLöb as "IH" forall (p). destruct (iProto_case p) as [->|(a&m&->)].
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
    destruct (iProto_case p1) as [->|(a&m&->)].
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
    iLöb as "IH" forall (p). destruct (iProto_case p) as [->|(a&m&->)].
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
    iLöb as "IH" forall (p1). destruct (iProto_case p1) as [->|(a&m&->)].
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
    iLöb as "IH" forall (p1 p2). destruct (iProto_case p1) as [->|(a&m&->)].
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

Instance iProto_inhabited {Σ V} : Inhabited (iProto Σ V) := populate (END).

Definition can_step {Σ V} (rec : gmap nat (iProto Σ V) → iProp Σ)
           (ps : gmap nat (iProto Σ V)) (i j : nat) : iProp Σ :=
  ∀ m1 m2,
  (ps !!! i ≡ <(Send j)> m1) -∗ (ps !!! j ≡ <Recv i> m2) -∗
  ∀ v p1, iMsg_car m1 v (Next p1) -∗
          ∃ p2, iMsg_car m2 v (Next p2) ∗
                ▷ (rec (<[i:=p1]>(<[j:=p2]>ps))).

Definition iProto_consistent_pre {Σ V} (rec : gmap nat (iProto Σ V) → iProp Σ)
  (ps : gmap nat (iProto Σ V)) : iProp Σ :=
  ∀ i j, can_step rec ps i j.

Global Instance iProto_consistent_pre_ne {Σ V}
       (rec : gmapO natO (iProto Σ V) -n> iPropO Σ) :
  NonExpansive (iProto_consistent_pre (λ ps, rec ps)).
Proof. Admitted.

Program Definition iProto_consistent_pre' {Σ V}
  (rec : gmapO natO (iProto Σ V) -n> iPropO Σ) :
  gmapO natO (iProto Σ V) -n> iPropO Σ :=
  λne ps, iProto_consistent_pre (λ ps, rec ps) ps.

Local Instance iProto_consistent_pre_contractive {Σ V} : Contractive (@iProto_consistent_pre' Σ V).
Proof. Admitted.

Definition iProto_consistent {Σ V} (ps : gmap nat (iProto Σ V)) : iProp Σ :=
  fixpoint iProto_consistent_pre' ps.

Arguments iProto_consistent {_ _} _%proto.
Global Instance: Params (@iProto_consistent) 1 := {}.

Global Instance iProto_consistent_ne {Σ V} : NonExpansive (@iProto_consistent Σ V).
Proof. solve_proper. Qed.
Global Instance iProto_consistent_proper {Σ V} : Proper ((≡) ==> (⊣⊢)) (@iProto_consistent Σ V).
Proof. solve_proper. Qed.

Lemma iProto_consistent_unfold {Σ V} (ps : gmap nat (iProto Σ V)) :
  iProto_consistent ps ≡ (iProto_consistent_pre iProto_consistent) ps.
Proof.
  apply: (fixpoint_unfold iProto_consistent_pre').
Qed.
(* Definition iProto_le {Σ V} (p1 p2 : iProto Σ V) : iProp Σ := *)
(*   ∀ p3, iProto_consistent p1 p3 -∗ iProto_consistent p2 p3. *)
(* Arguments iProto_le {_ _} _%proto _%proto. *)
(* Global Instance: Params (@iProto_le) 2 := {}. *)
(* Notation "p ⊑ q" := (iProto_le p q) : bi_scope. *)

(* Global Instance iProto_le_ne {Σ V} : NonExpansive2 (@iProto_le Σ V). *)
(* Proof. solve_proper. Qed. *)
(* Global Instance iProto_le_proper {Σ V} : Proper ((≡) ==> (≡) ==> (⊣⊢)) (@iProto_le Σ V). *)
(* Proof. solve_proper. Qed. *)

Definition iProto_example1 {Σ V} : gmap nat (iProto Σ V) :=
  ∅.

Lemma iProto_example1_consistent {Σ V} :
  ⊢ iProto_consistent (@iProto_example1 Σ V).
Proof.
  rewrite iProto_consistent_unfold.
  iIntros (i j m1 m2) "Hi Hj".
  rewrite lookup_total_empty.
  by rewrite iProto_end_message_equivI.
Qed.

Definition iProto_example2 `{!invGS Σ} (P : iProp Σ) : gmap nat (iProto Σ Z) :=
  <[0 := (<(Send 1) @ (x:Z)> MSG x {{ P }} ; END)%proto ]>
  (<[1 := (<(Recv 0) @ (x:Z)> MSG x {{ P }} ; END)%proto ]>
   ∅).

Lemma iProto_example2_consistent `{!invGS Σ} (P : iProp Σ) :
  ⊢ iProto_consistent (@iProto_example2 _ Σ invGS0 P).
Proof.
  rewrite iProto_consistent_unfold.
  rewrite /iProto_example2.
  iIntros (i j m1 m2) "Hm1 Hm2".
  destruct i, j.
  - rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    iDestruct "Hm1" as (Hieq) "#Hm1".
    iDestruct "Hm2" as (Hjeq) "#Hm2".
    done.
  - destruct j; last first.
    { rewrite !lookup_total_insert.
      rewrite !iProto_message_equivI.
      iDestruct "Hm1" as (Hieq) "#Hm1". done. }
    rewrite !lookup_total_insert.
    rewrite lookup_total_insert_ne; [|done].
    rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    iDestruct "Hm1" as (Hieq) "#Hm1".
    iDestruct "Hm2" as (Hjeq) "#Hm2".
    iIntros (v p1) "Hm1'".
    iSpecialize ("Hm1" $!v (Next p1)).
    rewrite iMsg_base_eq. simpl.
    rewrite iMsg_exist_eq. simpl.
    iRewrite -"Hm1" in "Hm1'".
    iExists END.
    iSpecialize ("Hm2" $!v (Next END)).
    iRewrite -"Hm2".
    simpl.
    iDestruct "Hm1'" as (x Heq) "[#Heq HP]".
    iSplitL.
    { iExists x. iSplit; [done|]. iFrame. done. }
    iNext. iRewrite -"Heq".
    rewrite insert_commute; [|done].
    rewrite insert_insert.
    rewrite insert_commute; [|done].
    rewrite insert_insert.
    rewrite iProto_consistent_unfold.
    iIntros (i' j' m1' m2') "Hm1' Hm2'".
    destruct i'.
    { rewrite lookup_total_insert.
      iDestruct (iProto_end_message_equivI with "Hm1'") as "H".
      done. }
    destruct i'.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert.
      iDestruct (iProto_end_message_equivI with "Hm1'") as "H".
      done. }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_alt. simpl.
    iDestruct (iProto_end_message_equivI with "Hm1'") as "H".
    done.
  - destruct i; last first.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_alt. simpl.
      iDestruct (iProto_end_message_equivI with "Hm1") as "H".
      done. }
    rewrite !lookup_total_insert.
    rewrite lookup_total_insert_ne; [|done].
    rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    iDestruct "Hm1" as (Hieq) "#Hm1". done.
  - destruct i.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert.
      rewrite !iProto_message_equivI.
      iDestruct "Hm1" as (Hieq) "#Hm1". done. }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_alt. simpl.
    iDestruct (iProto_end_message_equivI with "Hm1") as "H".
    done.
Qed.

Definition iProto_example3 `{!invGS Σ}  : gmap nat (iProto Σ Z) :=
  <[0 := <(Send 1) @ (x:Z)> MSG x ; <(Recv 2)> MSG x; END ]>
  (<[1 := <(Recv 0) @ (x:Z)> MSG x ; <(Send 2)> MSG x; END ]>
  (<[2 := <(Recv 1) @ (x:Z)> MSG x ; <(Send 0)> MSG x; END ]>
    ∅)).

Lemma iProto_example3_consistent `{!invGS Σ} :
  ⊢ iProto_consistent (@iProto_example3 _ Σ invGS0).
Proof.
  rewrite iProto_consistent_unfold.
  rewrite /iProto_example3.
  iIntros (i j m1 m2) "Hm1 Hm2".
  destruct i; last first.
  { destruct i.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite !lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm1" as (Hieq) "#Hm1". }
    destruct i.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert_ne; [|done].
      rewrite !iProto_message_equivI.
      by iDestruct "Hm1" as (Hieq) "#Hm1". }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty=> /=.
    by rewrite iProto_end_message_equivI. }
  destruct j.
  { rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    by iDestruct "Hm2" as (Hjeq) "#Hm2". }
  destruct j; last first.
  { rewrite !lookup_total_insert.
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    destruct j.
    { rewrite !lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm2" as (Hjeq) "#Hm2". }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty=> /=.
    by rewrite iProto_end_message_equivI. }
  rewrite !lookup_total_insert.
  rewrite lookup_total_insert_ne; [|done].
  rewrite !lookup_total_insert.
  rewrite !iProto_message_equivI.
  iDestruct "Hm1" as (Hieq) "#Hm1".
  iDestruct "Hm2" as (Hjeq) "#Hm2".
  iIntros (v p1) "Hm1'".
  iSpecialize ("Hm1" $!v (Next p1)).
  rewrite !iMsg_base_eq.
  rewrite !iMsg_exist_eq.
  iRewrite -"Hm1" in "Hm1'".
  iDestruct "Hm1'" as (x Heq) "[#Hm1' _]".
  iSpecialize ("Hm2" $!v (Next (<Send 2> iMsg_base_def x True END))).
  iExists (<Send 2> iMsg_base_def x True END).
  iRewrite -"Hm2".
  simpl.
  iSplitL.
  { iExists x. iSplit; [done|]. iFrame. done. }
  iNext.
  rewrite iProto_consistent_unfold.
  rewrite insert_commute; [|done].
  rewrite insert_insert.
  rewrite insert_commute; [|done].
  rewrite insert_insert.
  iRewrite -"Hm1'".
  iClear (m1 m2 Hieq Hjeq p1 v Heq) "Hm1 Hm2 Hm1'".
  iIntros (i j m1 m2) "Hm1 Hm2".
  destruct i.
  { rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    by iDestruct "Hm1" as (Hieq) "#Hm1". }
  rewrite lookup_total_insert_ne; [|done].
  destruct i; last first.
  { destruct i.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm1" as (Hieq) "#Hm1". }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty=> /=.
    by rewrite iProto_end_message_equivI. }
  rewrite lookup_total_insert.
  destruct j.
  { rewrite lookup_total_insert.
    rewrite !iProto_message_equivI.
    by iDestruct "Hm2" as (Hjeq) "#Hm2". }
  rewrite lookup_total_insert_ne; [|done].
  destruct j.
  { rewrite lookup_total_insert.
    rewrite !iProto_message_equivI.
    by iDestruct "Hm2" as (Hjeq) "#Hm2". }
  rewrite lookup_total_insert_ne; [|done].
  destruct j; last first.
  { rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty.
    by rewrite iProto_end_message_equivI. }
  rewrite lookup_total_insert.
  rewrite !iProto_message_equivI.
  iDestruct "Hm1" as (Hieq) "#Hm1".
  iDestruct "Hm2" as (Hjeq) "#Hm2".
  iIntros (v p1) "Hm1'".
  iSpecialize ("Hm1" $!v (Next p1)).
  iRewrite -"Hm1" in "Hm1'".
  iDestruct "Hm1'" as (Heq) "[#Hm1' _]".
  iSpecialize ("Hm2" $!v (Next (<Send 0> iMsg_base_def x True END))).
  iExists (<Send 0> iMsg_base_def x True END).
  iRewrite -"Hm2".
  simpl.
  iSplitL.
  { iExists x. iSplit; [done|]. iFrame. done. }
  iNext.
  rewrite iProto_consistent_unfold.
  rewrite (insert_commute _ 1 2); [|done].
  rewrite (insert_commute _ 1 0); [|done].
  rewrite insert_insert.
  rewrite (insert_commute _ 2 0); [|done].
  rewrite (insert_commute _ 2 1); [|done].
  rewrite insert_insert.
  iRewrite -"Hm1'".
  iClear (m1 m2 Hieq Hjeq p1 v Heq) "Hm1 Hm2 Hm1'".
  iIntros (i j m1 m2) "Hm1 Hm2".
  destruct i.
  { rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    by iDestruct "Hm1" as (Hieq) "#Hm1". }
  rewrite lookup_total_insert_ne; [|done].
  destruct i.
  { rewrite lookup_total_insert.
    by rewrite iProto_end_message_equivI. }
  rewrite lookup_total_insert_ne; [|done].
  destruct i; last first.
  { rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty.
    by rewrite iProto_end_message_equivI. }
  rewrite lookup_total_insert.
  destruct j; last first.
  { rewrite lookup_total_insert_ne; [|done].
    destruct j.
    { rewrite lookup_total_insert.
      by rewrite iProto_end_message_equivI. }
    rewrite lookup_total_insert_ne; [|done].
    destruct j.
    { rewrite lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm2" as (Hjeq) "#Hm2". }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty.
    by rewrite iProto_end_message_equivI. }
  rewrite lookup_total_insert.
  rewrite !iProto_message_equivI.
  iDestruct "Hm1" as (Hieq) "#Hm1".
  iDestruct "Hm2" as (Hjeq) "#Hm2".
  iIntros (v p1) "Hm1'".
  iSpecialize ("Hm1" $!v (Next p1)).
  iRewrite -"Hm1" in "Hm1'".
  iDestruct "Hm1'" as (Heq) "[#Hm1' _]".
  iSpecialize ("Hm2" $!v (Next END)).
  iExists END.
  iRewrite -"Hm2".
  simpl.
  iSplitL; [done|].
  rewrite insert_insert.
  rewrite insert_commute; [|done].
  rewrite (insert_commute _ 2 1); [|done].
  rewrite insert_insert.
  iNext.
  iRewrite -"Hm1'".
  rewrite iProto_consistent_unfold.
  iClear (m1 m2 Hieq Hjeq p1 v Heq) "Hm1 Hm2 Hm1'".
  iIntros (i j m1 m2) "Hm1 Hm2".
  destruct i.
  { rewrite lookup_total_insert.
    by rewrite !iProto_end_message_equivI. }
  rewrite lookup_total_insert_ne; [|done].
  destruct i.
  { rewrite lookup_total_insert.
    by rewrite !iProto_end_message_equivI. }
  rewrite lookup_total_insert_ne; [|done].
  destruct i.
  { rewrite lookup_total_insert.
    by rewrite !iProto_end_message_equivI. }
  rewrite lookup_total_insert_ne; [|done].
  rewrite lookup_total_empty.
  by rewrite iProto_end_message_equivI.
Qed.

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
  own γ (◯ ({[i := Excl' (Next p)]})).

(* TODO: Fix this def. *)
Definition iProto_own_auth `{!protoG Σ V} (γ : gname)
    (ps : gmap nat (iProto Σ V)) : iProp Σ :=
  own γ (● ∅).
  (* own γ (● ((λ (p : iProto Σ V), Excl' (Next p)) <$> ps)). *)

Definition iProto_ctx `{protoG Σ V}
    (γ : gname) : iProp Σ :=
  ∃ ps, iProto_own_auth γ ps ∗ ▷ iProto_consistent ps.

(** * The connective for ownership of channel ends *)
Definition iProto_own `{!protoG Σ V}
    (γ : gname) (i : nat) (p : iProto Σ V) : iProp Σ :=
  iProto_own_frag γ i p.
Arguments iProto_own {_ _ _} _ _ _%proto.
Global Instance: Params (@iProto_own) 3 := {}.

Global Instance iProto_own_frag_contractive `{protoG Σ V} γ i :
  Contractive (iProto_own_frag γ i).
Proof. solve_contractive. Qed.

Global Instance iProto_own_contractive `{protoG Σ V} γ i :
  Contractive (iProto_own γ i).
Proof. solve_contractive. Qed.

(** * Proofs *)
Section proto.
  Context `{!protoG Σ V}.
  Implicit Types v : V.
  Implicit Types p pl pr : iProto Σ V.
  Implicit Types m : iMsg Σ V.

  Lemma iProto_consistent_step ps m1 m2 i j v p1 :
    iProto_consistent ps -∗
    ps !!! i ≡ (<(Send j)> m1) -∗
    ps !!! j ≡ (<(Recv i)> m2) -∗
    iMsg_car m1 v (Next p1) -∗
    ∃ p2, iMsg_car m2 v (Next p2) ∗
          ▷ iProto_consistent (<[i := p1]>(<[j := p2]>ps)).
  Proof.
    iIntros "Hprot #Hi #Hj Hm1".
    rewrite iProto_consistent_unfold /iProto_consistent_pre.
    iDestruct ("Hprot" with "Hi Hj Hm1") as (p2) "[Hm2 Hprot]".
    iExists p2. iFrame.
  Qed.

  Global Instance iProto_own_frag_ne γ s : NonExpansive (iProto_own_frag γ s).
  Proof. solve_proper. Qed.

  (* TODO: Relies on above def *)
  Lemma iProto_own_auth_agree γ ps i p :
    iProto_own_auth γ ps -∗ iProto_own_frag γ i p -∗ ▷ (ps !!! i ≡ p).
  Proof. Admitted.
  (*   iIntros "H● H◯". iDestruct (own_valid_2 with "H● H◯") as "H✓". *)
  (*   iDestruct (excl_auth_agreeI with "H✓") as "H✓". *)
  (*   iApply (later_equivI_1 with "H✓"). *)
  (* Qed. *)

  Lemma iProto_own_auth_update γ ps i p p' :
    iProto_own_auth γ ps -∗ iProto_own_frag γ i p ==∗
    iProto_own_auth γ (<[i := p']>ps) ∗ iProto_own_frag γ i p'.
  Proof. Admitted.
  (*   iIntros "H● H◯". iDestruct (own_update_2 with "H● H◯") as "H". *)
  (*   { eapply (excl_auth_update _ _ (Next p'')). } *)
  (*   by rewrite own_op. *)
  (* Qed. *)

  Global Instance iProto_own_ne γ s : NonExpansive (iProto_own γ s).
  Proof. solve_proper. Qed.
  Global Instance iProto_own_proper γ s : Proper ((≡) ==> (≡)) (iProto_own γ s).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_init ps :
    iProto_consistent ps -∗
    |==> ∃ γ, iProto_ctx γ ∗ [∗ map] i ↦p ∈ ps, iProto_own γ i p.
  Proof. Admitted.
  (* iMod (own_alloc (●E (Next p) ⋅ ◯E (Next p))) as (lγ) "[H●l H◯l]". *)
  (* { by apply excl_auth_valid. } *)
  (*   iMod (own_alloc (●E (Next (iProto_dual p)) ⋅ *)
  (*     ◯E (Next (iProto_dual p)))) as (rγ) "[H●r H◯r]". *)
  (*   { by apply excl_auth_valid. } *)
  (*   pose (ProtName lγ rγ) as γ. iModIntro. iExists γ. iSplitL "H●l H●r". *)
  (*   { iExists p, (iProto_dual p). iFrame. iApply iProto_consistent_dual. } *)
  (*   iSplitL "H◯l"; iExists _; iFrame; iApply iProto_le_refl. *)
  (* Qed. *)

  Lemma iProto_step γ i j m1 m2 p1 v :
    iProto_ctx γ -∗
    iProto_own γ i (<(Send j)> m1) -∗
    iProto_own γ j (<(Recv i)> m2) -∗
    iMsg_car m1 v (Next p1) ==∗
    ▷ ∃ p2, iMsg_car m2 v (Next p2) ∗ ▷ iProto_ctx γ ∗
            iProto_own γ i p1 ∗ iProto_own γ j p2.
  Proof.
    iIntros "Hctx Hi Hj Hm".
    iDestruct "Hctx" as (ps) "[Hauth Hconsistent]".
    iDestruct (iProto_own_auth_agree with "Hauth Hi") as "#Hpi".
    iDestruct (iProto_own_auth_agree with "Hauth Hj") as "#Hpj".
    iDestruct (iProto_consistent_step with "Hconsistent [//] [//] [Hm //]") as
      (p2) "[Hm2 Hconsistent]".
    iMod (iProto_own_auth_update _ _ _ _ p1 with "Hauth Hi") as "[Hauth Hi]".
    iMod (iProto_own_auth_update _ _ _ _ p2 with "Hauth Hj") as "[Hauth Hj]".
    iIntros "!>!>". iExists p2. iFrame. iIntros "!>". iExists _. iFrame.
  Qed.

  (* (** The instances below make it possible to use the tactics [iIntros], *)
  (* [iExist], [iSplitL]/[iSplitR], [iFrame] and [iModIntro] on [iProto_le] goals. *) *)
  (* Global Instance iProto_le_from_forall_l {A} a (m1 : A → iMsg Σ V) m2 name : *)
  (*   AsIdentName m1 name → *)
  (*   FromForall (iProto_message Recv (iMsg_exist m1) ⊑ (<a> m2)) *)
  (*              (λ x, (<?> m1 x) ⊑ (<a> m2))%I name | 10. *)
  (* Proof. intros _. apply iProto_le_exist_elim_l. Qed. *)
  (* Global Instance iProto_le_from_forall_r {A} a m1 (m2 : A → iMsg Σ V) name : *)
  (*   AsIdentName m2 name → *)
  (*   FromForall ((<a> m1) ⊑ iProto_message Send (iMsg_exist m2)) *)
  (*              (λ x, (<a> m1) ⊑ (<!> m2 x))%I name | 11. *)
  (* Proof. intros _. apply iProto_le_exist_elim_r. Qed. *)

  (* Global Instance iProto_le_from_wand_l a m v P p : *)
  (*   TCIf (TCEq P True%I) False TCTrue → *)
  (*   FromWand ((<?> MSG v {{ P }}; p) ⊑ (<a> m)) P ((<?> MSG v; p) ⊑ (<a> m)) | 10. *)
  (* Proof. intros _. apply iProto_le_payload_elim_l. Qed. *)
  (* Global Instance iProto_le_from_wand_r a m v P p : *)
  (*   FromWand ((<a> m) ⊑ (<!> MSG v {{ P }}; p)) P ((<a> m) ⊑ (<!> MSG v; p)) | 11. *)
  (* Proof. apply iProto_le_payload_elim_r. Qed. *)

  (* Global Instance iProto_le_from_exist_l {A} (m : A → iMsg Σ V) p : *)
  (*   FromExist ((<! x> m x) ⊑ p) (λ a, (<!> m a) ⊑ p)%I | 10. *)
  (* Proof. *)
  (*   rewrite /FromExist. iDestruct 1 as (x) "H". *)
  (*   iApply (iProto_le_trans with "[] H"). iApply iProto_le_exist_intro_l. *)
  (* Qed. *)
  (* Global Instance iProto_le_from_exist_r {A} (m : A → iMsg Σ V) p : *)
  (*   FromExist (p ⊑ <? x> m x) (λ a, p ⊑ (<?> m a))%I | 11. *)
  (* Proof. *)
  (*   rewrite /FromExist. iDestruct 1 as (x) "H". *)
  (*   iApply (iProto_le_trans with "H"). iApply iProto_le_exist_intro_r. *)
  (* Qed. *)

  (* Global Instance iProto_le_from_sep_l m v P p : *)
  (*   FromSep ((<!> MSG v {{ P }}; p) ⊑ (<!> m)) P ((<!> MSG v; p) ⊑ (<!> m)) | 10. *)
  (* Proof. *)
  (*   rewrite /FromSep. iIntros "[HP H]". *)
  (*   iApply (iProto_le_trans with "[HP] H"). by iApply iProto_le_payload_intro_l. *)
  (* Qed. *)
  (* Global Instance iProto_le_from_sep_r m v P p : *)
  (*   FromSep ((<?> m) ⊑ (<?> MSG v {{ P }}; p)) P ((<?> m) ⊑ (<?> MSG v; p)) | 11. *)
  (* Proof. *)
  (*   rewrite /FromSep. iIntros "[HP H]". *)
  (*   iApply (iProto_le_trans with "H"). by iApply iProto_le_payload_intro_r. *)
  (* Qed. *)

  (* Global Instance iProto_le_frame_l q m v R P Q p : *)
  (*   Frame q R P Q → *)
  (*   Frame q R ((<!> MSG v {{ P }}; p) ⊑ (<!> m)) *)
  (*             ((<!> MSG v {{ Q }}; p) ⊑ (<!> m)) | 10. *)
  (* Proof. *)
  (*   rewrite /Frame /=. iIntros (HP) "[HR H]". *)
  (*   iApply (iProto_le_trans with "[HR] H"). iApply iProto_le_payload_elim_r. *)
  (*   iIntros "HQ". iApply iProto_le_payload_intro_l. iApply HP; iFrame. *)
  (* Qed. *)
  (* Global Instance iProto_le_frame_r q m v R P Q p : *)
  (*   Frame q R P Q → *)
  (*   Frame q R ((<?> m) ⊑ (<?> MSG v {{ P }}; p)) *)
  (*             ((<?> m) ⊑ (<?> MSG v {{ Q }}; p)) | 11. *)
  (* Proof. *)
  (*   rewrite /Frame /=. iIntros (HP) "[HR H]". *)
  (*   iApply (iProto_le_trans with "H"). iApply iProto_le_payload_elim_l. *)
  (*   iIntros "HQ". iApply iProto_le_payload_intro_r. iApply HP; iFrame. *)
  (* Qed. *)

  (* Global Instance iProto_le_from_modal a v p1 p2 : *)
  (*   FromModal True (modality_instances.modality_laterN 1) (p1 ⊑ p2) *)
  (*             ((<a> MSG v; p1) ⊑ (<a> MSG v; p2)) (p1 ⊑ p2). *)
  (* Proof. intros _. apply iProto_le_base. Qed. *)

End proto.

(* Typeclasses Opaque iProto_ctx iProto_own. *)

(* Global Hint Extern 0 (environments.envs_entails _ (?x ⊑ ?y)) => *)
(*   first [is_evar x; fail 1 | is_evar y; fail 1|iApply iProto_le_refl] : core. *)
