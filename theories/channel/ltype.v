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
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export lib.iprop.
From iris.base_logic Require Import lib.own.
From iris.program_logic Require Import language.
From actris.channel Require Import ltype_model.
Set Default Proof Using "Type".
Export action.

(** * Setup of Iris's cameras *)

Class ltypeG Σ V :=
  ltypeG_authG :>
    inG Σ (excl_authR (laterO (ltype (leibnizO V) (iPropO Σ) (iPropO Σ)))).

Definition ltypeΣ V := #[
  GFunctor (authRF (optionURF (exclRF (laterOF (ltypeOF (leibnizO V) idOF idOF)))))
].
Instance subG_chanΣ {Σ V} : subG (ltypeΣ V) Σ → ltypeG Σ V.
Proof. solve_inG. Qed.

(** * Types *)
Definition iLType Σ V := ltype V (iPropO Σ) (iPropO Σ).
Delimit Scope ltype_scope with ltype.
Bind Scope ltype_scope with iLType.
Local Open Scope ltype.

(** * Messages *)
Section iLMsg.
  Set Primitive Projections.
  Record iLMsg Σ V := ILMsg { iLMsg_car : V → laterO (iLType Σ V) -n> iPropO Σ }.
End iLMsg.
Arguments ILMsg {_ _} _.
Arguments iLMsg_car {_ _} _.

Delimit Scope lmsg_scope with lmsg.
Bind Scope lmsg_scope with iLMsg.
Instance iLMsg_inhabited {Σ V} : Inhabited (iLMsg Σ V) := populate (ILMsg inhabitant).

Section ilmsg_ofe .
  Context {Σ : gFunctors} {V : Type}.

  Instance iLMsg_equiv : Equiv (iLMsg Σ V) := λ m1 m2,
    ∀ w p, iLMsg_car m1 w p ≡ iLMsg_car m2 w p.
  Instance iLMsg_dist : Dist (iLMsg Σ V) := λ n m1 m2,
    ∀ w p, iLMsg_car m1 w p ≡{n}≡ iLMsg_car m2 w p.

  Lemma iLMsg_ofe_mixin : OfeMixin (iLMsg Σ V).
  Proof. by apply (iso_ofe_mixin (iLMsg_car : _ → V -d> _ -n> _)). Qed.
  Canonical Structure iLMsgO := Ofe (iLMsg Σ V) iLMsg_ofe_mixin.

  Global Instance iLMsg_cofe : Cofe iLMsgO.
  Proof. by apply (iso_cofe (ILMsg : (V -d> _ -n> _) → _) iLMsg_car). Qed.
End ilmsg_ofe.

Program Definition iLMsg_base_def {Σ V}
    (v : V) (P : iProp Σ) (p : iLType Σ V) : iLMsg Σ V :=
  ILMsg (λ v', λne p', ⌜ v = v' ⌝ ∗ Next p ≡ p' ∗ P)%I.
Next Obligation. solve_proper. Qed.
Definition iLMsg_base_aux : seal (@iLMsg_base_def). by eexists. Qed.
Definition iLMsg_base := iLMsg_base_aux.(unseal).
Definition iLMsg_base_eq : @iLMsg_base = @iLMsg_base_def := iLMsg_base_aux.(seal_eq).
Arguments iLMsg_base {_ _} _%V _%I _%ltype.
Instance: Params (@iLMsg_base) 3 := {}.

Program Definition iLMsg_exist_def {Σ V A} (m : A → iLMsg Σ V) : iLMsg Σ V :=
  ILMsg (λ v', λne p', ∃ x, iLMsg_car (m x) v' p')%I.
Next Obligation. solve_proper. Qed.
Definition iLMsg_exist_aux : seal (@iLMsg_exist_def). by eexists. Qed.
Definition iLMsg_exist := iLMsg_exist_aux.(unseal).
Definition iLMsg_exist_eq : @iLMsg_exist = @iLMsg_exist_def := iLMsg_exist_aux.(seal_eq).
Arguments iLMsg_exist {_ _ _} _%lmsg.
Instance: Params (@iLMsg_exist) 3 := {}.

Definition iLMsg_texist {Σ V} {TT : tele} (m : TT → iLMsg Σ V) : iLMsg Σ V :=
  tele_fold (@iLMsg_exist Σ V) (λ x, x) (tele_bind m).
Arguments iLMsg_texist {_ _ !_} _%lmsg /.

Notation "'LMSG' v {{ P } } ; p" := (iLMsg_base v P p)
  (at level 200, v at level 20, right associativity,
   format "'LMSG'  v  {{  P  } } ;  p") : lmsg_scope.
Notation "'LMSG' v ; p" := (iLMsg_base v True p)
  (at level 200, v at level 20, right associativity,
   format "LMSG  v ;  p") : lmsg_scope.
Notation "∃ x .. y , m" :=
  (iLMsg_exist (λ x, .. (iLMsg_exist (λ y, m)) ..)%lmsg) : lmsg_scope.
Notation "'∃..' x .. y , m" :=
  (iLMsg_texist (λ x, .. (iLMsg_texist (λ y, m)) .. )%lmsg)
  (at level 200, x binder, y binder, right associativity,
   format "∃..  x  ..  y ,  m") : lmsg_scope.

(** * Operators *)
Definition iLType_end_def {Σ V} : iLType Σ V := ltype_end.
Definition iLType_end_aux : seal (@iLType_end_def). by eexists. Qed.
Definition iLType_end := iLType_end_aux.(unseal).
Definition iLType_end_eq : @iLType_end = @iLType_end_def := iLType_end_aux.(seal_eq).
Arguments iLType_end {_ _}.

Definition iLType_message_def {Σ V} (a : action) (m : iLMsg Σ V) : iLType Σ V :=
  ltype_message a (iLMsg_car m).
Definition iLType_message_aux : seal (@iLType_message_def). by eexists. Qed.
Definition iLType_message := iLType_message_aux.(unseal).
Definition iLType_message_eq :
  @iLType_message = @iLType_message_def := iLType_message_aux.(seal_eq).
Arguments iLType_message {_ _} _ _%lmsg.
Instance: Params (@iLType_message) 3 := {}.

Notation "'LEND'" := iLType_end : ltype_scope.

Notation "< a > m" := (iLType_message a m)
  (at level 200, a at level 10, m at level 200,
   format "< a >  m") : ltype_scope.
Notation "< a @ x1 .. xn > m" := (iLType_message a (∃ x1, .. (∃ xn, m) ..))
  (at level 200, a at level 10, x1 closed binder, xn closed binder, m at level 200,
   format "< a  @  x1  ..  xn >  m") : ltype_scope.
Notation "< a @.. x1 .. xn > m" := (iLType_message a (∃.. x1, .. (∃.. xn, m) ..))
  (at level 200, a at level 10, x1 closed binder, xn closed binder, m at level 200,
   format "< a  @..  x1  ..  xn >  m") : ltype_scope.

Notation "<! x > m" := (<Send x> m) (at level 200, x at level 10, m at level 200) : ltype_scope.
Notation "<! x , x1 .. xn > m" := (<Send x> (∃ x1, .. (∃ xn, m) ..))
  (at level 200, x1 closed binder, xn closed binder, x at level 10, m at level 200, 
   format "<! x , x1  ..  xn > m") : ltype_scope.
Notation "<!.. x , x1 .. xn > m" := (<Send x> ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, x at level 10, m at level 200,
   format "<!..  x , x1  ..  xn > m") : ltype_scope.

Notation "<? x > m" := (<Recv x> m) (at level 200, x at level 10, m at level 200) : ltype_scope.
Notation "<? x , x1 .. xn > m" := (<Recv x> (∃ x1, .. (∃ xn, m) ..))
  (at level 200, x1 closed binder, xn closed binder, x at level 10, m at level 200, 
   format "<? x , x1  ..  xn > m") : ltype_scope.
Notation "<?.. x , x1 .. xn > m" := (<Recv x> ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, x at level 10, m at level 200,
   format "<?..  x , x1  ..  xn > m") : ltype_scope.

(** * Operations *)
Program Definition iLMsg_map {Σ V}
    (rec : iLType Σ V → iLType Σ V) (m : iLMsg Σ V) : iLMsg Σ V :=
  ILMsg (λ v, λne p1', ∃ p1, iLMsg_car m v (Next p1) ∗ p1' ≡ Next (rec p1))%I.
Next Obligation. solve_proper. Qed.

Program Definition iLType_map_app_aux {Σ V}
    (f : action → action) (p2 : iLType Σ V)
    (rec : iLType Σ V -n> iLType Σ V) : iLType Σ V -n> iLType Σ V := λne p,
  ltype_elim p2 (λ a m,
    ltype_message (f a) (iLMsg_car (iLMsg_map rec (ILMsg m)))) p.
Next Obligation.
  intros Σ V f p2 rec n p1 p1' Hp. apply ltype_elim_ne=> // a m1 m2 Hm.
  apply ltype_message_ne=> v p' /=. by repeat f_equiv.
Qed.

Instance iLType_map_app_aux_contractive {Σ V} f (p2 : iLType Σ V) :
  Contractive (iLType_map_app_aux f p2).
Proof.
  intros n rec1 rec2 Hrec p1; simpl. apply ltype_elim_ne=> // a m1 m2 Hm.
  apply ltype_message_ne=> v p' /=. by repeat (f_contractive || f_equiv).
Qed.

Definition iLType_map_app {Σ V} (f : action → action)
    (p2 : iLType Σ V) : iLType Σ V -n> iLType Σ V :=
  fixpoint (iLType_map_app_aux f p2).

Definition iLType_app_def {Σ V} (p1 p2 : iLType Σ V) : iLType Σ V :=
  iLType_map_app id p2 p1.
Definition iLType_app_aux : seal (@iLType_app_def). Proof. by eexists. Qed.
Definition iLType_app := iLType_app_aux.(unseal).
Definition iLType_app_eq : @iLType_app = @iLType_app_def := iLType_app_aux.(seal_eq).
Arguments iLType_app {_ _} _%ltype _%ltype.
Instance: Params (@iLType_app) 2 := {}.
Infix "<++>" := iLType_app (at level 60) : ltype_scope.
Notation "m <++> p" := (iLMsg_map (flip iLType_app p) m) : lmsg_scope.

Definition dest (a : action) :=
  match a with
  | Send x => x
  | Recv x => x
  end.

Definition dual_act x a :=
  match a with
  | Send _ => Recv x
  | Recv _ => Send x
  end.

Definition ltype_env Σ V := gmap nat (iLType Σ V).
Definition ltype_envO Σ V := gmap.gmapO nat (iLType Σ V).

Local Instance Dist_ltype_env  Σ V : Dist (ltype_env Σ V) := gmap.gmap_dist.

(*

1 : bool -> 2
1 : int -> 3


1: Send bool 2; Send int 3
2: Recv bool 1
3: Recv int 1 

------



1: Recv bool 2; Recv int 3
2: Send bool 1
3: Send int 1 

newChan : unit -> chan
send    : chan -> recv_id -> payload -> ()
recv    : chan -> send_id -> payload


newChan : unit -> chan
send    : chan -> payload -> ()
recv    : chan -> payload


-----

1 -> 2
3 -> 4

-----

1: Send nat 4; Recv bool 2; Recv int 3
2: Send bool 1
3: Send int 1 
4: Recv nat 1


*)

Definition isKey {A B} (a : A) (p : A * B) := fst p = a.
Instance isKey_dec {A B : Type} {EqA : EqDecision A} (a : A) (p : A * B) : Decision (isKey a p).
Proof. apply EqA. Qed.



Definition remove_from_list {A} (P : A -> Prop) {DecP : forall x, Decision (P x)} (xs : list A) :=
  match list_find P xs with
  | Some (n, x) => Some (x, delete n xs)
  | None        => None
  end.

 
Definition iLType_wf_pre {Σ V} (rec : ltype_env Σ V → iProp Σ) : 
  ltype_env Σ V → iProp Σ := 
  (λ lenv, 
   (∀ x le, lenv !! x ≡ Some le -∗ le ≡ LEND) ∨
   ∃ source dest ms md,
     ⌜ source <> dest ⌝ ∗
     lenv !! source ≡ Some (<! dest> ms) ∗
     lenv !! dest ≡ Some (<? source> md) ∗
     (∀v les, iLMsg_car ms v (Next les) -∗
              ∃ led, iLMsg_car md v (Next led) ∗
                     ▷(rec (<[source := les]> (<[dest := led]> lenv)))))%I.         

Program Instance iLType_wf_ne {Σ V} rec : 
  NonExpansive (@iLType_wf_pre Σ V rec).
Next Obligation.
  
Admitted.

  Program Definition iLType_wf_pre' {Σ V}
          (rec : ltype_envO Σ V -n> iPropO Σ) :
    ltype_envO Σ V -n> iPropO Σ :=
    λne lenv,
    (iLType_wf_pre (λ lenv', rec lenv') lenv).

  Local Instance iLType_wf_contractive {Σ V} : 
    Contractive (@iLType_wf_pre' Σ V).
    Admitted.
(*
  Proof.
    rewrite /project_pre' /project_pre /project_aux => n f f' H2 gt lt; simpl.
    rewrite iLType_message_eq /iLType_message_def.
    repeat (f_contractive || f_equiv);
      apply dist_later_dist; assumption.
  Qed.
  *)

  Definition iLType_wf {Σ V} (lenv : ltype_envO Σ V) : iPropO Σ :=
    fixpoint iLType_wf_pre' lenv.

(** * Protocol entailment *)

(*


                 p1 <: p2           p1 <: p2          p1 <: !B.p3    ?A.p3 <: p2
----------   ----------------   ----------------     ----------------------------
end <: end    !A.p1 <: !A.p2     ?A.p1 <: ?A.p2             ?A.p1 <: !B.p2

                 p1 <: p2               p1 <: p2     
----------   -------------------   ----------------    
end <: end    !x A.p1 <: !x A.p2     ?A.p1 <: ?A.p2            

  p1 <: !y B.p3    !x A.p3 <: p2
 ------------------------------- x ≠ y
      !x A.p1 <: !y B.p2

*)


Definition iLType_le_pre {Σ V}
    (rec : iLType Σ V → iLType Σ V → iProp Σ) (lty1 lty2 : iLType Σ V) : iProp Σ :=
  (lty1 ≡ LEND ∗ lty2 ≡ LEND) ∨
  ∃ a1 a2 m1 m2,
    (lty1 ≡ <a1> m1) ∗ (lty2 ≡ <a2> m2) ∗
    match a1, a2 with
    | Recv x, Recv y => 
      (⌜x = y⌝ -∗
       ∀ v lty1',
            iLMsg_car m1 v (Next lty1') -∗ 
                      ∃ lty2', ▷ rec lty1' lty2' ∗ iLMsg_car m2 v (Next lty2'))
    | Send x, Send y => 
      (⌜x = y⌝ -∗ ∀ v lty2',
            iLMsg_car m2 v (Next lty2') -∗ 
                      ∃ lty1', ▷ rec lty1' lty2' ∗ iLMsg_car m1 v (Next lty1'))(* ∨
      (⌜x ≠ y⌝ ∗ ∀ v1 v2 lty1' lty2',
       iLMsg_car m1 v1 (Next lty1') -∗ iLMsg_car m2 v2 (Next lty2') -∗ ∃ pt,
         ▷ rec lty1' (<! y> LMSG v2; pt) ∗ ▷ rec (<! x> LMSG v1; pt) lty2')*)
    | Recv x, Send y => ∀ v1 v2 lty1' lty2',
       iLMsg_car m1 v1 (Next lty1') -∗ iLMsg_car m2 v2 (Next lty2') -∗ ∃ pt,
         ▷ rec lty1' (<! y> LMSG v2; pt) ∗ ▷ rec (<? x> LMSG v1; pt) lty2' 
    | Send _, Recv _ => False
    end.

Instance iLType_le_pre_ne {Σ V} (rec : iLType Σ V → iLType Σ V → iProp Σ) :
  NonExpansive2 (iLType_le_pre rec).
Proof. solve_proper. Qed.

Program Definition iLType_le_pre' {Σ V}
    (rec : iLType Σ V -n> iLType Σ V -n> iPropO Σ) :
    iLType Σ V -n> iLType Σ V -n> iPropO Σ := λne lty1 lty2,
  iLType_le_pre (λ lty1' lty2', rec lty1' lty2') lty1 lty2.
Solve Obligations with solve_proper.

Local Instance iLType_le_pre_contractive {Σ V} : 
  Contractive (@iLType_le_pre' Σ V).
Proof.
  intros n rec1 rec2 Hrec lty1 lty2. rewrite /iLType_le_pre' /iLType_le_pre /=.
  by repeat (f_contractive || f_equiv).
Qed.

Definition iLType_le {Σ V} (lty1 lty2 : iLType Σ V) : iProp Σ :=
  fixpoint iLType_le_pre' lty1 lty2.
Arguments iLType_le {_ _} _%ltype _%ltype.
Instance: Params (@iLType_le) 2 := {}.
Notation "p ⊑ q" := (iLType_le p q) : bi_scope.


Instance iLType_le_ne {Σ V} : NonExpansive2 (@iLType_le Σ V).
Proof. solve_proper. Qed.
Instance iLType_le_proper {Σ V} : Proper ((≡) ==> (≡) ==> (⊣⊢)) (@iLType_le Σ V).
Proof. solve_proper. Qed.

Fixpoint iLType_app_recvs {Σ V} (vs : list (nat * V)) (p : iLType Σ V) : iLType Σ V :=
  match vs with
  | [] => p
  | v :: vs => <? (fst v)> LMSG (snd v); iLType_app_recvs vs p
  end.

Definition iLType_interp {Σ V} (vs : gmap nat (list (nat * V)))
           (ltys : ltype_env Σ V) : iProp Σ :=  
  ⌜ List.map fst (map_to_list vs) ≡ List.map fst (map_to_list ltys) ⌝ ∗
    (∃ltys' : ltype_env Σ V,
        ⌜ List.map fst (map_to_list vs) ≡ List.map fst (map_to_list ltys') ⌝ ∗
          iLType_wf ltys' ∗
        [∗ map] k ↦ lty ∈ ltys,
                ∃bs lty',
                  ⌜ vs !! k ≡ Some bs ∧ ltys' !! k ≡ Some lty' ⌝ ∗
                  iLType_app_recvs bs lty' ⊑ lty).

Definition ltype_name := gmap nat gname.
Instance ltype_name_inhabited : Inhabited ltype_name := _.
Instance ltype_name_eq_dec : EqDecision ltype_name := _.
Instance ltype_name_countable : Countable ltype_name.
Proof.
  refine (inj_countable id Some _); by intros [].
Qed.  

Definition iLType_own_frag `{!ltypeG Σ V} (γ : ltype_name) (x : nat)
           (p : iLType Σ V) : iProp Σ :=
  ∃γlt : gname, ⌜ γ !! x = Some γlt ⌝ ∗ own γlt (◯E (Next p)).

Definition iLType_own_auth `{!ltypeG Σ V} (γ : ltype_name) (x : nat)
    (p : iLType Σ V) : iProp Σ :=
  ∃γlt : gname, ⌜ γ !! x = Some γlt ⌝ ∗ own γlt (●E (Next p)).

Definition iLtype_ctx `{ltypeG Σ V}
    (γ : ltype_name) (vs : gmap nat (list (nat * V))) : iProp Σ :=
  ∃ ltys,
    map_fold (λ k lty acc, iLType_own_auth γ k lty ∗ acc) 
             (▷ (iLType_interp vs ltys)) ltys.

(** * The connective for ownership of channel ends *)
Definition iLType_own `{!ltypeG Σ V}
    (γ : ltype_name) (x : nat) (p : iLType Σ V) : iProp Σ :=
  ∃ p', ▷ (p' ⊑ p) ∗ iLType_own_frag γ x p'.
Arguments iLType_own {_ _ _} _ _%ltype.
Instance: Params (@iLType_own) 3 := {}.

(** * Proofs *)
Section ltype.
  Context `{!ltypeG Σ V}.
  Implicit Types v : V.
  Implicit Types lty : iLType Σ V.
  Implicit Types m : iLMsg Σ V.

  (** ** Equality *)
  Lemma iLType_case lt : lt ≡ LEND ∨ ∃ a m, lt ≡ <a> m.
  Proof.
    rewrite iLType_message_eq iLType_end_eq.
    destruct (ltype_case lt) as [|(a&m&?)]; [by left|right].
    by exists a, (ILMsg m).
  Qed.
  Lemma iLType_message_equivI `{!BiInternalEq SPROP} a1 a2 m1 m2 :
    (<a1> m1) ≡ (<a2> m2) ⊣⊢@{SPROP} ⌜ a1 = a2 ⌝ ∧
      (∀ v lp, iLMsg_car m1 v lp ≡ iLMsg_car m2 v lp).
  Proof. rewrite iLType_message_eq. apply ltype_message_equivI. Qed.
  Lemma iLType_message_end_equivI `{!BiInternalEq SPROP} a m :
    (<a> m) ≡ LEND ⊢@{SPROP} False.
  Proof. rewrite iLType_message_eq iLType_end_eq. apply ltype_message_end_equivI. Qed.
  Lemma iLType_end_message_equivI `{!BiInternalEq SPROP} a m :
    LEND ≡ (<a> m) ⊢@{SPROP} False.
  Proof. by rewrite internal_eq_sym iLType_message_end_equivI. Qed.

  (** ** Non-expansiveness of operators *)
  Global Instance iLMsg_contractive v n :
    Proper (dist n ==> dist_later n ==> dist n) (iLMsg_base (Σ:=Σ) (V:=V) v).
  Proof. rewrite iLMsg_base_eq=> P1 P2 HP p1 p2 Hp w q /=. solve_contractive. Qed.
  Global Instance iLMsg_ne v : NonExpansive2 (iLMsg_base (Σ:=Σ) (V:=V) v).
  Proof. rewrite iLMsg_base_eq=> P1 P2 HP p1 p2 Hp w q /=. solve_proper. Qed.
  Global Instance iLMsg_proper v :
    Proper ((≡) ==> (≡) ==> (≡)) (iLMsg_base (Σ:=Σ) (V:=V) v).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance iLMsg_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (@iLMsg_exist Σ V A).
  Proof. rewrite iLMsg_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.
  Global Instance iLMsg_exist_proper A :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@iLMsg_exist Σ V A).
  Proof. rewrite iLMsg_exist_eq=> m1 m2 Hm v p /=. f_equiv =>x. apply Hm. Qed.

  Global Instance iLType_message_ne a :
    NonExpansive (iLType_message (Σ:=Σ) (V:=V) a).
  Proof. rewrite iLType_message_eq. solve_proper. Qed.
  Global Instance iLType_message_proper a :
    Proper ((≡) ==> (≡)) (iLType_message (Σ:=Σ) (V:=V) a).
  Proof. apply (ne_proper _). Qed.

  (** Helpers *)
  Lemma iLMsg_map_base f v P lty :
    NonExpansive f →
    iLMsg_map f (LMSG v {{ P }}; lty) ≡ (LMSG v {{ P }}; f lty)%lmsg.
  Proof.
    rewrite iLMsg_base_eq. intros ? v' lty'; simpl. iSplit.
    - iDestruct 1 as (lty'') "[(->&Hlty&$) Hlty']". iSplit; [done|].
      iRewrite "Hlty'". iIntros "!>". by iRewrite "Hlty".
    - iIntros "(->&Hlty'&$)". iExists lty. iRewrite -"Hlty'". auto.
  Qed.
  Lemma iLMsg_map_exist {A} f (m : A → iLMsg Σ V) :
    iLMsg_map f (∃ x, m x) ≡ (∃ x, iLMsg_map f (m x))%lmsg.
  Proof.
    rewrite iLMsg_exist_eq. intros v' lty'; simpl. iSplit.
    - iDestruct 1 as (lty'') "[H Hlty']". iDestruct "H" as (x) "H"; auto.
    - iDestruct 1 as (x lty'') "[Hm Hp']". auto.
  Qed.

  (** **  Well foundedness *)
  Global Instance iiLType_wf_ne : NonExpansive (@iLType_wf Σ V).
  Proof. rewrite /iLType_wf. solve_proper. Qed.
  Global Instance iLType_wf_proper : Proper ((≡) ==> (≡)) (@iLType_wf Σ V).
  Proof. apply (ne_proper _). Qed.

  Lemma iLType_wf_end (env : ltype_env Σ V) : 
    (∀ x lty, env !! x ≡ Some lty -∗ lty ≡ LEND) -∗
    iLType_wf env.
  Proof.
    iIntros "Henv".
    unfold iLType_wf.
    iApply (fixpoint_unfold iLType_wf_pre').
    unfold iLType_wf_pre' at 1.
    simpl.
    unfold iLType_wf_pre.
    iLeft.
    iAssumption.
  Qed.

  (** ** Append *)
  Global Instance iLType_app_end_l : LeftId (≡) LEND (@iLType_app Σ V).
  Proof.
    intros p. rewrite iLType_end_eq iLType_app_eq /iLType_app_def /iLType_map_app.
    etrans; [apply (fixpoint_unfold (iLType_map_app_aux _ _))|]; simpl.
    by rewrite ltype_elim_end.
  Qed.
  Lemma iLType_app_message a m p2 : (<a> m) <++> p2 ≡ <a> m <++> p2.
  Proof.
    rewrite iLType_message_eq iLType_app_eq /iLType_app_def /iLType_map_app.
    etrans; [apply (fixpoint_unfold (iLType_map_app_aux _ _))|]; simpl.
    apply: ltype_elim_message=> a' m1 m2 Hm. f_equiv; solve_proper.
  Qed.

  Global Instance iLType_app_ne : NonExpansive2 (@iLType_app Σ V).
  Proof.
    assert (∀ n, Proper (dist n ==> (=) ==> dist n) (@iLType_app Σ V)).
    { intros n p1 p1' Hp1 p2 p2' <-. by rewrite iLType_app_eq /iLType_app_def Hp1. }
    assert (Proper ((≡) ==> (=) ==> (≡)) (@iLType_app Σ V)).
    { intros p1 p1' Hp1 p2 p2' <-. by rewrite iLType_app_eq /iLType_app_def Hp1. }
    intros n p1 p1' Hp1 p2 p2' Hp2. rewrite Hp1. clear p1 Hp1.
    revert p1'. induction (lt_wf n) as [n _ IH]; intros p1.
    destruct (iLType_case p1) as [->|(a&m&->)].
    { by rewrite !left_id. }
    rewrite !iLType_app_message. f_equiv=> v p' /=. do 4 f_equiv.
    f_contractive. apply IH; eauto using dist_le with lia.
  Qed.
  Global Instance iLType_app_proper : Proper ((≡) ==> (≡) ==> (≡)) (@iLType_app Σ V).
  Proof. apply (ne_proper_2 _). Qed.

  Lemma iLMsg_app_base v P lty1 lty2 :
    ((LMSG v {{ P }}; lty1) <++> lty2)%lmsg ≡ (LMSG v {{ P }}; lty1 <++> lty2)%lmsg.
  Proof. apply: iLMsg_map_base. Qed.
  Lemma iLMsg_app_exist {A} (m : A → iLMsg Σ V) lty2 :
    ((∃ x, m x) <++> lty2)%lmsg ≡ (∃ x, m x <++> lty2)%lmsg.
  Proof. apply iLMsg_map_exist. Qed.

  Global Instance iLType_app_end_r : RightId (≡) LEND (@iLType_app Σ V).
  Proof.
    intros lty. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (lty). destruct (iLType_case lty) as [->|(a&m&->)].
    { by rewrite left_id. }
    rewrite iLType_app_message.
    iApply iLType_message_equivI; iSplit; [done|]; iIntros (v lty') "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (lty1') "[H Hlty']". iRewrite "Hlty'".
      iApply (internal_eq_rewrite); [|done]; iIntros "!>".
      by iRewrite ("IH" $! lty1').
    - iIntros "H". destruct (Next_uninj lty') as [lty'' Hlty']. iExists lty''.
      rewrite Hlty'. iSplitL; [by auto|]. iIntros "!>". by iRewrite ("IH" $! lty'').
  Qed.
  Global Instance iLType_app_assoc : Assoc (≡) (@iLType_app Σ V).
  Proof.
    intros lty1 lty2 lty3. apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iLöb as "IH" forall (lty1). destruct (iLType_case lty1) as [->|(a&m&->)].
    { by rewrite !left_id. }
    rewrite !iLType_app_message.
    iApply iLType_message_equivI; iSplit; [done|]; iIntros (v lty123) "/=".
    iApply prop_ext; iIntros "!>". iSplit.
    - iDestruct 1 as (lty1') "[H #Hlty']".
      iExists (lty1' <++> lty2). iSplitL; [by auto|].
      iRewrite "Hlty'". iIntros "!>". iApply "IH".
    - iDestruct 1 as (lty12) "[H #Hlty123]". iDestruct "H" as (lty1') "[H #Hlty12]".
      iExists lty1'. iFrame "H". iRewrite "Hlty123".
      iIntros "!>". iRewrite "Hlty12". by iRewrite ("IH" $! lty1').
  Qed.

  (** ** Protocol entailment **)
  Lemma iLType_le_unfold lty1 lty2 : iLType_le lty1 lty2 ≡ iLType_le_pre iLType_le lty1 lty2.
  Proof. apply: (fixpoint_unfold iLType_le_pre'). Qed.

  Lemma iLType_le_end : ⊢ LEND ⊑ (LEND : iLType Σ V).
  Proof. rewrite iLType_le_unfold. iLeft. auto 10. Qed.

  Lemma iLType_le_send x y m1 m2 :
    (⌜x = y⌝ -∗ ∀ v lty2', iLMsg_car m2 v (Next lty2') -∗ ∃ lty1',
      ▷ (lty1' ⊑ lty2') ∗ iLMsg_car m1 v (Next lty1')) -∗
    (<! x> m1) ⊑ (<! y> m2).
  Proof.
    rewrite iLType_le_unfold; iIntros "H"; iRight.
    iExists (Send x), (Send y), m1, m2; auto.
  Qed.
(*
  Lemma iLType_le_send_swap x y m1 m2 (Hxy : x ≠ y) :
    (∀ v1 v2 lty1' lty2',
       iLMsg_car m1 v1 (Next lty1') -∗ iLMsg_car m2 v2 (Next lty2') -∗ ∃ ltyt,
         ▷ (lty1' ⊑ <!y> LMSG v2; ltyt) ∗ ▷ ((<!x> LMSG v1; ltyt) ⊑ lty2')) -∗
    (<!x> m1) ⊑ (<!y> m2).
  Proof.
    rewrite iLType_le_unfold; iIntros "H"; iRight.
    iExists (Send x), (Send y), m1, m2; auto.
  Qed.

  Lemma iLType_le_sends x y m1 m2 :
    (⌜ x = y ⌝ -∗ (∀ v lty2', iLMsg_car m2 v (Next lty2') -∗ ∃ lty1',
      ▷ (lty1' ⊑ lty2') ∗ iLMsg_car m1 v (Next lty1'))) -∗ (*
    (⌜ x ≠ y⌝ ∗ (∀ v1 v2 lty1' lty2',
       iLMsg_car m1 v1 (Next lty1') -∗ iLMsg_car m2 v2 (Next lty2') -∗ ∃ ltyt,
          ▷ (lty1' ⊑ <!y> LMSG v2; ltyt) ∗ ▷ ((<!x> LMSG v1; ltyt) ⊑ lty2'))) -∗ *)
    (<!x> m1) ⊑ (<!y> m2).
  Proof.
    iIntros "Hsend".
    rewrite iLType_le_unfold. iRight.
    iExists (Send x), (Send y), m1, m2.
    iSplit; [auto|].
    iSplit; [auto|].
    destruct (nat_eq_dec x y); [subst|]; auto.
  Qed.
*)  
  Lemma iLType_le_recv x y m1 m2 :
      
    (⌜x = y⌝ -∗ ∀ v lty1', iLMsg_car m1 v (Next lty1') -∗ ∃ lty2',
      ▷ (lty1' ⊑ lty2') ∗ iLMsg_car m2 v (Next lty2')) -∗
    (<? x> m1) ⊑ (<? y> m2).
  Proof.
    rewrite iLType_le_unfold; iIntros "H"; iRight.
    iExists (Recv x), (Recv y), m1, m2; auto.
  Qed.

  Lemma iLType_le_swap x y m1 m2 :
    (∀ v1 v2 lty1' lty2',
       iLMsg_car m1 v1 (Next lty1') -∗ iLMsg_car m2 v2 (Next lty2') -∗ ∃ ltyt,
         ▷ (lty1' ⊑ <!y> LMSG v2; ltyt) ∗ ▷ ((<?x> LMSG v1; ltyt) ⊑ lty2')) -∗
    (<?x> m1) ⊑ (<!y> m2).
  Proof.
    rewrite iLType_le_unfold; iIntros "H"; iRight.
    iExists (Recv x), (Send y), m1, m2; auto.
  Qed.

  Lemma iLType_le_end_inv_l lty : lty ⊑ LEND -∗ (lty ≡ LEND).
  Proof.
    rewrite iLType_le_unfold. iIntros "[[Hlty _]|H] //".
    iDestruct "H" as (a1 a2 m1 m2) "(_ & Heq & _)".
    by iDestruct (iLType_end_message_equivI with "Heq") as %[].
  Qed.

  Lemma iLType_le_end_inv_r lty : LEND ⊑ lty -∗ (lty ≡ LEND).
  Proof.
    rewrite iLType_le_unfold. iIntros "[[_ Hp]|H] //".
    iDestruct "H" as (a1 a2 m1 m2) "(Heq & _ & _)".
    iDestruct (iLType_end_message_equivI with "Heq") as %[].
  Qed.

  Lemma iLType_le_send_inv x p1 m2 :
    p1 ⊑ (<! x> m2) -∗ 
       ∃ a1 m1,
         (p1 ≡ <a1> m1) ∗
         ((∃y, ⌜ a1 ≡ Send y ⌝ ∗ 
              (⌜x = y⌝ -∗ ∀v p2',
                iLMsg_car m2 v (Next p2') -∗ ∃ p1',
                    ▷ (p1' ⊑ p2') ∗ iLMsg_car m1 v (Next p1'))) ∨ (*
          (∃y, ⌜ a1 ≡ Send y ∧ y ≠ x ⌝ ∗
               ∀ v1 v2 p1' p2',
                 iLMsg_car m1 v1 (Next p1') -∗ iLMsg_car m2 v2 (Next p2') -∗ ∃ pt,
                     ▷ (p1' ⊑ <! x> LMSG v2; pt) ∗ ▷ ((<! y> LMSG v1; pt) ⊑ p2')) ∨ *)
          (∃y, ⌜ a1 ≡ Recv y ⌝ ∗
               ∀ v1 v2 p1' p2',
                 iLMsg_car m1 v1 (Next p1') -∗ iLMsg_car m2 v2 (Next p2') -∗ ∃ pt,
                     ▷ (p1' ⊑ <! x> LMSG v2; pt) ∗ ▷ ((<? y> LMSG v1; pt) ⊑ p2'))).
  Proof.
    rewrite iLType_le_unfold. iIntros "[[_ Heq]|H]".
    { iDestruct (iLType_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 m1 m2') "(Hp1 & Hp2 & H)".
    iExists _, _; iSplit; [done|]. destruct a1, a2.
    - iDestruct (iLType_message_equivI with "Hp2") as (Heq) "{Hp2} #Hm".
      simplify_eq.
      iLeft; iExists n. iSplitR; [auto|]. iIntros (Heq v p2') "Hm2". subst.
      iApply "H"; [auto|]. 
      by iRewrite -("Hm" $! v (Next p2')).
    - done.
    - iRight; iExists n; iSplitR; [auto|]; iIntros (v1 v2 p1' p2') "Hm1 Hm2".
      iDestruct (iLType_message_equivI with "Hp2") as (Heq) "{Hp2} #Hm";
        simplify_eq.
      iApply ("H" with "Hm1"). by iRewrite -("Hm" $! v2 (Next p2')).
    - iDestruct (iLType_message_equivI with "Hp2") as ([=]) "_".
  Qed.

  Lemma iLType_le_send_send_inv x m1 m2 v p2' :
    (<! x> m1) ⊑ (<! x> m2) -∗
    iLMsg_car m2 v (Next p2') -∗ ∃ p1', ▷ (p1' ⊑ p2') ∗ iLMsg_car m1 v (Next p1').
  Proof.
    iIntros "H Hm2". iDestruct (iLType_le_send_inv with "H") as (a m1') "[Hm1 H]".
    iDestruct (iLType_message_equivI with "Hm1") as (<-) "Hm1".
    iDestruct "H" as "[H | H]".
    - iDestruct "H" as (y) "[#Heq H]".
      iDestruct "Heq" as %Heq. simplify_eq.
      assert (y = y) by auto.
      iSpecialize  ("H" $!H with "Hm2").
      iDestruct "H" as (p1') "[H1 H2]".
      iExists p1'.
      iRewrite ("Hm1" $! v (Next p1')).
      auto with iFrame.
    - iDestruct "H" as (y H) "_". simplify_eq.
  Qed.
(*
  
  Lemma iLType_le_send_send2_inv x y m1 m2 v1 v2 p1' p2' (H : x ≠ y) :
    (<! x> m1) ⊑ (<! y> m2) -∗
    iLMsg_car m1 v1 (Next p1') -∗ iLMsg_car m2 v2 (Next p2') -∗ ∃ pt,
      ▷ (p1' ⊑ <! y> LMSG v2; pt) ∗ ▷ ((<! x> LMSG v1; pt) ⊑ p2').
  Proof.
    iIntros "H Hm1 Hm2". iDestruct (iLType_le_send_inv with "H") as (a m1') "[Heq H]".
    iDestruct (iLType_message_equivI with "Heq") as (<-) "#Hmeq".
(*    iDestruct "H" as "[[Heq' H] | [H | H]]".*)
    iDestruct "H" as "[[Heq' H] | H]".
    - iDestruct "Heq'" as %Heq; simplify_eq.
(*    - iDestruct "H" as (z [Heq Hzy]) "H"; simplify_eq.
      iApply ("H" with "[Hm1]"); [|iAssumption]. 
      iRewrite -("Hmeq" $! v1 (Next p1')); iAssumption. *)
    - iDestruct "H" as (z Heq) "H". simplify_eq.
  Qed.
   *)
  
  Lemma iLType_le_recv_send_inv x y m1 m2 v1 v2 p1' p2' :
    (<? x> m1) ⊑ (<! y> m2) -∗
    iLMsg_car m1 v1 (Next p1') -∗ iLMsg_car m2 v2 (Next p2') -∗ ∃ pt,
      ▷ (p1' ⊑ <! y> LMSG v2; pt) ∗ ▷ ((<? x> LMSG v1; pt) ⊑ p2').
  Proof.
    iIntros "H Hm1 Hm2". iDestruct (iLType_le_send_inv with "H") as (a m1') "[Hm H]".
    iDestruct (iLType_message_equivI with "Hm") as (<-) "{Hm} #Hm".
    iDestruct "H" as "[H | H]".
    - iDestruct "H" as (z) "[#Heq _]".
      iDestruct "Heq" as %Heq; simplify_eq.
(*    - iDestruct "H" as (z [Heq _]) "H"; simplify_eq.*)
    - iDestruct "H" as (z Heq) "H"; simplify_eq.
      iApply ("H" with "[Hm1] Hm2"). by iRewrite -("Hm" $! v1 (Next p1')).
  Qed.

  Lemma iLType_le_recv_inv x p1 m2 :
    p1 ⊑ (<? x> m2) -∗ ∃ m1,
      ∃y, (p1 ≡ <? y> m1) ∗
      (⌜x = y⌝ -∗ ∀ v p1', iLMsg_car m1 v (Next p1') -∗ ∃ p2',
        ▷ (p1' ⊑ p2') ∗ iLMsg_car m2 v (Next p2')).
  Proof.
    
    rewrite iLType_le_unfold. iIntros "[[_ Heq]|H]".
    { iDestruct (iLType_message_end_equivI with "Heq") as %[]. }
    iDestruct "H" as (a1 a2 m1 m2') "(Hp1 & Hp2 & H)".
    iExists m1.
    iDestruct (iLType_message_equivI with "Hp2") as (<-) "{Hp2} #Hm2".
    destruct a1; [done|].
    iExists n.
    iSplitL "Hp1"; [auto|].
    iIntros (Heq v p1') "Hm1"; subst.
    assert (n = n) by auto.
    iSpecialize  ("H" $!H with "Hm1").

    iDestruct "H" as (p2') "[Hle Hm]".
    iExists p2'. iIntros "{$Hle}". by iRewrite ("Hm2" $! v (Next p2')).
  Qed.

  Lemma iLType_le_recv_recv_inv x m1 m2 v p1' :
    (<? x> m1) ⊑ (<? x> m2) -∗
    iLMsg_car m1 v (Next p1') -∗ ∃ p2', ▷ (p1' ⊑ p2') ∗ iLMsg_car m2 v (Next p2').
  Proof.
    iIntros "H Hm2". iDestruct (iLType_le_recv_inv with "H") as (m1' y) "[Hm1 H]".
    iDestruct (iLType_message_equivI with "Hm1") as (Heq) "Hm1". simplify_eq.
    iApply "H"; [auto|].
    by iRewrite -("Hm1" $! v (Next p1')).
  Qed.

  Lemma iLType_le_refl (p : iLType Σ V) : ⊢ p ⊑ p.
  Proof.
    iLöb as "IH" forall (p). destruct (iLType_case p) as [->|([]&m&->)].
    - iApply iLType_le_end.
    - iApply iLType_le_send. auto 10 with iFrame.
    - iApply iLType_le_recv. auto 10 with iFrame.
  Qed.

  Lemma iLType_le_trans (p1 p2 p3 : iLType Σ V) : p1 ⊑ p2 -∗ p2 ⊑ p3 -∗ p1 ⊑ p3.
  Proof.
    (*

    iIntros "H1 H2". iLöb as "IH" forall (p1 p2 p3).
    destruct (iLType_case p3) as [->|([]&m3&->)].
    - iDestruct (iLType_le_end_inv_l with "H2") as "H2". by iRewrite "H2" in "H1".
    - iDestruct (iLType_le_send_inv with "H2") as (a2 m2) "[Hp2 H2]".
      iRewrite "Hp2" in "H1"; clear p2. destruct a2.
      + iDestruct (iLType_le_send_inv with "H1") as (a1 m1) "[Hp1 H1]".
        iRewrite "Hp1"; clear p1. destruct a1. 
        * iDestruct "H1" as "[[#Heq H1] | H1]". iDestruct "Heq" as %Heq; simplify_eq.
          iDestruct "H2" as "[[#Heq H2] | H2]". iDestruct "Heq" as %Heq; simplify_eq.
          iApply iLType_le_send; iIntros (v p3') "Hm3".
          iDestruct ("H2" with "Hm3") as (p2') "[Hle Hm2]".
          iDestruct ("H1" with "Hm2") as (p1') "[Hle' Hm1]".
          iExists p1'. iIntros "{$Hm1} !>". by iApply ("IH" with "Hle'").
          iDestruct "H2" as (y) "[Heq _]".
          iDestruct "Heq" as %Heq; simplify_eq.
          iDestruct "H1" as (y) "[Heq _]".
          iDestruct "Heq" as %Heq; simplify_eq.
        * iApply iLType_le_swap. iIntros (v1 v3 p1' p3') "Hm1 Hm3".
          iDestruct "H1" as "[[Heq H1] | H1]".
          iDestruct "Heq" as %Heq; simplify_eq.
          iDestruct "H1" as (y) "[Heq H1]".
          iDestruct "Heq" as %Heq; simplify_eq.
          iDestruct "H2" as "[[Heq H2] | H2]".
          iDestruct "Heq" as %Heq; simplify_eq.
          iDestruct ("H2" with "Hm3") as (p2') "[Hle Hm2]".
          iDestruct ("H1" with "Hm1 Hm2") as (pt) "[Hp1' Hp2']".
          iExists pt. iIntros "{$Hp1'} !>". by iApply ("IH" with "Hp2'").
          iDestruct "H2" as (y') "[Heq _]".
          iDestruct "Heq" as %Heq; simplify_eq.

 (*        * { iDestruct "H1" as "[[Heq H1] | [H1 | H1]]". 
            - iDestruct "Heq" as %Heq; simplify_eq.
              iDestruct "H2" as "[[Heq H2] | [H2 | H2]]".
              + iDestruct "Heq" as %Heq; simplify_eq.
                iApply iLType_le_send. iIntros (v p3') "Hm3".
                iDestruct ("H2" with "Hm3") as (p2') "[Hle Hm2]".
                iDestruct ("H1" with "Hm2") as (p1') "[Hle' Hm1]".
                iExists p1'. iIntros "{$Hm1} !>". by iApply ("IH" with "Hle'").
              + iDestruct "H2" as (y [Heq Hineq]) "H2"; simplify_eq.
                iApply iLType_le_send_swap; [assumption|].
                iIntros (v1 v2 lty1' lty2') "Hm1 Hm3".
                admit.
              + iDestruct "H2" as (y) "[Heq _]".
                iDestruct "Heq" as %Heq; simplify_eq.
            - iDestruct "H2" as "[[Heq H2] | [H2 | H2]]".
              iDestruct "Heq" as %Heq; simplify_eq.
              iDestruct "H1" as (y) "[#[Heq Hneq] H1]".
              iDestruct "Heq" as %Heq. simplify_eq.
              iDestruct "Hneq" as %Hneq.
              
          }
        * iApply iLType_le_sends. iIntros (v p3') "Hm3".
          iDestruct ("H2" with "Hm3") as (p2') "[Hle Hm2]".
          iDestruct ("H1" with "Hm2") as (p1') "[Hle' Hm1]".
          iExists p1'. iIntros "{$Hm1} !>". by iApply ("IH" with "Hle'").
        * iApply iLType_le_swap. iIntros (v1 v3 p1' p3') "Hm1 Hm3".
          iDestruct ("H2" with "Hm3") as (p2') "[Hle Hm2]".
          iDestruct ("H1" with "Hm1 Hm2") as (pt) "[Hp1' Hp2']".
          iExists pt. iIntros "{$Hp1'} !>". by iApply ("IH" with "Hp2'"). *)
      + iDestruct (iLType_le_recv_inv with "H1") as (m1) "[Hp1 H1]".
        iRewrite "Hp1"; clear p1. iApply iLType_le_swap.
        iIntros (v1 v3 p1' p3') "Hm1 Hm3".
        iDestruct ("H1" with "Hm1") as (p2') "[Hle Hm2]".
        iDestruct "H2" as "[[Heq _] | H2]".
        iDestruct "Heq" as %Heq; simplify_eq.
        iDestruct "H2" as (y) "[Heq H2]".
        iDestruct "Heq" as %Heq; simplify_eq.
        iDestruct ("H2" with "Hm2 Hm3") as (pt) "[Hp2' Hp3']".
        iExists pt. iIntros "{$Hp3'} !>". by iApply ("IH" with "Hle").
    - iDestruct (iLType_le_recv_inv with "H2") as (m2) "[Hp2 H3]".
      iRewrite "Hp2" in "H1".
      iDestruct (iLType_le_recv_inv with "H1") as (m1) "[Hp1 H2]".
      iRewrite "Hp1". iApply iLType_le_recv. iIntros (v p1') "Hm1".
      iDestruct ("H2" with "Hm1") as (p2') "[Hle Hm2]".
      iDestruct ("H3" with "Hm2") as (p3') "[Hle' Hm3]".
      iExists p3'. iIntros "{$Hm3} !>". by iApply ("IH" with "Hle").
  Qed.
     *)
    Admitted.
  Lemma iLType_le_payload_elim_l a m v P p x:
    (P -∗ (<? x> LMSG v; p) ⊑ (<a> m)) -∗
    (<? x> LMSG v {{ P }}; p) ⊑ (<a> m).
  Proof.
    rewrite iLMsg_base_eq. iIntros "H". destruct a.
    - iApply iLType_le_swap. iIntros (v1 v2 p1' p2') "/= (#?&#?&HP) Hm2 /=". 
      iApply (iLType_le_recv_send_inv with "(H HP)"); simpl; auto.
    - iApply iLType_le_recv. iIntros (Heq v' p') "(->&Hp&HP)". subst.
      iApply (iLType_le_recv_recv_inv with "(H HP)"); simpl; auto.
  Qed.
  
  Lemma iLType_le_payload_elim_r a m v P p x :
    (P -∗ (<a> m) ⊑ (<! x> LMSG v; p)) -∗
    (<a> m) ⊑ (<! x> LMSG v {{ P }}; p).
  Proof.
    rewrite iLMsg_base_eq. iIntros "H". destruct a.
    - iApply iLType_le_send. iIntros (Hnx v' p') "(->&Hp&HP)"; subst.
      iApply (iLType_le_send_send_inv with "(H HP)"); simpl; auto.
    - iApply iLType_le_swap. iIntros (v1 v2 p1' p2') "/= Hm1 (->&#?&HP) /=".
      iApply (iLType_le_recv_send_inv with "(H HP) Hm1"); simpl; auto.
  Qed.
  Lemma iLType_le_payload_intro_l v P (p : iLType Σ V) x :
    P -∗ (<! x> LMSG v {{ P }}; p) ⊑ (<! x> LMSG v; p).
  Proof.
    rewrite iLMsg_base_eq.
    iIntros "HP". iApply iLType_le_send. iIntros (_ v' p') "(->&Hp&_) /=".
    iExists p'. iSplitR; [iApply iLType_le_refl|]. auto.
  Qed.
  Lemma iLType_le_payload_intro_r x v P (p :iLType Σ V) :
    P -∗ (<? x> LMSG v; p) ⊑ (<? x> LMSG v {{ P }}; p).
  Proof.
    rewrite iLMsg_base_eq.
    iIntros "HP". iApply iLType_le_recv. iIntros (_ v' p') "(->&Hp&_) /=".
    iExists p'. iSplitR; [iApply iLType_le_refl|]. auto.
  Qed.

  Lemma iLType_le_exist_elim_l {A} (m1 : A → iLMsg Σ V) a m2 y :
    (∀ x : A, (<? y> m1 x) ⊑ (<a> m2)) -∗
    (<? y, x> m1 x) ⊑ (<a> m2).
  Proof.
    rewrite iLMsg_exist_eq. iIntros "H". destruct a.
    - iApply iLType_le_swap. iIntros (v1 v2 p1' p2') "/= Hm1 Hm2 /=".
      iDestruct "Hm1" as (x) "Hm1".
      iApply (iLType_le_recv_send_inv with "H Hm1 Hm2").
    - iApply iLType_le_recv. iIntros (Heq v p1') "/="; subst. iDestruct 1 as (x) "Hm".
      by iApply (iLType_le_recv_recv_inv with "H").
  Qed.

  Lemma iLType_le_exist_elim_l_inhabited `{!Inhabited A} (m : A → iLMsg Σ V) p y :
    (∀ x, (<? y> m x) ⊑ p) -∗
    (<? y, x> m x) ⊑ p.
  Proof.
    rewrite iLMsg_exist_eq. iIntros "H".
    destruct (iLType_case p) as [Heq | [a [m' Heq]]].
    - unshelve iSpecialize ("H" $!inhabitant); first by apply _.
      rewrite Heq.
      iDestruct (iLType_le_end_inv_l with "H") as "H".
      rewrite iLType_end_eq iLType_message_eq.
      iDestruct (ltype_message_end_equivI with "H") as "[]".
    - iEval (rewrite Heq). destruct a.
      + iApply iLType_le_swap. iIntros (v1 v2 p1' p2') "/= Hm1 Hm2 /=".
        iDestruct "Hm1" as (x) "Hm1".
        iSpecialize ("H" $! x). rewrite Heq.
        iApply (iLType_le_recv_send_inv with "H Hm1 Hm2").
      + iApply iLType_le_recv. iIntros (Heq' v p1') "/="; subst. iDestruct 1 as (x) "Hm".
        iSpecialize ("H" $! x). rewrite Heq.
        by iApply (iLType_le_recv_recv_inv with "H").
  Qed.

  Lemma iLType_le_exist_elim_r {A} a m1 (m2 : A → iLMsg Σ V) y :
    (∀ x, (<a> m1) ⊑ (<!y> m2 x)) -∗
    (<a> m1) ⊑ (<! y, x> m2 x).
  Proof.
    rewrite iLMsg_exist_eq. iIntros "H". destruct a.
    - iApply iLType_le_send. iIntros (Heq v p2'); subst. iDestruct 1 as (x) "Hm".
      by iApply (iLType_le_send_send_inv with "H").
    - iApply iLType_le_swap. iIntros (v1 v2 p1' p2') "/= Hm1".
      iDestruct 1 as (x) "Hm2".
      iApply (iLType_le_recv_send_inv with "H Hm1 Hm2").
  Qed.
  Lemma iLType_le_exist_elim_r_inhabited `{Hinh : Inhabited A} p (m : A → iLMsg Σ V) y :
    (∀ x, p ⊑ (<!y > m x)) -∗
    p ⊑ (<! y, x> m x).
  Proof.
    rewrite iLMsg_exist_eq. iIntros "H".
    destruct (iLType_case p) as [Heq | [a [m' Heq]]].
    - unshelve iSpecialize ("H" $!inhabitant); first by apply _.
      rewrite Heq.
      iDestruct (iLType_le_end_inv_r with "H") as "H".
      rewrite iLType_end_eq iLType_message_eq.
      iDestruct (ltype_message_end_equivI with "H") as "[]".
    - iEval (rewrite Heq). destruct a.
      + iApply iLType_le_send. iIntros (Heq' v p2'); subst. iDestruct 1 as (x) "Hm".
        iSpecialize ("H" $! x). rewrite Heq.
        by iApply (iLType_le_send_send_inv with "H").
      + iApply iLType_le_swap. iIntros (v1 v2 p1' p2') "/= Hm1".
        iDestruct 1 as (x) "Hm2".
        iSpecialize ("H" $! x). rewrite Heq.
        iApply (iLType_le_recv_send_inv with "H Hm1 Hm2").
  Qed.
  Lemma iLType_le_exist_intro_l {A} (m : A → iLMsg Σ V) a y :
    ⊢ (<! y, x> m x) ⊑ (<!y > m a).
  Proof.
    rewrite iLMsg_exist_eq. iApply iLType_le_send. iIntros (_ v p') "Hm /=".
    iExists p'. iSplitR; last by auto. iApply iLType_le_refl.
  Qed.
  Lemma iLType_le_exist_intro_r {A} (m : A → iLMsg Σ V) a y :
    ⊢ (<?y > m a) ⊑ (<? y, x> m x).
  Proof.
    rewrite iLMsg_exist_eq. iApply iLType_le_recv. iIntros (_ v p') "Hm /=".
    iExists p'. iSplitR; last by auto. iApply iLType_le_refl.
  Qed.

  Lemma iLType_le_texist_elim_l {TT : tele} (m1 : TT → iLMsg Σ V) a m2 y :
    (∀ x, (<?y > m1 x) ⊑ (<a> m2)) -∗
    (<?..y, x> m1 x) ⊑ (<a> m2).
  Proof.
    iIntros "H". iInduction TT as [|T TT] "IH"; simpl; [done|].
    iApply iLType_le_exist_elim_l; iIntros (x).
    iApply "IH". iIntros (xs). iApply "H".
  Qed.
  Lemma iLType_le_texist_elim_r {TT : tele} a m1 (m2 : TT → iLMsg Σ V) y :
    (∀ x, (<a> m1) ⊑ (<! y> m2 x)) -∗
    (<a> m1) ⊑ (<!.. y, x> m2 x).
  Proof.
    iIntros "H". iInduction TT as [|T TT] "IH"; simpl; [done|].
    iApply iLType_le_exist_elim_r; iIntros (x).
    iApply "IH". iIntros (xs). iApply "H".
  Qed.
  Lemma iLType_le_texist_intro_l {TT : tele} (m : TT → iLMsg Σ V) x y :
    ⊢ (<!..y, x> m x) ⊑ (<!y> m x). 
  Proof.
    induction x as [|T TT x xs IH]; simpl; [iApply iLType_le_refl|].
    iApply iLType_le_trans; [by iApply iLType_le_exist_intro_l|]. iApply IH.
  Qed.
  Lemma iLType_le_texist_intro_r {TT : tele} (m : TT → iLMsg Σ V) x y:
    ⊢ (<?y> m x) ⊑ (<?.. y, x> m x).
  Proof.
    induction x as [|T TT x xs IH]; simpl; [iApply iLType_le_refl|].
    iApply iLType_le_trans; [|by iApply iLType_le_exist_intro_r]. iApply IH.
  Qed.

  Lemma iLType_le_base a v P p1 (p2 : iLType Σ V):
    ▷ (p1 ⊑ p2) -∗
    (<a> LMSG v {{ P }}; p1) ⊑ (<a> LMSG v {{ P }}; p2).
  Proof.
    rewrite iLMsg_base_eq. iIntros "H". destruct a.
    - iApply iLType_le_send. iIntros (_ v' p') "(->&Hp&$)".
      iExists p1. iSplit; [|by auto]. iIntros "!>". by iRewrite -"Hp".
    - iApply iLType_le_recv. iIntros (_ v' p') "(->&Hp&$)".
      iExists p2. iSplit; [|by auto]. iIntros "!>". by iRewrite -"Hp".
  Qed.

  Lemma iLType_le_base_swap v1 v2 P1 P2 (p : iLType Σ V) x y:
    ⊢ (<? x> LMSG v1 {{ P1 }}; <! y> LMSG v2 {{ P2 }}; p)
    ⊑ (<! y> LMSG v2 {{ P2 }}; <? x> LMSG v1 {{ P1 }}; p).
  Proof.
    rewrite {1 3}iLMsg_base_eq. iApply iLType_le_swap.
    iIntros (v1' v2' p1' p2') "/= (->&#Hp1&HP1) (->&#Hp2&HP2)". iExists p.
    iSplitL "HP2".
    - iIntros "!>". iRewrite -"Hp1". by iApply iLType_le_payload_intro_l.
    - iIntros "!>". iRewrite -"Hp2". by iApply iLType_le_payload_intro_r.
  Qed.
(*
  Lemma iLType_le_dual p1 p2 : p2 ⊑ p1 -∗ iLType_dual p1 ⊑ iLType_dual p2.
  Proof.
    iIntros "H". iLöb as "IH" forall (p1 p2).
    destruct (iLType_case p1) as [->|([]&m1&->)].
    - iDestruct (iLType_le_end_inv_l with "H") as "H".
      iRewrite "H". iApply iLType_le_refl.
    - iDestruct (iLType_le_send_inv with "H") as (a2 m2) "[Hp2 H]".
      iRewrite "Hp2"; clear p2. iEval (rewrite !iLType_dual_message).
      destruct a2; simpl.
      + iApply iLType_le_recv. iIntros (v p1d).
        iDestruct 1 as (p1') "[Hm1 #Hp1d]".
        iDestruct ("H" with "Hm1") as (p2') "[H Hm2]".
        iDestruct ("IH" with "H") as "H". iExists (iLType_dual p2').
        iSplitL "H"; [iIntros "!>"; by iRewrite "Hp1d"|]. simpl; auto.
      + iApply iLType_le_swap. iIntros (v1 v2 p1d p2d).
        iDestruct 1 as (p1') "[Hm1 #Hp1d]". iDestruct 1 as (p2') "[Hm2 #Hp2d]".
        iDestruct ("H" with "Hm2 Hm1") as (pt) "[H1 H2]".
        iDestruct ("IH" with "H1") as "H1". iDestruct ("IH" with "H2") as "H2 {IH}".
        rewrite !iLType_dual_message /=. iExists (iLType_dual pt). iSplitL "H2".
        * iIntros "!>". iRewrite "Hp1d". by rewrite -iMsg_dual_base.
        * iIntros "!>". iRewrite "Hp2d". by rewrite -iMsg_dual_base.
    - iDestruct (iLType_le_recv_inv with "H") as (m2) "[Hp2 H]".
      iRewrite "Hp2"; clear p2. iEval (rewrite !iLType_dual_message /=).
      iApply iLType_le_send. iIntros (v p2d).
      iDestruct 1 as (p2') "[Hm2 #Hp2d]".
      iDestruct ("H" with "Hm2") as (p1') "[H Hm1]".
      iDestruct ("IH" with "H") as "H". iExists (iLType_dual p1').
      iSplitL "H"; [iIntros "!>"; by iRewrite "Hp2d"|]. simpl; auto.
  Qed.
*)
  Lemma iLType_le_amber_internal (p1 p2 : iLType Σ V → iLType Σ V)
      `{Contractive p1, Contractive p2}:
    □ (∀ rec1 rec2, ▷ (rec1 ⊑ rec2) → p1 rec1 ⊑ p2 rec2) -∗
    fixpoint p1 ⊑ fixpoint p2.
  Proof.
    iIntros "#H". iLöb as "IH".
    iEval (rewrite (fixpoint_unfold p1)).
    iEval (rewrite (fixpoint_unfold p2)).
    iApply "H". iApply "IH".
  Qed.
  Lemma iLType_le_amber_external (p1 p2 : iLType Σ V → iLType Σ V)
      `{Contractive p1, Contractive p2}:
    (∀ rec1 rec2, (⊢ rec1 ⊑ rec2) → ⊢ p1 rec1 ⊑ p2 rec2) →
    ⊢ fixpoint p1 ⊑ fixpoint p2.
  Proof.
    intros IH. apply fixpoint_ind.
    - by intros p1' p2' -> ?.
    - exists (fixpoint p2). iApply iLType_le_refl.
    - intros p' ?. rewrite (fixpoint_unfold p2). by apply IH.
    - apply bi.limit_preserving_entails; [done|solve_proper].
  Qed.
(*
  Lemma iLType_le_dual_l p1 p2 : iLType_dual p2 ⊑ p1 -∗ iLType_dual p1 ⊑ p2.
  Proof.
    iIntros "H". iEval (rewrite -(involutive iLType_dual p2)).
    by iApply iLType_le_dual.
  Qed.
  Lemma iLType_le_dual_r p1 p2 : p2 ⊑ iLType_dual p1 -∗ p1 ⊑ iLType_dual p2.
  Proof.
    iIntros "H". iEval (rewrite -(involutive iLType_dual p1)).
    by iApply iLType_le_dual.
  Qed.
*)
  Lemma iLType_le_app (p1 p2 p3 p4 : iLType Σ V) :
    p1 ⊑ p2 -∗ p3 ⊑ p4 -∗ p1 <++> p3 ⊑ p2 <++> p4.
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (p1 p2 p3 p4).
    destruct (iLType_case p2) as [->|([]&m2&->)].
    - iDestruct (iLType_le_end_inv_l with "H1") as "H1".
      iRewrite "H1". by rewrite !left_id.
    - iDestruct (iLType_le_send_inv with "H1") as (a1 m1) "[Hp1 H1]".
      iRewrite "Hp1"; clear p1. rewrite !iLType_app_message. destruct a1; simpl.
      + iApply iLType_le_send. iIntros (Heq v p24); subst.
        iDestruct 1 as (p2') "[Hm2 #Hp24]".
        iDestruct "H1" as "[H1 | H1]"; [|iDestruct "H1" as (y) "[%Heq _]"; simplify_eq].
        iDestruct "H1" as (y) "[%Heq H1]"; simplify_eq.
        iDestruct ("H1" $!eq_refl with "Hm2") as (p1') "[H1 Hm1]".
        iExists (p1' <++> p3). iSplitR "Hm1"; [|by simpl; eauto].
        iIntros "!>". iRewrite "Hp24". by iApply ("IH" with "H1").
      + iApply iLType_le_swap. iIntros (v1 v2 p13 p24).
        iDestruct 1 as (p1') "[Hm1 #Hp13]". iDestruct 1 as (p2') "[Hm2 #Hp24]".
        iDestruct "H1" as "[H1 | H1]"; [iDestruct "H1" as (y) "[%Heq _]"; simplify_eq|].
        iDestruct "H1" as (y) "[%Heq H1]"; simplify_eq.
        iSpecialize ("H1" with "Hm1 Hm2").
        iDestruct "H1" as (pt) "[H1 H1']".
        iExists (pt <++> p3). iSplitL "H1".
        * iIntros "!>". iRewrite "Hp13".
          rewrite /= -iLMsg_app_base -iLType_app_message.
          iApply ("IH" with "H1"). iApply iLType_le_refl.
        * iIntros "!>". iRewrite "Hp24".
          rewrite /= -iLMsg_app_base -iLType_app_message.
          iApply ("IH" with "H1' H2").
    - iDestruct (iLType_le_recv_inv with "H1") as (m1 y) "[Hp1 H1]".
      iRewrite "Hp1"; clear p1. rewrite !iLType_app_message. iApply iLType_le_recv.
      iIntros (Heq v p13); subst. iDestruct 1 as (p1') "[Hm1 #Hp13]".
      iDestruct ("H1" $!eq_refl with "Hm1") as (p2'') "[H1 Hm2]".
      iExists (p2'' <++> p4). iSplitR "Hm2"; [|by simpl; eauto].
      iIntros "!>". iRewrite "Hp13". by iApply ("IH" with "H1").
  Qed.

  (** ** Lemmas about the auxiliary definitions and invariants *)
  Global Instance iLType_app_recvs_ne vs :
    NonExpansive (iLType_app_recvs (Σ:=Σ) (V:=V) vs).
  Proof. induction vs; solve_proper. Qed.
  Global Instance iLType_app_recvs_proper vs :
    Proper ((≡) ==> (≡)) (iLType_app_recvs (Σ:=Σ) (V:=V) vs).
  Proof. induction vs; solve_proper. Qed.
  (*
  Global Instance iLType_interp_ne vs ltys :
    NonExpansive2 (iLType_interp (Σ:=Σ) (V:=V) vs ltys).
  Proof. solve_proper. Qed.
  Global Instance iLType_interp_proper vs ltys :
    Proper ((≡) ==> (≡) ==> (≡)) (iLType_interp (Σ:=Σ) (V:=V) vs ltys).
  Proof. apply (ne_proper_2 _). Qed.
*)
  Global Instance iLType_own_frag_ne γ s : NonExpansive (iLType_own_frag γ s).
  Proof. solve_proper. Qed.

  Lemma iLType_own_auth_agree γ s p p' :
    iLType_own_auth γ s p -∗ iLType_own_frag γ s p' -∗ ▷ (p ≡ p').
  Proof.
    iIntros "[%y1 [%Heq1 H●]] [%y2 [%Heq2 H◯]]"; simplify_eq; clear Heq1.
    iDestruct (own_valid_2 with "H● H◯") as "H✓".
    iDestruct (excl_auth_agreeI with "H✓") as "H✓".
    iApply (later_equivI_1 with "H✓").
  Qed.

  Lemma iLType_own_auth_update γ s p p' p'' :
    iLType_own_auth γ s p -∗ iLType_own_frag γ s p' ==∗
    iLType_own_auth γ s p'' ∗ iLType_own_frag γ s p''.
  Proof.
    iIntros "[%y1 [%Heq1 H●]] [%y2 [%Heq2 H◯]]"; simplify_eq; subst.
    iDestruct (own_update_2 with "H● H◯") as "H".
    { eapply (excl_auth_update _ _ (Next p'')). }
    rewrite own_op.
    iApply bupd_mono; [|iAssumption].
    iIntros "[H● H◯]"; iSplitL "H●".
    + iExists y1; iSplitR; done.
    + iExists y1; iSplitR; done.
  Qed.

  (* TODO: Move somewhere else *)
  Lemma false_disj_cong (P Q Q' : iProp Σ) :
    (P ⊢ False) → (Q ⊣⊢ Q') → (P ∨ Q ⊣⊢ Q').
  Proof. intros HP ->. apply (anti_symm _). by rewrite HP left_id. auto. Qed.

  Lemma pure_sep_cong (φ1 φ2 : Prop) (P1 P2 : iProp Σ) :
    (φ1 ↔ φ2) → (φ1 → φ2 → P1 ⊣⊢ P2) → (⌜φ1⌝ ∗ P1) ⊣⊢ (⌜φ2⌝ ∗ P2).
  Proof. intros -> HP. iSplit; iDestruct 1 as (Hϕ) "H"; rewrite HP; auto. Qed.
(*
  Lemma iLType_interp_nil p : ⊢ iLType_interp [] [] p (iLType_dual p).
  Proof. iExists p; simpl. iSplitL; iApply iLType_le_refl. Qed.

  Lemma iLType_interp_flip vsl vsr pl pr :
    iLType_interp vsl vsr pl pr -∗ iLType_interp vsr vsl pr pl.
  Proof.
    iDestruct 1 as (p) "[Hp Hdp]". iExists (iLType_dual p).
    rewrite (involutive iLType_dual). iFrame.
  Qed.

  Lemma iLType_interp_le_l vsl vsr pl pl' pr :
    iLType_interp vsl vsr pl pr -∗ pl ⊑ pl' -∗ iLType_interp vsl vsr pl' pr.
  Proof.
    iDestruct 1 as (p) "[Hp Hdp]". iIntros "Hle". iExists p.
    iFrame "Hdp". by iApply (iLType_le_trans with "Hp").
  Qed.
  Lemma iLType_interp_le_r vsl vsr pl pr pr' :
    iLType_interp vsl vsr pl pr -∗ pr ⊑ pr' -∗ iLType_interp vsl vsr pl pr'.
  Proof.
    iIntros "H Hle". iApply iLType_interp_flip.
    iApply (iLType_interp_le_l with "[H] Hle"). by iApply iLType_interp_flip.
  Qed.
 *)

  Lemma iLType_interp_send source dest vs v lenv ml lty :
    ⌜ lenv !! source = Some (<! dest> ml) ⌝ -∗
    iLType_interp vs lenv -∗
    iLMsg_car ml v (Next lty) -∗
    iLType_interp (<[dest := ((vs !!! dest) ++ [(source, v)])]> vs) (<[source:=lty]> lenv).
(*    ▷^(length vsr) iLType_interp (vsl ++ [vl]) vsr pl' pr.*)
  Proof.
    iIntros "%Heq [%Heq' [%lenv' [%Heq'' [Hwf Henv]]]] Hcar". unfold ltype_env in lenv.
    iInduction lenv as [|k v' lenv''] "IH" using map_ind.
    + rewrite lookup_empty in Heq; simplify_eq.
    + apply (lookup_insert_Some lenv'') in Heq as [[Hk Hv']|H1]; subst.
    - iClear "IH"; rewrite insert_insert.
      rewrite big_sepM_insert; [|apply H].
      iDestruct "Henv" as "[[%v' [%lty' [[%Heq1 %Heq2] Hvs']]] Henv]".
      unfold iLType_interp.
      Check big_sepM_insert _ lenv'' source (<! dest> ml) H.
      iRewrite (big_sepM_insert $! _ lenv'' source (<! dest> ml) H) in "Henv".
     Search insert big_opM bi_sep.
        unfold iLType_interp.
      Search insert.

      destruct (nat_eq_dec k source); subst.
      Check lookup_insert_Some.
      Search lookup Some.
      Search big_opM.
      unfold iLType_interp.
      Set Printing All.
      Search insert lookup gmap.
      
      unfold iLType_interp at 3.
      Search map_fold.
    admit.
    Check map_fold_insert.

    iIntros "%Henv [%Heq [%lenv' Hlenv]] Hcar".
    iPoseProof (@map_fold_ind nat (gmap nat) _ _ _ _ _ _ _ _ _ (iLType Σ V) (iProp Σ) _ ((λ (k : nat) lty0 (acc : iPropI Σ),
                 ∃ (bs : list (nat * V)) lty',
                   ⌜vs !! k ≡ Some bs ∧ lenv' !! k ≡ Some lty'⌝ ∗
                                              iLType_app_recvs bs lty' ⊑ lty0 ∗ acc)%I) ((⌜map fst (map_to_list vs) ≡ map fst (map_to_list lenv')⌝ ∗
             iLType_wf lenv')%I)) as "Hpat".
    apply  ((λ (k : nat) lty0 (acc : iPropI Σ),
                 ∃ (bs : list (nat * V)) lty',
                   ⌜vs !! k ≡ Some bs ∧ lenv' !! k ≡ Some lty'⌝ ∗
                                              iLType_app_recvs bs lty' ⊑ lty0 ∗ acc)%I).
    apply ((⌜map fst (map_to_list vs) ≡ map fst (map_to_list lenv')⌝ ∗
             iLType_wf lenv')%I).
    Focus 2. intros.
    apply map_fold_ind with (B := iProp Σ).
    Check @map_fold_ind.
    Check map_fold_ind.
    induction lenv using (@map_fold_ind nat (gmap nat) _ _ _ _ _ _ _ _ _ (iLType Σ V) (iProp Σ) _ ((λ (k : nat) lty0 (acc : iPropI Σ),
                 ∃ (bs : list (nat * V)) lty',
                   ⌜vs !! k ≡ Some bs ∧ lenv' !! k ≡ Some lty'⌝ ∗
                   iLType_app_recvs bs lty' ⊑ lty0 ∗ acc)%I)).
    induction lenv using map_fold_ind.
    induction lenv using (@map_fold_ind nat (gmap nat) _ _ _ _ _ _ _ _ _ (iLType Σ V) (iProp Σ)).
    iInduction lenv as [| a b c d] "IH" using (@map_fold_ind nat (gmap nat) _ _ _ _ _ _ _ _ _ (iLType Σ V) (iProp Σ)).
    iInduction lenv as [| k x1 levn r] "IH" using map_fold_ind.
    iInduction lenv as [| k x1 lenv] "IH" using map_ind; simpl.
    + rewrite lookup_empty in Henv; simplify_eq.
    + destruct (nat_eq_dec k source); subst.
      - iClear "IH".
        iDestruct "Hlenv" as (Heq lenv') "Hlenv".
        Search map_fold insert.
        Check @map_fold_insert.
        
        iPoseProof (@map_fold_insert nat (gmap nat) _ _ _ _ _ _ _ _ _ (iLType Σ V) (iProp Σ) bi_entails _
                                     ((λ (k : nat) lty0 (acc : iPropI Σ),
                 ∃ (bs : list (nat * V)) lty',
                   ⌜vs !! k ≡ Some bs ∧ lenv' !! k ≡ Some lty'⌝ ∗
                   iLType_app_recvs bs lty' ⊑ lty0 ∗ acc)%I)
                                     ((⌜map fst (map_to_list vs) ≡ map fst (map_to_list lenv')⌝ ∗
               iLType_wf lenv')%I) Source x1 lenv) as "Hpat"; [| | apply H| ].
        Focus 3.
        iSpecialize ("Hpat" with "Hlenv").
        iDestruct "Hpat" as (vs' lty' [Heq1 Heq2]) "[Happ Hmap]".
        Search map_fold.
        unfold iLType_interp.
        iSplitR.
        simpl.
        Set Printing All.
        iRewrite "ipat" in "Hlenv".
        Check (@map_fold_insert nat _ _ _ _ _ _ _ _ _ _ _ _ bi_entails).
        iRewrite (@map_fold_insert $! nat _ _ _ _ _ _ _ _ _ _ _ bi_entails) in "Hlenv".
        iRewrite map_fold_insert (R := bi_wand) in "Hlenv" with .
        simpl.
      Search gmap_lookup insert Some.
      apply lookup_fmap_Some in H.
    Search lookup.
    Check lookup_empty.
    Check map_ind.
    
    simpl.
    iDestruct 1 as (p) "[Hp Hdp] /="; iIntros "Hml".
    iDestruct (iLType_le_trans _ _ (<!> MSG vl; pl') with "Hp [Hml]") as "Hp".
    { iApply iLType_le_send. rewrite iMsg_base_eq. iIntros (v' p') "(->&Hp&_) /=".
      iExists p'. iSplitR; [iApply iLType_le_refl|]. by iRewrite -"Hp". }
    iInduction vsr as [|vr vsr] "IH" forall (pl'); simpl.
    { iExists pl'; simpl. iSplitR; [iApply iLType_le_refl|].
      iApply (iLType_le_trans with "[Hp] Hdp").
      iInduction vsl as [|vl' vsl] "IH"; simpl.
      { iApply iLType_le_dual_r. rewrite iLType_dual_message iMsg_dual_base /=.
        by rewrite involutive. }
      iApply iLType_le_base; iIntros "!>". by iApply "IH". }
    iDestruct (iLType_le_recv_send_inv _ _ vr vl
      (iLType_app_recvs vsr p) pl' with "Hp [] []") as (p') "[H1 H2]";
      [rewrite iMsg_base_eq; by auto..|].
    iIntros "!>". iSpecialize ("IH" with "Hdp H1"). iIntros "!>".
    iDestruct "IH" as (p'') "[Hp'' Hdp'']". iExists p''. iFrame "Hdp''".
    iApply (iLType_le_trans with "[Hp''] H2"); simpl. by iApply iLType_le_base.
  Qed.

  Lemma iLType_interp_recv vl vsl vsr pl mr :
    iLType_interp (vl :: vsl) vsr pl (<?> mr) -∗
    ∃ pr, iMsg_car mr vl (Next pr) ∗ ▷ iLType_interp vsl vsr pl pr.
  Proof.
    iDestruct 1 as (p) "[Hp Hdp] /=".
    iDestruct (iLType_le_recv_inv with "Hdp") as (m) "[#Hm Hpr]".
    iDestruct (iLType_message_equivI with "Hm") as (_) "{Hm} #Hm".
    iDestruct ("Hpr" $! vl (iLType_app_recvs vsl (iLType_dual p)) with "[]")
      as (pr'') "[Hler Hpr]".
    { iRewrite -("Hm" $! vl (Next (iLType_app_recvs vsl (iLType_dual p)))).
      rewrite iMsg_base_eq; auto. }
    iExists pr''. iIntros "{$Hpr} !>". iExists p. iFrame.
  Qed.

  Global Instance iLType_own_ne γ s : NonExpansive (iLType_own γ s).
  Proof. solve_proper. Qed.
  Global Instance iLType_own_proper γ s : Proper ((≡) ==> (≡)) (iLType_own γ s).
  Proof. apply (ne_proper _). Qed.

  Lemma iLType_own_le γ s p1 p2 :
    iLType_own γ s p1 -∗ ▷ (p1 ⊑ p2) -∗ iLType_own γ s p2.
  Proof.
    iDestruct 1 as (p1') "[Hle H]". iIntros "Hle'".
    iExists p1'. iFrame "H". by iApply (iLType_le_trans with "Hle").
  Qed.

  Lemma iLType_init p :
    ⊢ |==> ∃ γ,
      iLType_ctx γ [] [] ∗
      iLType_own γ Left p ∗ iLType_own γ Right (iLType_dual p).
  Proof.
    iMod (own_alloc (●E (Next p) ⋅ ◯E (Next p))) as (lγ) "[H●l H◯l]".
    { by apply excl_auth_valid. }
    iMod (own_alloc (●E (Next (iLType_dual p)) ⋅
      ◯E (Next (iLType_dual p)))) as (rγ) "[H●r H◯r]".
    { by apply excl_auth_valid. }
    pose (ProtName lγ rγ) as γ. iModIntro. iExists γ. iSplitL "H●l H●r".
    { iExists p, (iLType_dual p). iFrame. iApply iLType_interp_nil. }
    iSplitL "H◯l"; iExists _; iFrame; iApply iLType_le_refl.
  Qed.

  Lemma iLType_send_l γ m vsr vsl vl p :
    iLType_ctx γ vsl vsr -∗
    iLType_own γ Left (<!> m) -∗
    iMsg_car m vl (Next p) ==∗
      ▷^(length vsr) iLType_ctx γ (vsl ++ [vl]) vsr ∗
      iLType_own γ Left p.
  Proof.
    iDestruct 1 as (pl pr) "(H●l & H●r & Hinterp)".
    iDestruct 1 as (pl') "[Hle H◯]". iIntros "Hm".
    iDestruct (iLType_own_auth_agree with "H●l H◯") as "#Hp".
    iAssert (▷ (pl ⊑ <!> m))%I
      with "[Hle]" as "{Hp} Hle"; first (iNext; by iRewrite "Hp").
    iDestruct (iLType_interp_le_l with "Hinterp Hle") as "Hinterp".
    iDestruct (iLType_interp_send with "Hinterp [Hm //]") as "Hinterp".
    iMod (iLType_own_auth_update _ _ _ _ p with "H●l H◯") as "[H●l H◯]".
    iIntros "!>". iSplitR "H◯".
    - iIntros "!>". iExists p, pr. iFrame.
    - iExists p. iFrame. iApply iLType_le_refl.
  Qed.

  Lemma iLType_send_r γ m vsr vsl vr p :
    iLType_ctx γ vsl vsr -∗
    iLType_own γ Right (<!> m) -∗
    iMsg_car m vr (Next p) ==∗
      ▷^(length vsl) iLType_ctx γ vsl (vsr ++ [vr]) ∗
      iLType_own γ Right p.
  Proof.
    iDestruct 1 as (pl pr) "(H●l & H●r & Hinterp)".
    iDestruct 1 as (pr') "[Hle H◯]". iIntros "Hm".
    iDestruct (iLType_own_auth_agree with "H●r H◯") as "#Hp".
    iAssert (▷ (pr ⊑ <!> m))%I
      with "[Hle]" as "{Hp} Hle"; first (iNext; by iRewrite "Hp").
    iDestruct (iLType_interp_flip with "Hinterp") as "Hinterp".
    iDestruct (iLType_interp_le_l with "Hinterp Hle") as "Hinterp".
    iDestruct (iLType_interp_send with "Hinterp [Hm //]") as "Hinterp".
    iMod (iLType_own_auth_update _ _ _ _ p with "H●r H◯") as "[H●r H◯]".
    iIntros "!>". iSplitR "H◯".
    - iIntros "!>". iExists pl, p. iFrame. by iApply iLType_interp_flip.
    - iExists p. iFrame. iApply iLType_le_refl.
  Qed.

  Lemma iLType_recv_l γ m vr vsr vsl :
    iLType_ctx γ vsl (vr :: vsr) -∗
    iLType_own γ Left (<?> m) ==∗
    ▷ ∃ p,
      iLType_ctx γ vsl vsr ∗
      iLType_own γ Left p ∗
      iMsg_car m vr (Next p).
  Proof.
    iDestruct 1 as (pl pr) "(H●l & H●r & Hinterp)".
    iDestruct 1 as (p) "[Hle H◯]".
    iDestruct (iLType_own_auth_agree with "H●l H◯") as "#Hp".
    iDestruct (iLType_interp_le_l with "Hinterp [Hle]") as "Hinterp".
    { iIntros "!>". by iRewrite "Hp". }
    iDestruct (iLType_interp_flip with "Hinterp") as "Hinterp".
    iDestruct (iLType_interp_recv with "Hinterp") as (q) "[Hm Hinterp]".
    iMod (iLType_own_auth_update _ _ _ _ q with "H●l H◯") as "[H●l H◯]".
    iIntros "!> !> /=". iExists q. iFrame "Hm". iSplitR "H◯".
    - iExists q, pr. iFrame. by iApply iLType_interp_flip.
    - iExists q. iIntros "{$H◯} !>". iApply iLType_le_refl.
  Qed.

  Lemma iLType_recv_r γ m vl vsr vsl :
    iLType_ctx γ (vl :: vsl) vsr -∗
    iLType_own γ Right (<?> m) ==∗
    ▷ ∃ p,
      iLType_ctx γ vsl vsr ∗
      iLType_own γ Right p ∗
      iMsg_car m vl (Next p).
  Proof.
    iDestruct 1 as (pl pr) "(H●l & H●r & Hinterp)".
    iDestruct 1 as (p) "[Hle H◯]".
    iDestruct (iLType_own_auth_agree with "H●r H◯") as "#Hp".
    iDestruct (iLType_interp_le_r with "Hinterp [Hle]") as "Hinterp".
    { iIntros "!>". by iRewrite "Hp". }
    iDestruct (iLType_interp_recv with "Hinterp") as (q) "[Hm Hinterp]".
    iMod (iLType_own_auth_update _ _ _ _ q with "H●r H◯") as "[H●r H◯]".
    iIntros "!> !> /=". iExists q. iFrame "Hm". iSplitR "H◯".
    - iExists pl, q. iFrame.
    - iExists q. iIntros "{$H◯} !>". iApply iLType_le_refl.
  Qed.

  (** The instances below make it possible to use the tactics [iIntros],
  [iExist], [iSplitL]/[iSplitR], [iFrame] and [iModIntro] on [iLType_le] goals. *)
  Global Instance iLType_le_from_forall_l {A} a (m1 : A → iMsg Σ V) m2 name :
    AsIdentName m1 name →
    FromForall (iLType_message Recv (iMsg_exist m1) ⊑ (<a> m2))
               (λ x, (<?> m1 x) ⊑ (<a> m2))%I name | 10.
  Proof. intros _. apply iLType_le_exist_elim_l. Qed.
  Global Instance iLType_le_from_forall_r {A} a m1 (m2 : A → iMsg Σ V) name :
    AsIdentName m2 name →
    FromForall ((<a> m1) ⊑ iLType_message Send (iMsg_exist m2))
               (λ x, (<a> m1) ⊑ (<!> m2 x))%I name | 11.
  Proof. intros _. apply iLType_le_exist_elim_r. Qed.

  Global Instance iLType_le_from_wand_l a m v P p :
    TCIf (TCEq P True%I) False TCTrue →
    FromWand ((<?> MSG v {{ P }}; p) ⊑ (<a> m)) P ((<?> MSG v; p) ⊑ (<a> m)) | 10.
  Proof. intros _. apply iLType_le_payload_elim_l. Qed.
  Global Instance iLType_le_from_wand_r a m v P p :
    FromWand ((<a> m) ⊑ (<!> MSG v {{ P }}; p)) P ((<a> m) ⊑ (<!> MSG v; p)) | 11.
  Proof. apply iLType_le_payload_elim_r. Qed.

  Global Instance iLType_le_from_exist_l {A} (m : A → iMsg Σ V) p :
    FromExist ((<! x> m x) ⊑ p) (λ a, (<!> m a) ⊑ p)%I | 10.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (iLType_le_trans with "[] H"). iApply iLType_le_exist_intro_l.
  Qed.
  Global Instance iLType_le_from_exist_r {A} (m : A → iMsg Σ V) p :
    FromExist (p ⊑ <? x> m x) (λ a, p ⊑ (<?> m a))%I | 11.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (iLType_le_trans with "H"). iApply iLType_le_exist_intro_r.
  Qed.

  Global Instance iLType_le_from_sep_l m v P p :
    FromSep ((<!> MSG v {{ P }}; p) ⊑ (<!> m)) P ((<!> MSG v; p) ⊑ (<!> m)) | 10.
  Proof.
    rewrite /FromSep. iIntros "[HP H]".
    iApply (iLType_le_trans with "[HP] H"). by iApply iLType_le_payload_intro_l.
  Qed.
  Global Instance iLType_le_from_sep_r m v P p :
    FromSep ((<?> m) ⊑ (<?> MSG v {{ P }}; p)) P ((<?> m) ⊑ (<?> MSG v; p)) | 11.
  Proof.
    rewrite /FromSep. iIntros "[HP H]".
    iApply (iLType_le_trans with "H"). by iApply iLType_le_payload_intro_r.
  Qed.

  Global Instance iLType_le_frame_l q m v R P Q p :
    Frame q R P Q →
    Frame q R ((<!> MSG v {{ P }}; p) ⊑ (<!> m))
              ((<!> MSG v {{ Q }}; p) ⊑ (<!> m)) | 10.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (iLType_le_trans with "[HR] H"). iApply iLType_le_payload_elim_r.
    iIntros "HQ". iApply iLType_le_payload_intro_l. iApply HP; iFrame.
  Qed.
  Global Instance iLType_le_frame_r q m v R P Q p :
    Frame q R P Q →
    Frame q R ((<?> m) ⊑ (<?> MSG v {{ P }}; p))
              ((<?> m) ⊑ (<?> MSG v {{ Q }}; p)) | 11.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (iLType_le_trans with "H"). iApply iLType_le_payload_elim_l.
    iIntros "HQ". iApply iLType_le_payload_intro_r. iApply HP; iFrame.
  Qed.

  Global Instance iLType_le_from_modal a v p1 p2 :
    FromModal (modality_instances.modality_laterN 1) (p1 ⊑ p2)
              ((<a> MSG v; p1) ⊑ (<a> MSG v; p2)) (p1 ⊑ p2).
  Proof. apply iLType_le_base. Qed.

End proto.

Typeclasses Opaque iLType_ctx iLType_own.

Hint Extern 0 (environments.envs_entails _ (?x ⊑ ?y)) =>
  first [is_evar x; fail 1 | is_evar y; fail 1|iApply iLType_le_refl] : core.


End ltype.
