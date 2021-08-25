(** This file defines the model of dependent separation protocols as the
solution of a recursive domain equation, along with various primitive
operations, such as append and map.

Important: This file should not be used directly, but rather the wrappers in
[proto] should be used.

Dependent Separation Protocols are modeled as the solution of the following
recursive domain equation:

[proto = 1 + (action * (V → ▶ proto → PROP))]

Here, the left-hand side of the sum is used for the terminated process, while
the right-hand side is used for the communication constructors. The type
[action] is an inductively defined datatype with two constructors [Send] and
[Recv]. Compared to having an additional sum in [proto], this makes it
possible to factorize the code in a better way.

The remainder [V → ▶ proto → PROP] is a predicate that ranges over the
communicated value [V] and the tail protocol [proto]. Note that to solve this
recursive domain equation using Iris's COFE solver, the recursive occurrence
of [proto] appear under the later [▶].

On top of the type [proto], we define the constructors:

- [proto_end], which constructs the left-side of the sum.
- [proto_msg], which takes an action and a predicate and constructs the
  right-hand side of the sum accordingly.

The defined functions on the type [proto] are:

- [proto_map], which can be used to map the actions and the propositions of
  a given protocol.
- [proto_app], which appends two protocols [p1] and [p2], by substituting
  all terminations [END] in [p1] with [p2]. *)
From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From actris.utils Require Import cofe_solver_2.
Set Default Proof Using "Type".

Module Export action.
  Inductive action := Send of nat | Recv of nat.
  Instance action_inhabited : Inhabited action := populate (Send 0).
  Canonical Structure actionO := leibnizO action.
End action.

Definition ltype_auxO (V : Type) (PROP : ofe) (A : ofe) : ofe :=
  optionO (prodO actionO (V -d> laterO A -n> PROP)).
Definition ltype_auxOF (V : Type) (PROP : ofe) : oFunctor :=
  optionOF (actionO * (V -d> ▶ ∙ -n> PROP)).

Definition ltype_result (V : Type) := result_2 (ltype_auxOF V).
Definition ltype (V : Type) (PROPn PROP : ofe) `{!Cofe PROPn, !Cofe PROP} : ofe :=
  solution_2_car (ltype_result V) PROPn _ PROP _.
Instance ltype_cofe {V} `{!Cofe PROPn, !Cofe PROP} : Cofe (ltype V PROPn PROP).
Proof. apply _. Qed.
Lemma ltype_iso {V} `{!Cofe PROPn, !Cofe PROP} :
  ofe_iso (ltype_auxO V PROP (ltype V PROP PROPn)) (ltype V PROPn PROP).
Proof. apply ltype_result. Qed.

Definition ltype_fold {V} `{!Cofe PROPn, !Cofe PROP} :
  ltype_auxO V PROP (ltype V PROP PROPn) -n> ltype V PROPn PROP := ofe_iso_1 ltype_iso.
Definition ltype_unfold {V} `{!Cofe PROPn, !Cofe PROP} :
  ltype V PROPn PROP -n> ltype_auxO V PROP (ltype V PROP PROPn) := ofe_iso_2 ltype_iso.
Lemma ltype_fold_unfold {V} `{!Cofe PROPn, !Cofe PROP} (p : ltype V PROPn PROP) :
  ltype_fold (ltype_unfold p) ≡ p.
Proof. apply (ofe_iso_12 ltype_iso). Qed.
Lemma ltype_unfold_fold {V} `{!Cofe PROPn, !Cofe PROP}
    (p : ltype_auxO V PROP (ltype V PROP PROPn)) :
  ltype_unfold (ltype_fold p) ≡ p.
Proof. apply (ofe_iso_21 ltype_iso). Qed.

Definition ltype_end {V} `{!Cofe PROPn, !Cofe PROP} : ltype V PROPn PROP :=
  ltype_fold None.
Definition ltype_message {V} `{!Cofe PROPn, !Cofe PROP} (a : action)
    (m : V → laterO (ltype V PROP PROPn) -n> PROP) : ltype V PROPn PROP :=
  ltype_fold (Some (a, m)).

Instance ltype_message_ne {V} `{!Cofe PROPn, !Cofe PROP} a n :
  Proper (pointwise_relation V (dist n) ==> dist n)
         (ltype_message (PROPn:=PROPn) (PROP:=PROP) a).
Proof. intros c1 c2 Hc. rewrite /ltype_message. f_equiv. by repeat constructor. Qed.
Instance ltype_message_proper {V} `{!Cofe PROPn, !Cofe PROP} a :
  Proper (pointwise_relation V (≡) ==> (≡))
         (ltype_message (PROPn:=PROPn) (PROP:=PROP) a).
Proof. intros c1 c2 Hc. rewrite /ltype_message. f_equiv. by repeat constructor. Qed.

Lemma ltype_case {V} `{!Cofe PROPn, !Cofe PROP} (p : ltype V PROPn PROP) :
  p ≡ ltype_end ∨ ∃ a m, p ≡ ltype_message a m.
Proof.
  destruct (ltype_unfold p) as [[a m]|] eqn:E; simpl in *; last first.
  - left. by rewrite -(ltype_fold_unfold p) E.
  - right. exists a, m. by rewrite /ltype_message -E ltype_fold_unfold.
Qed.
Instance ltype_inhabited {V} `{!Cofe PROPn, !Cofe PROP} :
  Inhabited (ltype V PROPn PROP) := populate ltype_end.

Lemma ltype_message_equivI `{!BiInternalEq SPROP} {V} `{!Cofe PROPn, !Cofe PROP} a1 a2 m1 m2 :
  ltype_message (V:=V) (PROPn:=PROPn) (PROP:=PROP) a1 m1 ≡ ltype_message a2 m2
  ⊣⊢@{SPROP} ⌜ a1 = a2 ⌝ ∧ (∀ v p', m1 v p' ≡ m2 v p').
Proof.
  trans (ltype_unfold (ltype_message a1 m1) ≡ ltype_unfold (ltype_message a2 m2) : SPROP)%I.
  { iSplit.
    - iIntros "Heq". by iRewrite "Heq".
    - iIntros "Heq". rewrite -{2}(ltype_fold_unfold (ltype_message _ _)).
      iRewrite "Heq". by rewrite ltype_fold_unfold. }
  rewrite /ltype_message !ltype_unfold_fold option_equivI prod_equivI /=.
  rewrite discrete_eq discrete_fun_equivI.
  by setoid_rewrite ofe_morO_equivI.
Qed.
Lemma ltype_message_end_equivI `{!BiInternalEq SPROP} {V} `{!Cofe PROPn, !Cofe PROP} a m :
  ltype_message (V:=V) (PROPn:=PROPn) (PROP:=PROP) a m ≡ ltype_end ⊢@{SPROP} False.
Proof.
  trans (ltype_unfold (ltype_message a m) ≡ ltype_unfold ltype_end : SPROP)%I.
  { iIntros "Heq". by iRewrite "Heq". }
  by rewrite /ltype_message !ltype_unfold_fold option_equivI.
Qed.
Lemma ltype_end_message_equivI `{!BiInternalEq SPROP} {V} `{!Cofe PROPn, !Cofe PROP} a m :
  ltype_end ≡ ltype_message (V:=V) (PROPn:=PROPn) (PROP:=PROP) a m ⊢@{SPROP} False.
Proof. by rewrite internal_eq_sym ltype_message_end_equivI. Qed.

(** The eliminator [ltype_elim x f p] is only well-behaved if the function [f]
is contractive *)
Definition ltype_elim {V} `{!Cofe PROPn, !Cofe PROP} {A}
    (x : A) (f : action → (V → laterO (ltype V PROP PROPn) -n> PROP) → A)
    (p : ltype V PROPn PROP) : A :=
  match ltype_unfold p with None => x | Some (a, m) => f a m end.

Lemma ltype_elim_ne {V} `{!Cofe PROPn, !Cofe PROP} {A : ofe}
    (x : A) (f1 f2 : action → (V → laterO (ltype V PROP PROPn) -n> PROP) → A) p1 p2 n :
  (∀ a m1 m2, (∀ v, m1 v ≡{n}≡ m2 v) → f1 a m1 ≡{n}≡ f2 a m2) →
  p1 ≡{n}≡ p2 →
  ltype_elim x f1 p1 ≡{n}≡ ltype_elim x f2 p2.
Proof.
  intros Hf Hp. rewrite /ltype_elim.
  apply (_ : NonExpansive ltype_unfold) in Hp
    as [[a1 m1] [a2 m2] [-> ?]|]; simplify_eq/=; [|done].
  apply Hf. destruct n; by simpl.
Qed.

Lemma ltype_elim_end {V} `{!Cofe PROPn, !Cofe PROP} {A : ofe}
    (x : A) (f : action → (V → laterO (ltype V PROP PROPn) -n> PROP) → A) :
  ltype_elim x f ltype_end ≡ x.
Proof.
  rewrite /ltype_elim /ltype_end.
  pose proof (ltype_unfold_fold (V:=V) (PROPn:=PROPn) (PROP:=PROP) None) as Hfold.
  by destruct (ltype_unfold (ltype_fold None)) as [[??]|] eqn:E; inversion Hfold.
Qed.
Lemma ltype_elim_message {V} `{!Cofe PROPn, !Cofe PROP} {A : ofe}
    (x : A) (f : action → (V → laterO (ltype V PROP PROPn) -n> PROP) → A)
    `{Hf : ∀ a, Proper (pointwise_relation _ (≡) ==> (≡)) (f a)} a m :
  ltype_elim x f (ltype_message a m) ≡ f a m.
Proof.
  rewrite /ltype_elim /ltype_message /=.
  pose proof (ltype_unfold_fold (V:=V) (PROPn:=PROPn)
    (PROP:=PROP) (Some (a, m))) as Hfold.
  destruct (ltype_unfold (ltype_fold (Some (a, m))))
    as [[??]|] eqn:E; inversion Hfold as [?? [Ha Hc]|]; simplify_eq/=.
  by f_equiv=> v.
Qed.

(** Functor *)
Program Definition ltype_map_aux {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (g : PROP -n> PROP') (rec : ltype V PROP' PROPn' -n> ltype V PROP PROPn) :
    ltype V PROPn PROP -n> ltype V PROPn' PROP' := λne p,
  ltype_elim ltype_end (λ a m, ltype_message a (λ v, g ◎ m v ◎ laterO_map rec)) p.
Next Obligation.
  intros V PROPn ? PROPn' ? PROP ? PROP' ? g rec n p1 p2 Hp.
  apply ltype_elim_ne=> // a m1 m2 Hm. by repeat f_equiv.
Qed.

Instance ltype_map_aux_contractive {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'} (g : PROP -n> PROP') :
  Contractive (ltype_map_aux (V:=V) (PROPn:=PROPn) (PROPn':=PROPn') g).
Proof.
  intros n rec1 rec2 Hrec p. simpl. apply ltype_elim_ne=> // a m1 m2 Hm.
  f_equiv=> v p' /=. do 2 f_equiv; [done|].
  apply Next_contractive; destruct n as [|n]=> //=.
Qed.

Definition ltype_map_aux_2 {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP')
    (rec : ltype V PROPn PROP -n> ltype V PROPn' PROP') :
    ltype V PROPn PROP -n> ltype V PROPn' PROP' :=
  ltype_map_aux g (ltype_map_aux gn rec).
Instance ltype_map_aux_2_contractive {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
  Contractive (ltype_map_aux_2 (V:=V) gn g).
Proof.
  intros n rec1 rec2 Hrec. rewrite /ltype_map_aux_2.
  f_equiv. by apply ltype_map_aux_contractive.
Qed.
Definition ltype_map {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
    ltype V PROPn PROP -n> ltype V PROPn' PROP' :=
  fixpoint (ltype_map_aux_2 gn g).

Lemma ltype_map_unfold {V}
    `{Hcn:!Cofe PROPn, Hcn':!Cofe PROPn', Hc:!Cofe PROP, Hc':!Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') p :
  ltype_map (V:=V) gn g p ≡ ltype_map_aux g (ltype_map g gn) p.
Proof.
  apply equiv_dist=> n. revert PROPn Hcn PROPn' Hcn' PROP Hc PROP' Hc' gn g p.
  induction (lt_wf n) as [n _ IH]=>
    PROPn Hcn PROPn' Hcn' PROP Hc PROP' Hc' gn g p.
  etrans; [apply equiv_dist, (fixpoint_unfold (ltype_map_aux_2 gn g))|].
  apply ltype_map_aux_contractive; destruct n as [|n]; [done|]; simpl.
  symmetry. apply: IH. lia.
Qed.
Lemma ltype_map_end {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
  ltype_map (V:=V) gn g ltype_end ≡ ltype_end.
Proof. by rewrite ltype_map_unfold /ltype_map_aux /= ltype_elim_end. Qed.
Lemma ltype_map_message {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') a m :
  ltype_map (V:=V) gn g (ltype_message a m)
  ≡ ltype_message a (λ v, g ◎ m v ◎ laterO_map (ltype_map g gn)).
Proof.
  rewrite ltype_map_unfold /ltype_map_aux /=.
  apply: ltype_elim_message=> a' m1 m2 Hm; f_equiv; solve_proper.
Qed.

Lemma ltype_map_ne {V}
    `{Hcn:!Cofe PROPn, Hcn':!Cofe PROPn', Hc:!Cofe PROP, Hc':!Cofe PROP'}
    (gn1 gn2 : PROPn' -n> PROPn) (g1 g2 : PROP -n> PROP') p n :
  gn1 ≡{n}≡ gn2 → g1 ≡{n}≡ g2 →
  ltype_map (V:=V) gn1 g1 p ≡{n}≡ ltype_map (V:=V) gn2 g2 p.
Proof.
  revert PROPn Hcn PROPn' Hcn' PROP Hc PROP' Hc' gn1 gn2 g1 g2 p.
  induction (lt_wf n) as [n _ IH]=>
    PROPn ? PROPn' ? PROP ? PROP' ? gn1 gn2 g1 g2 p Hgn Hg /=.
  destruct (ltype_case p) as [->|(a & m & ->)]; [by rewrite !ltype_map_end|].
  rewrite !ltype_map_message /=.
  apply ltype_message_ne=> // v p' /=. f_equiv; [done|]. f_equiv.
  apply Next_contractive; destruct n as [|n]=> //=; auto using dist_S with lia.
Qed.
Lemma ltype_map_ext {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn1 gn2 : PROPn' -n> PROPn) (g1 g2 : PROP -n> PROP') p :
  gn1 ≡ gn2 → g1 ≡ g2 → ltype_map (V:=V) gn1 g1 p ≡ ltype_map (V:=V) gn2 g2 p.
Proof.
  intros Hgn Hg. apply equiv_dist=> n.
  apply ltype_map_ne=> // ?; by apply equiv_dist.
Qed.
Lemma ltype_map_id {V} `{Hcn:!Cofe PROPn, Hc:!Cofe PROP} (p : ltype V PROPn PROP) :
  ltype_map cid cid p ≡ p.
Proof.
  apply equiv_dist=> n. revert PROPn Hcn PROP Hc p.
  induction (lt_wf n) as [n _ IH]=> PROPn ? PROP ? p /=.
  destruct (ltype_case p) as [->|(a & m & ->)]; [by rewrite !ltype_map_end|].
  rewrite !ltype_map_message /=. apply ltype_message_ne=> // v p' /=. f_equiv.
  apply Next_contractive; destruct n as [|n]=> //=; auto.
Qed.
Lemma ltype_map_compose {V}
   `{Hcn:!Cofe PROPn, Hcn':!Cofe PROPn', Hcn'':!Cofe PROPn'',
     Hc:!Cofe PROP, Hc':!Cofe PROP', Hc'':!Cofe PROP''}
    (gn1 : PROPn'' -n> PROPn') (gn2 : PROPn' -n> PROPn)
    (g1 : PROP -n> PROP') (g2 : PROP' -n> PROP'') (p : ltype V PROPn PROP) :
  ltype_map (gn2 ◎ gn1) (g2 ◎ g1) p ≡ ltype_map gn1 g2 (ltype_map gn2 g1 p).
Proof.
  apply equiv_dist=> n. revert PROPn Hcn PROPn' Hcn' PROPn'' Hcn''
    PROP Hc PROP' Hc' PROP'' Hc'' gn1 gn2 g1 g2 p.
  induction (lt_wf n) as [n _ IH]=> PROPn ? PROPn' ? PROPn'' ?
    PROP ? PROP' ? PROP'' ? gn1 gn2 g1 g2 p /=.
  destruct (ltype_case p) as [->|(a & c & ->)]; [by rewrite !ltype_map_end|].
  rewrite !ltype_map_message /=. apply ltype_message_ne=> // v p' /=.
  do 3 f_equiv. apply Next_contractive; destruct n as [|n]=> //=; auto.
Qed.

Program Definition ltypeOF (V : Type) (Fn F : oFunctor)
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car Fn A B)}
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F A B)} : oFunctor := {|
  oFunctor_car A _ B _ := ltype V (oFunctor_car Fn B A) (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    ltype_map (oFunctor_map Fn (fg.2, fg.1)) (oFunctor_map F fg)
|}.
Next Obligation.
  intros V Fn F ?? A1 ? A2 ? B1 ? B2 ? n f g [??] p; simpl in *.
  apply ltype_map_ne=> // y; by apply oFunctor_map_ne.
Qed.
Next Obligation.
  intros V Fn F ?? A ? B ? p; simpl in *. rewrite /= -{2}(ltype_map_id p).
  apply ltype_map_ext=> //= y; by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros V Fn F ?? A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' p; simpl in *.
  rewrite -ltype_map_compose.
  apply ltype_map_ext=> //= y; by rewrite ofe.oFunctor_map_compose.
Qed.

Instance ltypeOF_contractive (V : Type) (Fn F : oFunctor)
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car Fn A B)}
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F A B)} :
  oFunctorContractive Fn → oFunctorContractive F → 
  oFunctorContractive (ltypeOF V Fn F).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n f g Hfg p; simpl in *.
  apply ltype_map_ne=> //= y;
    [destruct n; [|destruct Hfg]; by apply oFunctor_map_contractive..].
Qed.
