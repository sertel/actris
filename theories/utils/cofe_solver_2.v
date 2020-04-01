From iris.algebra Require Import cofe_solver.

(** Composition of [oFunctor]. Move to Iris. Fix name [oFunctor_compose] which
is already in use. *)
Program Definition oFunctor_compose (F1 F2 : oFunctor)
  `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} : oFunctor := {|
  oFunctor_car A _ B _ := oFunctor_car F1 (oFunctor_car F2 B A) (oFunctor_car F2 A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ 'fg :=
    oFunctor_map F1 (oFunctor_map F2 (fg.2,fg.1),oFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] [??]; simpl in *.
  apply oFunctor_ne; split; apply oFunctor_ne; by split.
Qed.
Next Obligation.
  intros F1 F2 ? A ? B ? x; simpl in *. rewrite -{2}(oFunctor_id F1 x).
  apply equiv_dist=> n. apply oFunctor_ne. split=> y /=; by rewrite !oFunctor_id.
Qed.
Next Obligation.
  intros F1 F2 ? A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -oFunctor_compose. apply equiv_dist=> n. apply oFunctor_ne.
  split=> y /=; by rewrite !oFunctor_compose.
Qed.
Instance oFunctor_compose_contractive1 (F1 F2 : oFunctor)
  `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} :
  oFunctorContractive F1 → oFunctorContractive (oFunctor_compose F1 F2).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_contractive; destruct Hfg; split; simpl in *; apply oFunctor_ne; by split.
Qed.

(** Version of the cofe_solver for a parametrized functor. Generalize and move
to Iris. *)
Record solution_2 (F : ofeT → oFunctor) := Solution2 {
  solution_2_car :> ∀ An `{!Cofe An} A `{!Cofe A}, ofeT;
  solution_2_cofe `{!Cofe An, !Cofe A} : Cofe (solution_2_car An A);
  solution_2_iso `{!Cofe An, !Cofe A} :>
    ofe_iso (F A (solution_2_car A An) _) (solution_2_car An A);
}.
Existing Instance solution_2_cofe.

Section cofe_solver_2.
  Context (F : ofeT → oFunctor).
  Context `{Fcontr : !∀ T, oFunctorContractive (F T)}.
  Context `{Fcofe : !∀ `{!Cofe T, Cofe Bn, !Cofe B}, Cofe (oFunctor_car (F T) Bn B)}.
  Context `{Finh : !∀ `{!Cofe T, Cofe Bn, !Cofe B}, Inhabited (oFunctor_car (F T) Bn B)}.
  Notation map := (oFunctor_map (F _)).

  Definition F_2 (An : ofeT) `{!Cofe An} (A : ofeT) `{!Cofe A} : oFunctor :=
    oFunctor_compose (F A) (F An).

  Definition T_result `{!Cofe An, !Cofe A} : solution (F_2 An A) := solver.result _.
  Definition T (An : ofeT) `{!Cofe An} (A : ofeT) `{!Cofe A} : ofeT :=
    T_result (An:=An) (A:=A).
  Instance T_cofe `{!Cofe An, !Cofe A} : Cofe (T An A) := _.
  Instance T_inhabited `{!Cofe An, !Cofe A} : Inhabited (T An A) :=
    populate (ofe_iso_1 T_result inhabitant).

  Definition T_iso_fun_aux `{!Cofe An, !Cofe A}
      (rec : prodO (F An (T An A) _ -n> T A An) (T A An -n> F An (T An A) _)) :
      prodO (F A (T A An) _ -n> T An A) (T An A -n> F A (T A An) _) :=
    (ofe_iso_1 T_result ◎ map (rec.1,rec.2), map (rec.2,rec.1) ◎ ofe_iso_2 T_result).
  Instance T_iso_aux_fun_contractive `{!Cofe An, !Cofe A} :
    Contractive (T_iso_fun_aux (An:=An) (A:=A)).
  Proof. solve_contractive. Qed.

  Definition T_iso_fun_aux_2 `{!Cofe An, !Cofe A}
      (rec : prodO (F A (T A An) _ -n> T An A) (T An A -n> F A (T A An) _)) :
      prodO (F A (T A An) _ -n> T An A) (T An A -n> F A (T A An) _) :=
    T_iso_fun_aux (T_iso_fun_aux rec).
  Instance T_iso_fun_aux_2_contractive `{!Cofe An, !Cofe A} :
    Contractive (T_iso_fun_aux_2 (An:=An) (A:=A)).
  Proof.
    intros n rec1 rec2 Hrec. rewrite /T_iso_fun_aux_2.
    f_equiv. by apply T_iso_aux_fun_contractive.
  Qed.

  Definition T_iso_fun `{!Cofe An, !Cofe A} :
      prodO (F A (T A An) _ -n> T An A) (T An A -n> F A (T A An) _) :=
    fixpoint T_iso_fun_aux_2.
  Definition T_iso_fun_unfold_1 `{!Cofe An, !Cofe A} y :
    T_iso_fun (An:=An) (A:=A).1 y ≡ (T_iso_fun_aux (T_iso_fun_aux T_iso_fun)).1 y.
  Proof. apply (fixpoint_unfold T_iso_fun_aux_2). Qed.
  Definition T_iso_fun_unfold_2 `{!Cofe An, !Cofe A} y :
    T_iso_fun (An:=An) (A:=A).2 y ≡ (T_iso_fun_aux (T_iso_fun_aux T_iso_fun)).2 y.
  Proof. apply (fixpoint_unfold T_iso_fun_aux_2). Qed.

  Lemma result_2 : solution_2 F.
  Proof using Fcontr Fcofe Finh.
    apply (Solution2 F T _)=> An Hcn A Hc.
    apply (OfeIso (T_iso_fun.1) (T_iso_fun.2)).
    - intros y. apply equiv_dist=> n. revert An Hcn A Hc y.
      induction (lt_wf n) as [n _ IH]; intros An ? A ? y.
      rewrite T_iso_fun_unfold_1 T_iso_fun_unfold_2 /=.
      rewrite -{2}(ofe_iso_12 T_result y). f_equiv.
      rewrite -(oFunctor_id (F _) (ofe_iso_2 T_result y)) -!ofe.oFunctor_compose.
      f_equiv; apply Fcontr; destruct n as [|n]; simpl; [done|].
      split => x /=; rewrite ofe_iso_21 -{2}(oFunctor_id (F _) x)
        -!ofe.oFunctor_compose; do 2 f_equiv; split=> z /=; auto.
    - intros y. apply equiv_dist=> n. revert An Hcn A Hc y.
      induction (lt_wf n) as [n _ IH]; intros An ? A ? y.
      rewrite T_iso_fun_unfold_1 T_iso_fun_unfold_2 /= ofe_iso_21.
      rewrite -(oFunctor_id (F _) y) -!ofe.oFunctor_compose.
      f_equiv; apply Fcontr; destruct n as [|n]; simpl; [done|].
      split => x /=; rewrite -{2}(ofe_iso_12 T_result x); f_equiv;
        rewrite -{2}(oFunctor_id (F _) (ofe_iso_2 T_result x)) -!ofe.oFunctor_compose;
        do 2 f_equiv; split=> z /=; auto.
  Qed.
End cofe_solver_2.
