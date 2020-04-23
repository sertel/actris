From stdpp Require Import pretty.
From actris.utils Require Import switch.
From actris.logrel Require Export ltyping session_types.
From actris.channel Require Import proto proofmode.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang.lib Require Import assert.
From iris.heap_lang Require Import notation proofmode lib.par spin_lock.

Section types.
  Context `{heapG Σ}.

  Definition lty_unit : lty Σ := Lty (λ w, ⌜ w = #() ⌝%I).
  Definition lty_bool : lty Σ := Lty (λ w, ∃ b : bool, ⌜ w = #b ⌝)%I.
  Definition lty_int : lty Σ := Lty (λ w, ∃ n : Z, ⌜ w = #n ⌝)%I.
  Definition lty_copy (A : lty Σ) : lty Σ := Lty (λ w, □ (A w))%I.
  Definition lty_arr (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    ∀ v, ▷ A1 v -∗ WP w v {{ A2 }})%I.
  (* TODO: Make a non-linear version of prod, using ∧ *)
  Definition lty_prod (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    ∃ w1 w2, ⌜w = (w1,w2)%V⌝ ∗ ▷ A1 w1 ∗ ▷ A2 w2)%I.
  Definition lty_sum (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    (∃ w1, ⌜w = InjLV w1⌝ ∗ ▷ A1 w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∗ ▷ A2 w2))%I.
  Definition lty_any : lty Σ := Lty (λ w, True%I).
  Definition lty_rec_aux (C : lty Σ → lty Σ) `{!Contractive C}
      (rec : lty Σ) : lty Σ := Lty (C rec)%I.
  Instance lty_rec_aux_contractive C `{!Contractive C} : Contractive (lty_rec_aux C).
  Proof. solve_contractive. Qed.
  Definition lty_rec (C : lty Σ → lty Σ) `{!Contractive C} : lty Σ :=
    fixpoint (lty_rec_aux C).
  Definition lty_forall (C : lty Σ → lty Σ) : lty Σ := Lty (λ w,
    ∀ A : lty Σ, WP w #() {{ C A }})%I.
  Definition lty_forall_lsty (C : lsty Σ → lty Σ) : lty Σ := Lty (λ w,
    ∀ A : lsty Σ, WP w #() {{ C A }})%I.
  Definition lty_exist (C : lty Σ → lty Σ) : lty Σ := Lty (λ w,
    ∃ A : lty Σ, ▷ C A w)%I.
  Definition lty_exist_lsty (C : lsty Σ → lty Σ) : lty Σ := Lty (λ w,
    ∃ A : lsty Σ, ▷ C A w)%I.
  Definition lty_ref_mut (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ (l : loc) (v : val), ⌜w = #l⌝ ∗ l ↦ v ∗ ▷ A v)%I.
  Definition ref_shrN := nroot .@ "shr_ref".
  Definition lty_ref_shr (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ l : loc, ⌜w = #l⌝ ∗ inv (ref_shrN .@ l) (∃ v, l ↦ v ∗ A v))%I.
  Definition lty_mutex `{lockG Σ} (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ (γ : gname) (l : loc) (lk : val),
      ⌜ w = PairV lk #l ⌝ ∗
      is_lock γ lk (∃ v_inner, l ↦ v_inner ∗ A v_inner))%I.
  Definition lty_mutexguard `{lockG Σ} (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ (γ : gname) (l : loc) (lk : val) (v : val),
      ⌜ w = PairV lk #l ⌝ ∗
      is_lock γ lk (∃ v_inner, l ↦ v_inner ∗ A v_inner) ∗
      locked γ ∗ l ↦ v)%I.
  Definition lty_chan `{chanG Σ} (P : lsty Σ) : lty Σ := Lty (λ w, w ↣ P)%I.
End types.

Notation "()" := lty_unit : lty_scope.
Notation "'copy' A" := (lty_copy A) (at level 10) : lty_scope.
Notation "A → B" := (lty_copy (lty_arr A B)) : lty_scope.
Notation "A ⊸ B" := (lty_arr A B) (at level 99, B at level 200, right associativity) : lty_scope.
Infix "*" := lty_prod : lty_scope.
Infix "+" := lty_sum : lty_scope.
Notation any := lty_any.
Notation "∀ A1 .. An , C" :=
  (lty_forall (λ A1, .. (lty_forall (λ An, C%lty)) ..)) : lty_scope.
Notation "∃ A1 .. An , C" :=
  (lty_exist (λ A1, .. (lty_exist (λ An, C%lty)) ..)) : lty_scope.
Notation "∀p A1 .. An , C" :=
  (lty_forall_lsty (λ A1, .. (lty_forall_lsty (λ An, C%lty)) ..))
  (at level 200, A1 binder, An binder, right associativity,
  format "'[ ' '[ ' ∀p A1 .. An ']' , '/' C ']'") : lty_scope.
Notation "∃p A1 .. An , C" :=
  (lty_exist_lsty (λ A1, .. (lty_exist_lsty (λ An, C%lty)) ..))
  (at level 200, A1 binder, An binder, right associativity,
  format "'[ ' '[ ' ∃p A1 .. An ']' , '/' C ']'") : type_scope.
Notation "'ref_mut' A" := (lty_ref_mut A) (at level 10) : lty_scope.
Notation "'ref_shr' A" := (lty_ref_shr A) (at level 10) : lty_scope.

Notation "'mutex' A" := (lty_mutex A) (at level 10) : lty_scope.
Notation "'mutexguard' A" := (lty_mutexguard A) (at level 10) : lty_scope.
Notation "'chan' A" := (lty_chan A) (at level 10) : lty_scope.

Section properties.
  Context `{heapG Σ}.
  Implicit Types Γ : gmap string (lty Σ).

  (** Basic properties *)
  Global Instance lty_unit_unboxed : @LTyUnboxed Σ ().
  Proof. by iIntros (v ->). Qed.
  Global Instance lty_unit_copy : @LTyCopy Σ _ ().
  Proof. iIntros (v). apply _. Qed.
  Global Instance lty_bool_unboxed : @LTyUnboxed Σ lty_bool.
  Proof. iIntros (v). by iDestruct 1 as (b) "->". Qed.
  Global Instance lty_bool_copy : @LTyCopy Σ _ lty_bool.
  Proof. iIntros (v). apply _. Qed.
  Global Instance lty_int_unboxed : @LTyUnboxed Σ lty_int.
  Proof. iIntros (v). by iDestruct 1 as (i) "->". Qed.
  Global Instance lty_int_copy : @LTyCopy Σ _ lty_int.
  Proof. iIntros (v). apply _. Qed.

  Lemma ltyped_unit Γ : ⊢ Γ ⊨ #() : ().
  Proof. iIntros "!>" (vs) "Henv /=". iApply wp_value. eauto. Qed.
  Lemma ltyped_bool Γ (b : bool) : ⊢ Γ ⊨ #b : lty_bool.
  Proof. iIntros "!>" (vs) "Henv /=". iApply wp_value. eauto. Qed.
  Lemma ltyped_nat Γ (n : Z) : ⊢ Γ ⊨ #n : lty_int.
  Proof. iIntros "!>" (vs) "Henv /=". iApply wp_value. eauto. Qed.

  (** Operator Properties *)
  Global Instance lty_bin_op_eq A : LTyUnboxed A → @LTyBinOp Σ EqOp A A lty_bool.
  Proof.
    iIntros (Q v1 v2) "A1 _". rewrite /bin_op_eval /lty_car /=.
    iDestruct (lty_unboxed with "A1") as %Hunb.
    rewrite decide_True; last solve_vals_compare_safe.
    eauto.
  Qed.
  Global Instance lty_bin_op_arith op :
    TCElemOf op [PlusOp; MinusOp; MultOp; QuotOp; RemOp;
                 AndOp; OrOp; XorOp; ShiftLOp; ShiftROp] →
    @LTyBinOp Σ op lty_int lty_int lty_int.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /lty_car /=; eauto.
  Qed.
  Global Instance lty_bin_op_compare op :
    TCElemOf op [LeOp; LtOp] →
    @LTyBinOp Σ op lty_int lty_int lty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /lty_car /=; eauto.
  Qed.
  Global Instance lty_bin_op_bool op :
    TCElemOf op [AndOp; OrOp; XorOp] →
    @LTyBinOp Σ op lty_bool lty_bool lty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /lty_car /=; eauto.
  Qed.

  (** Variable properties *)
  Lemma ltyped_var Γ (x : string) A :
    Γ !! x = Some A → ⊢ Γ ⊨ x : A ⫤ delete x Γ.
  Proof.
    iIntros (HΓx) "!>".
    iIntros (vs) "HΓ /=".
    iDestruct (env_ltyped_lookup with "HΓ") as (v ->) "[HA HΓ]"; first done.
    iApply wp_value. eauto with iFrame.
  Qed.

  (** Copy properties *)
  Global Instance lty_copy_ne : NonExpansive (@lty_copy Σ).
  Proof. solve_proper. Qed.

  Global Instance lty_copy_copy A : LTyCopy (copy A).
  Proof. iIntros (v). apply _. Qed.

  (** Arrow properties *)
  Global Instance lty_arr_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) lty_arr.
  Proof.
    intros A A' ? B B' ?.
    apply lty_ne.
    intros f.
    f_equiv.
    intros w.
    f_equiv.
    - by f_contractive.
    - apply wp_contractive.
      { apply _. }
      intros q.
      destruct n as [|n'].
      + done.
      + by simpl.
  Qed.

  Global Instance lty_arr_ne : NonExpansive2 (@lty_arr Σ _).
  Proof. solve_proper. Qed.

  Lemma ltyped_app Γ1 Γ2 Γ3 e1 e2 A1 A2 :
    (Γ2 ⊨ e1 : A1 ⊸ A2 ⫤ Γ3) -∗ (Γ1 ⊨ e2 : A1 ⫤ Γ2) -∗
    Γ1 ⊨ e1 e2 : A2 ⫤ Γ3.
  Proof.
    iIntros "#H1 #H2". iIntros (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(H2 [HΓ //])"). iIntros (v) "[HA1 HΓ]".
    wp_apply (wp_wand with "(H1 [HΓ //])"). iIntros (f) "[Hf HΓ]".
    iApply wp_frame_r. iFrame "HΓ". iApply ("Hf" $! v with "HA1").
  Qed.

  Lemma ltyped_lam Γ Γ' x e A1 A2 :
    (binder_insert x A1 Γ ⊨ e : A2 ⫤ Γ') -∗
    Γ ⊨ (λ: x, e) : A1 ⊸ A2 ⫤ ∅.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_pures.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros (v) "HA1". wp_pures.
    iDestruct ("He" $!((binder_insert x v vs)) with "[HA1 HΓ]") as "He'".
    { iApply (env_ltyped_insert with "[HA1 //] HΓ"). }
    iDestruct (wp_wand _ _ _ _ (λ v, A2 v) with "He' []") as "He'".
    { iIntros (w) "[$ _]". }
    destruct x as [|x]; rewrite /= -?subst_map_insert //.
  Qed.

  Lemma ltyped_let Γ1 Γ2 Γ3 (x : binder) e1 e2 A1 A2 :
    (Γ1 ⊨ e1 : A1 ⫤ Γ2) -∗ (binder_insert x A1 Γ2 ⊨ e2 : A2 ⫤ Γ3) -∗
    Γ1 ⊨ (let: x:=e1 in e2) : A2 ⫤ ∅.
  Proof. iIntros "#He1 #He2". iApply ltyped_app=> //. iApply ltyped_lam. Qed.

  Lemma ltyped_rec Γ Γ' f x e A1 A2 :
    env_copy Γ Γ' -∗
    (binder_insert f (A1 → A2)%lty (binder_insert x A1 Γ') ⊨ e : A2) -∗
    Γ ⊨ (rec: f x := e) : A1 → A2 ⫤ ∅.
  Proof.
    iIntros "#Hcopy #He". iIntros (vs) "!> HΓ /=". iApply wp_fupd. wp_pures.
    iDestruct ("Hcopy" with "HΓ") as "HΓ".
    iMod (fupd_mask_mono with "HΓ") as "#HΓ"; first done.
    iModIntro. iSplitL; last by iApply env_ltyped_empty.
    iLöb as "IH".
    iIntros (v) "!> HA1". wp_pures. set (r := RecV f x _).
    iDestruct ("He" $!(binder_insert f r (binder_insert x v vs))
                  with "[HΓ HA1]") as "He'".
    { iApply (env_ltyped_insert with "IH").
      iApply (env_ltyped_insert with "HA1 HΓ"). }
    iDestruct (wp_wand _ _ _ _ (λ v, A2 v) with "He' []") as "He'".
    { iIntros (w) "[$ _]". }
    destruct x as [|x], f as [|f]; rewrite /= -?subst_map_insert //.
    destruct (decide (x = f)) as [->|].
    - by rewrite subst_subst delete_idemp !insert_insert -subst_map_insert.
    - rewrite subst_subst_ne // -subst_map_insert.
      by rewrite -delete_insert_ne // -subst_map_insert.
  Qed.

  Fixpoint lty_arr_list (As : list (lty Σ)) (B : lty Σ) : lty Σ :=
    match As with
    | [] => B
    | A :: As => A ⊸ lty_arr_list As B
    end.

  Lemma lty_arr_list_spec_step A As (e : expr) B ws y i :
    (∀ v, lty_car A v -∗
          WP subst_map (<[ y +:+ pretty i := v ]>ws)
             (switch_lams y (S i) (length As) e) {{ lty_arr_list As B }}) -∗
    WP subst_map ws (switch_lams y i (length (A::As)) e)
       {{ lty_arr_list (A::As) B }}.
  Proof.
    iIntros "H". wp_pures. iIntros (v) "HA".
    iDestruct ("H" with "HA") as "H".
    rewrite subst_map_insert.
    wp_apply "H".
  Qed.

  Lemma lty_arr_list_spec As (e : expr) B ws y i n :
    n = length As →
    (∀ vs, ([∗ list] A;v ∈ As;vs, (lty_car A) v) -∗
           WP subst_map (map_string_seq y i vs ∪ ws) e {{ lty_car B }}) -∗
    WP subst_map ws (switch_lams y i n e) {{ lty_arr_list As B }}.
  Proof.
    iIntros (Hlen) "H". iRevert (Hlen).
    iInduction As as [|A As] "IH" forall (ws i e n)=> /=.
    - iIntros (->).
      iDestruct ("H" $! [] with "[$]") as "H"=> /=.
      by rewrite left_id_L.
    - iIntros (->). iApply lty_arr_list_spec_step.
      iIntros (v) "HA".
      iApply ("IH" with "[H HA]")=> //.
      iIntros (vs) "HAs".
      iSpecialize ("H" $!(v::vs))=> /=.
      do 2 rewrite insert_union_singleton_l.
      rewrite (map_union_comm ({[y +:+ pretty i := v]})); last first.
      { apply map_disjoint_singleton_l_2.
        apply lookup_map_string_seq_None_lt. eauto. }
      rewrite assoc_L. iApply ("H" with "[HA HAs]"). iFrame "HA HAs".
  Qed.

  (** Product properties  *)
  Global Instance lty_prod_copy `{!LTyCopy A1, !LTyCopy A2} : LTyCopy (A1 * A2).
  Proof. iIntros (v). apply _. Qed.
  Global Instance lty_prod_contractive n:
    Proper (dist_later n ==> dist_later n ==> dist n) (@lty_prod Σ).
  Proof. solve_contractive. Qed.
  Global Instance lty_prod_ne : NonExpansive2 (@lty_prod Σ).
  Proof. solve_proper. Qed.

  Lemma ltyped_pair Γ1 Γ2 Γ3 e1 e2 A1 A2 :
    (Γ2 ⊨ e1 : A1 ⫤ Γ3) -∗ (Γ1 ⊨ e2 : A2 ⫤ Γ2) -∗
    Γ1 ⊨ (e1,e2) : A1 * A2 ⫤ Γ3.
  Proof.
    iIntros "#H1 #H2". iIntros (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(H2 [HΓ //])"); iIntros (w2) "[HA2 HΓ]".
    wp_apply (wp_wand with "(H1 [HΓ //])"); iIntros (w1) "[HA1 HΓ]".
    wp_pures. iFrame "HΓ". iExists w1, w2. by iFrame.
  Qed.

  Definition split : val := λ: "pair" "f", "f" (Fst "pair") (Snd "pair").

  Lemma ltyped_split A1 A2 B :
    ⊢ ∅ ⊨ split : A1 * A2 → (A1 ⊸ A2 ⊸ B) ⊸ B.
  Proof.
    iIntros (vs) "!> HΓ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (v) "Hv". rewrite /split. wp_pures.
    iDestruct "Hv" as (w1 w2 ->) "[Hw1 Hw2]".
    iIntros (f) "Hf". wp_pures.
    iPoseProof ("Hf" with "Hw1") as "Hf".
    wp_apply (wp_wand with "Hf").
    iIntros (g) "Hg". iApply ("Hg" with "Hw2").
  Qed.

  (** Sum Properties *)
  Global Instance lty_sum_copy `{!LTyCopy A1, !LTyCopy A2} : LTyCopy (A1 + A2).
  Proof. iIntros (v). apply _. Qed.
  Global Instance lty_sum_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lty_sum Σ).
  Proof. solve_contractive. Qed.
  Global Instance lty_sum_ne : NonExpansive2 (@lty_sum Σ).
  Proof. solve_proper. Qed.

  Lemma ltyped_injl Γ e A1 A2 :
    (Γ ⊨ e : A1) -∗ Γ ⊨ InjL e : A1 + A2.
  Proof.
    iIntros "#HA" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(HA [HΓ //])").
    iIntros (v) "[HA' $]". wp_pures.
    iLeft. iExists v. auto.
  Qed.

  Lemma ltyped_injr Γ e A1 A2 :
    (Γ ⊨ e : A2) -∗ Γ ⊨ InjR e : A1 + A2.
  Proof.
    iIntros "#HA" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(HA [HΓ //])").
    iIntros (v) "[HA' $]". wp_pures.
    iRight. iExists v. auto.
  Qed.

  Definition paircase : val := λ: "pair" "left" "right",
    Case "pair" "left" "right".

  Lemma ltyped_paircase A1 A2 B :
    ⊢ ∅ ⊨ paircase : A1 + A2 → (A1 ⊸ B) ⊸ (A2 ⊸ B) ⊸ B.
  Proof.
    iIntros (vs) "!> HΓ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    rewrite /paircase. iIntros "!>" (p) "Hp". wp_pures.
    iIntros (f_left) "Hleft". wp_pures.
    iIntros (f_right) "Hright". wp_pures.
    iDestruct "Hp" as "[Hp|Hp]".
    - iDestruct "Hp" as (w1 ->) "Hp". wp_pures.
      wp_apply (wp_wand with "(Hleft [Hp //])").
      iIntros (v) "HB". iApply "HB".
    - iDestruct "Hp" as (w2 ->) "Hp". wp_pures.
      wp_apply (wp_wand with "(Hright [Hp //])").
      iIntros (v) "HB". iApply "HB".
  Qed.

  (** Universal Properties *)
  Global Instance lty_forall_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_forall Σ _).
  Proof. solve_proper. Qed.
  Global Instance lty_forall_contractive n :
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (@lty_forall Σ _).
  Proof.
    intros F F' A. apply lty_ne=> w. f_equiv=> B.
    apply (wp_contractive _ _ _ _ _)=> u. specialize (A B).
    by destruct n as [|n]; simpl.
  Qed.

  Global Instance lty_forall_lsty_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_forall_lsty Σ _).
  Proof. solve_proper. Qed.
  Global Instance lty_forall_lsty_contractive n :
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (@lty_forall_lsty Σ _).
  Proof.
    intros F F' A. apply lty_ne=> w. f_equiv=> B.
    apply (wp_contractive _ _ _ _ _)=> u. specialize (A B).
    by destruct n as [|n]; simpl.
  Qed.

  Lemma ltyped_tlam Γ e C :
    (∀ A, Γ ⊨ e : C A ⫤ ∅) -∗ Γ ⊨ (λ: <>, e) : ∀ A, C A ⫤ ∅.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=". wp_pures.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros (A) "/=". wp_pures.
    iApply (wp_wand with "(He HΓ)"). iIntros (v) "[$ _]".
  Qed.
  Lemma ltyped_tlam_lsty Γ e C :
    (∀ A, Γ ⊨ e : C A ⫤ ∅) -∗ Γ ⊨ (λ: <>, e) : ∀p A, C A ⫤ ∅.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=". wp_pures.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros (A) "/=". wp_pures.
    iApply (wp_wand with "(He HΓ)"). iIntros (v) "[$ _]".
  Qed.

  Lemma ltyped_tapp Γ Γ2 e C A :
    (Γ ⊨ e : ∀ A, C A ⫤ Γ2) -∗ Γ ⊨ e #() : C A ⫤ Γ2.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "[HB HΓ]".
    by iApply (wp_wand with "HB [HΓ]"); iIntros (v) "$ //".
  Qed.
  Lemma ltyped_tapp_lsty Γ Γ2 e C A :
    (Γ ⊨ e : ∀p A, C A ⫤ Γ2) -∗ Γ ⊨ e #() : C A ⫤ Γ2.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "[HB HΓ]".
    by iApply (wp_wand with "HB [HΓ]"); iIntros (v) "$ //".
  Qed.

  (** Existential properties *)
  Global Instance lty_exist_copy C (Hcopy : ∀ A, LTyCopy (C A)) :
    (LTyCopy (lty_exist C)).
  Proof. intros v. apply bi.exist_persistent. intros A.
         apply bi.later_persistent. apply Hcopy. Qed.
  Global Instance lty_exist_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_exist Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_exist_contractive n :
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (@lty_exist Σ).
  Proof. solve_contractive. Qed.

  Global Instance lty_exist_lsty_copy C (Hcopy : ∀ A, LTyCopy (C A)) :
    (LTyCopy (lty_exist_lsty C)).
  Proof. intros v. apply bi.exist_persistent. intros A.
         apply bi.later_persistent. apply Hcopy. Qed.
  Global Instance lty_exist_lsty_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_exist_lsty Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_exist_lsty_contractive n :
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (@lty_exist_lsty Σ).
  Proof. solve_contractive. Qed.

  Lemma ltyped_pack Γ e C A :
    (Γ ⊨ e : C A) -∗ Γ ⊨ e : ∃ A, C A.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "[HB $]". by iExists A.
  Qed.
  Lemma ltyped_pack_lsty Γ e C A :
    (Γ ⊨ e : C A) -∗ Γ ⊨ e : ∃p A, C A.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "[HB $]". by iExists A.
  Qed.

  Definition unpack : val := λ: "exist" "f", "f" #() "exist".

  Lemma ltyped_unpack C B :
    ⊢ ∅ ⊨ unpack : (∃ A, C A) → (∀ A, C A ⊸ B) ⊸ B.
  Proof.
    iIntros (vs) "!> HΓ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (v). iDestruct 1 as (A) "Hv".
    rewrite /unpack. wp_pures.
    iIntros (fty) "Hfty". wp_pures.
    iSpecialize ("Hfty" $! A).
    wp_bind (fty _). wp_apply (wp_wand with "Hfty").
    iIntros (f) "Hf".
    wp_apply (wp_wand with "(Hf [Hv //])").
    iIntros (w) "HB". iApply "HB".
  Qed.
  Lemma ltyped_unpack_lsty C B :
    ⊢ ∅ ⊨ unpack : (∃p A, C A) → (∀p A, C A ⊸ B) ⊸ B.
  Proof.
    iIntros (vs) "!> HΓ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (v). iDestruct 1 as (A) "Hv".
    rewrite /unpack. wp_pures.
    iIntros (fty) "Hfty". wp_pures.
    iSpecialize ("Hfty" $! A).
    wp_bind (fty _). wp_apply (wp_wand with "Hfty").
    iIntros (f) "Hf".
    wp_apply (wp_wand with "(Hf [Hv //])").
    iIntros (w) "HB". iApply "HB".
  Qed.

  (** Mutable Reference properties *)
  Global Instance lty_ref_mut_contractive : Contractive (@lty_ref_mut Σ _).
  Proof. solve_contractive. Qed.
  Global Instance lty_ref_mut_ne : NonExpansive2 (@lty_ref_mut Σ _).
  Proof. solve_proper. Qed.
  Global Instance lty_ref_mut_unboxed A : LTyUnboxed (ref_mut A).
  Proof. iIntros (v). by iDestruct 1 as (i w ->) "?". Qed.

  Definition alloc : val := λ: "init", ref "init".
  Lemma ltyped_alloc A :
    ⊢ ∅ ⊨ alloc : A → ref_mut A.
  Proof.
    iIntros (vs) "!> HΓ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (v) "Hv". rewrite /alloc. wp_pures.
    wp_alloc l as "Hl".
    iExists l, v. iSplit=> //.
    iFrame "Hv Hl".
  Qed.

  (* The intuition for the any is that the value is still there, but
  it no longer holds any Iris resources. Just as in Rust, where a move
  might turn into a memcpy, which leaves the original memory
  unmodified, but moves the resources, in the sense that you can no
  longer use the memory at the old location. *)
  Definition load : val := λ: "r", (!"r", "r").
  Lemma ltyped_load A :
    ⊢ ∅ ⊨ load : ref_mut A → A * ref_mut any.
  Proof.
    iIntros (vs) "!> HΓ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (v) "Hv". rewrite /load. wp_pures.
    iDestruct "Hv" as (l w ->) "[Hl Hw]".
    wp_load. wp_pures.
    iExists w, #l. iSplit=> //. iFrame "Hw".
    iExists l, w. iSplit=> //. iFrame "Hl".
    by iModIntro.
  Qed.

  Lemma ltyped_load_copy A {copyA : LTyCopy A} :
    ⊢ ∅ ⊨ load : ref_mut A → A * ref_mut A.
  Proof.
    iIntros (vs) "!> HΓ /=".
    iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (v) "Hv". rewrite /load. wp_pures.
    iDestruct "Hv" as (l w ->) "[Hl #Hw]".
    wp_load. wp_pures.
    iExists w, #l. iSplit=> //. iFrame "Hw".
    iExists l, w. iSplit=> //. iFrame "Hl".
    by iModIntro.
  Qed.

  Definition store : val := λ: "r" "new", "r" <- "new";; "r".

  Lemma ltyped_store A B :
    ⊢ ∅ ⊨ store : ref_mut A → B ⊸ ref_mut B.
  Proof.
    iIntros (vs) "!> HΓ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (v) "Hv". rewrite /store. wp_pures.
    iDestruct "Hv" as (l old ->) "[Hl Hold]".
    iIntros (new) "Hnew". wp_store.
    iExists l, new. eauto with iFrame.
  Qed.

  (** Weak Reference properties *)
  Global Instance lty_ref_shr_contractive : Contractive (@lty_ref_shr Σ _).
  Proof. solve_contractive. Qed.
  Global Instance lty_ref_shr_ne : NonExpansive2 (@lty_ref_shr Σ _).
  Proof. solve_proper. Qed.
  Global Instance lty_ref_shr_unboxed A : LTyUnboxed (ref_shr A).
  Proof. iIntros (v). by iDestruct 1 as (l ->) "?". Qed.
  Global Instance lty_ref_shr_copy A : LTyCopy (ref_shr A).
  Proof. iIntros (v). apply _. Qed.

  Definition fetch_and_add : val := λ: "r" "inc", FAA "r" "inc".
  Lemma ltyped_fetch_and_add :
    ⊢ ∅ ⊨ fetch_and_add : ref_shr lty_int → lty_int → lty_int.
  Proof.
    iIntros (vs) "!> _ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (r) "Hr".
    iApply wp_fupd. rewrite /fetch_and_add; wp_pures.
    iDestruct "Hr" as (l ->) "Hr".
    iMod (fupd_mask_mono with "Hr") as "#Hr"; first done.
    iIntros "!> !>" (inc) "Hinc". wp_pures.
    iDestruct "Hinc" as %[k ->].
    iInv (ref_shrN .@ l) as (n) "[>Hl >Hn]" "Hclose".
    iDestruct "Hn" as %[m ->]. wp_faa.
    iMod ("Hclose" with "[Hl]") as %_.
    { iExists #(m + k). iFrame "Hl". by iExists (m + k). }
    by iExists m.
  Qed.

  Lemma ltyped_ref_shr_load (A : lty Σ) {copyA : LTyCopy A} :
    ⊢ ∅ ⊨ load : ref_shr A → (A * ref_shr A).
  Proof.
    iIntros (vs) "!> _ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (r) "Hr".
    iApply wp_fupd. rewrite /load; wp_pures.
    iDestruct "Hr" as (l ->) "Hr".
    iMod (fupd_mask_mono with "Hr") as "#Hr"; first done.
    wp_bind (!#l)%E.
    iInv (ref_shrN .@ l) as (v) "[>Hl #HA]" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hl HA]") as "_".
    { iExists v. iFrame "Hl HA". }
    iIntros "!>". wp_pures. iIntros "!>".
    iExists _, _.
    iSplit; first done.
    iFrame "HA".
    iExists _.
    iSplit; first done.
    by iFrame "Hr".
  Qed.

  Lemma ltyped_ref_shrstore (A : lty Σ) :
    ⊢ ∅ ⊨ store : ref_shr A → A → ref_shr A.
  Proof.
    iIntros (vs) "!> _ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (r) "Hr".
    iApply wp_fupd. rewrite /store; wp_pures.
    iDestruct "Hr" as (l ->) "#Hr".
    iIntros "!> !>" (x) "HA". wp_pures.
    wp_bind (_ <- _)%E.
    iInv (ref_shrN .@ l) as (v) "[>Hl _]" "Hclose".
    wp_store. iMod ("Hclose" with "[Hl HA]") as "_".
    { iExists x. iFrame "Hl HA". }
    iModIntro. wp_pures. iExists _. iSplit; first done. by iFrame "Hr".
  Qed.

  Section with_lock.
    Context `{lockG Σ}.

    (** Mutex properties *)
    Global Instance lty_mutex_contractive : Contractive (@lty_mutex Σ _ _).
    Proof. solve_contractive. Qed.
    Global Instance lty_mutex_ne : NonExpansive (@lty_mutex Σ _ _).
    Proof. solve_proper. Qed.

    Global Instance lty_mutexguard_contractive : Contractive (@lty_mutexguard Σ _ _).
    Proof. solve_contractive. Qed.
    Global Instance lty_mutexguard_ne : NonExpansive (@lty_mutexguard Σ _ _).
    Proof. solve_proper. Qed.

    Definition mutexalloc : val := λ: "x", (newlock #(), ref "x").
    Lemma ltyped_mutexalloc A :
      ⊢ ∅ ⊨ mutexalloc : A → mutex A.
    Proof.
      iIntros (vs) "!> HΓ /=". iApply wp_value.
      iSplitL; last by iApply env_ltyped_empty.
      iIntros "!>" (v) "Hv". rewrite /mutexalloc. wp_pures.
      wp_alloc l as "Hl".
      wp_bind (newlock _).
      set (N := nroot .@ "makelock").
      iAssert (∃ inner, l ↦ inner ∗ A inner)%I with "[Hl Hv]" as "Hlock".
      { iExists v. iFrame "Hl Hv". }
      wp_apply (newlock_spec with "Hlock").
      iIntros (lk γ) "Hlock".
      wp_pures. iExists γ, l, lk. iSplit=> //.
    Qed.

    Definition mutexacquire : val := λ: "x", acquire (Fst "x");; (! (Snd "x"), "x").
    Lemma ltyped_mutexacquire A :
      ⊢ ∅ ⊨ mutexacquire : mutex A → A * mutexguard A.
    Proof.
      iIntros (vs) "!> HΓ /=". iApply wp_value.
      iSplitL; last by iApply env_ltyped_empty.
      iIntros "!>" (m) "Hm". rewrite /mutexacquire. wp_pures.
      iDestruct "Hm" as (γ l lk ->) "Hlock".
      iMod (fupd_mask_mono with "Hlock") as "#Hlock"; first done.
      wp_bind (acquire _).
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hinner]".
      wp_pures.
      iDestruct "Hinner" as (v) "[Hl HA]".
      wp_load. wp_pures.
      iExists v, (lk, #l)%V. iSplit=> //.
      iFrame "HA".
      iExists γ, l, lk, v. iSplit=> //.
      by iFrame "Hl Hlocked Hlock".
    Qed.

    Definition mutexrelease : val :=
      λ: "inner" "guard", Snd "guard" <- "inner";; release (Fst "guard");; "guard".
    Lemma ltyped_mutexrelease A :
      ⊢ ∅ ⊨ mutexrelease : A → mutexguard A ⊸ mutex A.
    Proof.
      iIntros (vs) "!> HΓ /=". iApply wp_value.
      iSplitL; last by iApply env_ltyped_empty.
      iIntros "!>" (w1) "Hw1". rewrite /mutexrelease. wp_pures.
      iIntros (w2) "Hw2". wp_pures.
      iDestruct "Hw2" as (γ l lk inner ->) "[#Hlock [Hlocked Hinner]]".
      wp_store.
      iAssert (∃ inner : val, l ↦ inner ∗ A inner)%I
        with "[Hinner Hw1]" as "Hinner".
      { iExists w1. iFrame "Hinner Hw1". }
      wp_bind (release _).
      wp_apply (release_spec γ _ (∃ inner, l ↦ inner ∗ A inner)%I
                  with "[Hlocked Hinner]").
      { iFrame "Hlock Hlocked".
        iDestruct "Hinner" as (v) "[Hl HA]". eauto with iFrame. }
      iIntros "_". wp_pures.
      iExists γ, l, lk. iSplit=> //.
    Qed.
  End with_lock.

  Section with_spawn.
    Context `{spawnG Σ}.

    (** Parallel composition properties *)
    Definition parallel : val := λ: "e1" "e2", par "e1" "e2".

    Lemma ltyped_parallel A B :
      ⊢ ∅ ⊨ parallel : (() ⊸ A) → (() ⊸ B) ⊸ (A * B).
    Proof.
      iIntros (vs) "!> HΓ /=". iApply wp_value.
      iSplitL; last by iApply env_ltyped_empty.
      iIntros "!>" (fa) "Hfa". rewrite /parallel. wp_pures.
      iIntros (fb) "Hfb". wp_pures.
      wp_apply (par_spec A B with "[Hfa] [Hfb]").
      - by wp_apply "Hfa".
      - by wp_apply "Hfb".
      - iIntros (v1 v2) "[HA HB] !>". iExists v1, v2. eauto with iFrame.
    Qed.
  End with_spawn.

  Section with_chan.
    Context `{chanG Σ}.

    Global Instance lty_chan_ne : NonExpansive lty_chan.
    Proof. solve_proper. Qed.

    Definition chanalloc : val := λ: "u", let: "cc" := new_chan #() in "cc".
    Lemma ltyped_chanalloc S :
      ⊢ ∅ ⊨ chanalloc : () → (chan S * chan (lsty_dual S)).
    Proof.
      iIntros (vs) "!> HΓ /=". iApply wp_value.
      iSplitL; last by iApply env_ltyped_empty.
      iIntros "!>" (u) ">->". rewrite /chanalloc. wp_pures.
      wp_apply (new_chan_spec with "[//]"); iIntros (c1 c2) "Hp".
      iDestruct "Hp" as "[Hp1 Hp2]". wp_pures.
      iExists c1, c2. iSplit=> //. iSplitL "Hp1"; by iModIntro.
    Qed.

    Definition chansend : val := λ: "chan" "val", send "chan" "val";; "chan".
    Lemma ltyped_chansend A S :
      ⊢ ∅ ⊨ chansend : chan (<!!> A; S) → A ⊸ chan S.
    Proof.
      iIntros (vs) "!> HΓ /=". iApply wp_value.
      iSplitL; last by iApply env_ltyped_empty.
      iIntros "!>" (c) "Hc". rewrite /chansend. wp_pures.
      iIntros (w) "Hw". wp_pures.
      wp_send with "[$Hw]". wp_pures. iFrame "Hc".
    Qed.

    Lemma ltyped_send Γ Γ' (x : string) e A S :
      (Γ ⊨ e : A ⫤ <[x:=(chan (<!!> A; S))%lty]> Γ') -∗
      Γ ⊨ send x e : () ⫤ <[x:=(chan S)%lty]> Γ'.
    Proof.
      iIntros "#He !>" (vs) "HΓ"=> /=.
      wp_bind (subst_map vs e).
      iApply (wp_wand with "(He HΓ)"); iIntros (v) "[HA HΓ']".
      iDestruct (env_ltyped_lookup with "HΓ'") as (v' Heq) "[Hc HΓ']".
      { by apply lookup_insert. }
      rewrite Heq.
      wp_send with "[HA //]".
      iSplitR; first done.
      iDestruct (env_ltyped_insert _ _ x (chan _) with "[Hc //] HΓ'")
        as "HΓ'"=> /=.
      by rewrite insert_delete insert_insert (insert_id vs).
    Qed.

    Definition chanrecv : val := λ: "chan", (recv "chan", "chan").
    Lemma ltyped_chanrecv A S :
      ⊢ ∅ ⊨ chanrecv : chan (<??> A; S) → A * chan S.
    Proof.
      iIntros (vs) "!> HΓ /=". iApply wp_value.
      iSplitL; last by iApply env_ltyped_empty.
      iIntros "!>" (c) "Hc". rewrite /chanrecv. wp_pures.
      wp_recv (v) as "HA". wp_pures.
      iExists v, c. eauto with iFrame.
    Qed.

    Lemma ltyped_recv Γ (x : string) A S :
      ⊢ <[x := (chan (<??> A; S))%lty]>Γ ⊨ recv x : A ⫤ <[x:=(chan S)%lty]> Γ.
    Proof.
      iIntros "!>" (vs) "HΓ"=> /=.
      iDestruct (env_ltyped_lookup with "HΓ") as (v' Heq) "[Hc HΓ]".
      { by apply lookup_insert. }
      rewrite Heq.
      wp_recv (v) as "HA".
      iSplitL "HA"; first done.
      iDestruct (env_ltyped_insert _ _ x (chan _) _ with "[Hc //] HΓ") as "HΓ"=> /=.
      by rewrite insert_delete !insert_insert (insert_id vs).
    Qed.

    Definition chanselect : val := λ: "c" "i", send "c" "i";; "c".
    Lemma ltyped_chanselect Γ (c : val) (i : Z) S Ss :
      Ss !! i = Some S →
      (Γ ⊨ c : chan (lsty_select Ss)) -∗
      Γ ⊨ chanselect c #i : chan S.
    Proof.
      iIntros (Hin) "#Hc !>".
      iIntros (vs) "H /=".
      rewrite /chanselect.
      iMod (wp_value_inv with "(Hc H)") as "[Hc' HΓ]".
      wp_send with "[]"; [by eauto|].
      rewrite (lookup_total_correct Ss i S)=> //.
      wp_pures. iFrame.
    Qed.

    Definition chanbranch (xs : list Z) : val := λ: "c",
      switch_lams "f" 0 (length xs) $
      let: "y" := recv "c" in
      switch_body "y" 0 xs (assert: #false) $ λ i, ("f" +:+ pretty i) "c".

    Lemma ltyped_chanbranch Ss A xs :
      (∀ x, x ∈ xs ↔ is_Some (Ss !! x)) →
      ⊢ ∅ ⊨ chanbranch xs : chan (lsty_branch Ss) ⊸
        lty_arr_list ((λ x, (chan (Ss !!! x) ⊸ A)%lty) <$> xs) A.
    Proof.
      iIntros (Hdom) "!>". iIntros (vs) "Hvs".
      iApply wp_value.
      iSplitL; last by iApply env_ltyped_empty.
      iIntros (c) "Hc". wp_lam.
      rewrite -subst_map_singleton.
      iApply lty_arr_list_spec.
      { by rewrite fmap_length. }
      iIntros (ws) "H".
      rewrite big_sepL2_fmap_l.
      iDestruct (big_sepL2_length with "H") as %Heq.
      rewrite -insert_union_singleton_r; last by apply lookup_map_string_seq_None.
      rewrite /= lookup_insert.
      wp_recv (x) as "HPsx". iDestruct "HPsx" as %HPs_Some.
      wp_pures.
      rewrite -subst_map_insert.
      assert (x ∈ xs) as Hin by naive_solver.
      pose proof (list_find_elem_of (x =.) xs x) as [[n z] Hfind_Some]; [done..|].
      iApply switch_body_spec.
      { apply fmap_Some_2, Hfind_Some. }
      { by rewrite lookup_insert. }
      simplify_map_eq. rewrite lookup_map_string_seq_Some.
      assert (xs !! n = Some x) as Hxs_Some.
      { by apply list_find_Some in Hfind_Some as [? [-> _]]. }
      assert (is_Some (ws !! n)) as [w Hws_Some].
      { apply lookup_lt_is_Some_2. rewrite -Heq. eauto using lookup_lt_Some. }
      iDestruct (big_sepL2_lookup _ xs ws n with "H") as "HA"; [done..|].
      rewrite Hws_Some. by iApply "HA".
    Qed.
  End with_chan.
End properties.
