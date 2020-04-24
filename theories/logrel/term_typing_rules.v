From stdpp Require Import pretty.
From iris.bi.lib Require Import core.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import metatheory.
From iris.heap_lang.lib Require Export spawn par assert.
From actris.logrel Require Export subtyping typing_judgment session_types.
From actris.logrel Require Import environments.
From actris.utils Require Import switch.
From actris.channel Require Import proofmode.

Section properties.
  Context `{heapG Σ}.
  Implicit Types A B : ltty Σ.
  Implicit Types S T : lsty Σ.
  Implicit Types Γ : gmap string (ltty Σ).

  (** Variable properties *)
  Lemma ltyped_var Γ (x : string) A :
    Γ !! x = Some A → ⊢ Γ ⊨ x : A ⫤ delete x Γ.
  Proof.
    iIntros (HΓx) "!>"; iIntros (vs) "HΓ /=".
    iDestruct (env_ltyped_lookup with "HΓ") as (v ->) "[HA HΓ]"; first done.
    iApply wp_value. eauto with iFrame.
  Qed.

  (** Subtyping *)
  Theorem ltyped_subsumption Γ Γ2 e τ1 τ2 :
    τ1 <: τ2 -∗ (Γ ⊨ e : τ1 ⫤ Γ2) -∗ (Γ ⊨ e : τ2 ⫤ Γ2).
  Proof.
    iIntros "#Hle #Hltyped" (vs) "!> Henv".
    iDestruct ("Hltyped" with "Henv") as "Hltyped'".
    iApply (wp_wand with "Hltyped' [Hle]").
    iIntros (v) "[H1 $]". by iApply "Hle".
  Qed.

  (** Basic properties *)
  Lemma ltyped_unit Γ : ⊢ Γ ⊨ #() : ().
  Proof. iIntros "!>" (vs) "Henv /=". iApply wp_value. eauto. Qed.
  Lemma ltyped_bool Γ (b : bool) : ⊢ Γ ⊨ #b : lty_bool.
  Proof. iIntros "!>" (vs) "Henv /=". iApply wp_value. eauto. Qed.
  Lemma ltyped_nat Γ (n : Z) : ⊢ Γ ⊨ #n : lty_int.
  Proof. iIntros "!>" (vs) "Henv /=". iApply wp_value. eauto. Qed.

  (** Arrow properties *)
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
    iDestruct (wp_wand _ _ _ _ (ltty_car A2) with "He' []") as "He'".
    { iIntros (w) "[$ _]". }
    destruct x as [|x]; rewrite /= -?subst_map_insert //.
  Qed.

  (* Typing rule for introducing copyable functions *)
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
    iDestruct (wp_wand _ _ _ _ (ltty_car A2) with "He' []") as "He'".
    { iIntros (w) "[$ _]". }
    destruct x as [|x], f as [|f]; rewrite /= -?subst_map_insert //.
    destruct (decide (x = f)) as [->|].
    - by rewrite subst_subst delete_idemp !insert_insert -subst_map_insert.
    - rewrite subst_subst_ne // -subst_map_insert.
      by rewrite -delete_insert_ne // -subst_map_insert.
  Qed.

  Lemma ltyped_let Γ1 Γ2 Γ3 (x : binder) e1 e2 A1 A2 :
    (Γ1 ⊨ e1 : A1 ⫤ Γ2) -∗ (binder_insert x A1 Γ2 ⊨ e2 : A2 ⫤ Γ3) -∗
    Γ1 ⊨ (let: x:=e1 in e2) : A2 ⫤ ∅.
  Proof. iIntros "#He1 #He2". iApply ltyped_app; last done. by iApply ltyped_lam. Qed.

  Fixpoint lty_arr_list (As : list (ltty Σ)) (B : ltty Σ) : ltty Σ :=
    match As with
    | [] => B
    | A :: As => A ⊸ lty_arr_list As B
    end.

  Lemma lty_arr_list_spec_step A As (e : expr) B ws y i :
    (∀ v, ltty_car A v -∗
      WP subst_map (<[y+:+pretty i:=v]> ws)
         (switch_lams y (S i) (length As) e) {{ ltty_car (lty_arr_list As B) }}) -∗
    WP subst_map ws (switch_lams y i (S (length As)) e)
       {{ ltty_car (lty_arr_list (A :: As) B) }}.
  Proof.
    iIntros "H". wp_pures. iIntros (v) "HA".
    iDestruct ("H" with "HA") as "H".
    rewrite subst_map_insert.
    wp_apply "H".
  Qed.

  Lemma lty_arr_list_spec As (e : expr) B ws y i n :
    n = length As →
    (∀ vs, ([∗ list] A;v ∈ As;vs, ltty_car A v) -∗
           WP subst_map (map_string_seq y i vs ∪ ws) e {{ ltty_car B }}) -∗
    WP subst_map ws (switch_lams y i n e) {{ ltty_car (lty_arr_list As B) }}.
  Proof.
    iIntros (Hlen) "H".
    iInduction As as [|A As] "IH" forall (ws i e n Hlen); simplify_eq/=.
    - iDestruct ("H" $! [] with "[$]") as "H"=> /=.
      by rewrite left_id_L.
    - iApply lty_arr_list_spec_step. iIntros (v) "HA".
      iApply ("IH" with "[//]"). iIntros (vs) "HAs".
      iSpecialize ("H" $! (v::vs)); simpl.
      do 2 rewrite insert_union_singleton_l.
      rewrite (map_union_comm ({[y +:+ pretty i := v]})); last first.
      { apply map_disjoint_singleton_l_2.
        apply lookup_map_string_seq_None_lt. eauto. }
      rewrite assoc_L. iApply ("H" with "[$HA $HAs]").
  Qed.

  (** Product properties  *)
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
  Lemma ltyped_tlam Γ e k Mlow Mup (C : lty Σ k → ltty Σ) :
    (∀ M, Mlow <: M -∗ M <: Mup -∗ Γ ⊨ e : C M ⫤ ∅) -∗
    Γ ⊨ (λ: <>, e) : lty_forall Mlow Mup C ⫤ ∅.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=". wp_pures.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros (M) "/= Hlow Hup". wp_pures.
    iApply (wp_wand with "(He Hlow Hup HΓ)"). iIntros (v) "[$ _]".
  Qed.

  Lemma ltyped_tapp Γ Γ2 e k (C : lty Σ k → ltty Σ) Mlow Mup M :
    Mlow <: M -∗ M <: Mup -∗
    (Γ ⊨ e : lty_forall Mlow Mup C ⫤ Γ2) -∗
    Γ ⊨ e #() : C M ⫤ Γ2.
  Proof.
    iIntros "#Hlow #Hup #He" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "[HB HΓ] /=".
    iApply (wp_wand with "(HB Hlow Hup) [HΓ]"). by iIntros (v) "$".
  Qed.

  (** Existential properties *)
  Definition unpack : val := λ: "exist" "f", "f" #() "exist".

  Lemma ltyped_unpack k (C : lty Σ k → ltty Σ) Mlow Mup B :
    ⊢ ∅ ⊨ unpack : lty_exist Mlow Mup C → lty_forall Mlow Mup (λ M, C M ⊸ B)%lty ⊸ B.
  Proof.
    iIntros (vs) "!> HΓ /=". iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros "!>" (v). iDestruct 1 as (M) "(Hlow & Hup & Hv)".
    rewrite /unpack. wp_pures.
    iIntros (fty) "Hfty". wp_pures.
    iSpecialize ("Hfty" $! M).
    wp_bind (fty _). wp_apply (wp_wand with "(Hfty Hlow Hup)").
    iIntros (f) "Hf".
    wp_apply (wp_wand with "(Hf [Hv //])").
    iIntros (w) "HB". iApply "HB".
  Qed.

  (** Mutable Reference properties *)
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
    ⊢ ∅ ⊨ load : ref_mut A → A * ref_mut ⊤.
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

  (* TODO(COPY) *)
  (* Lemma ltyped_load_copy A {copyA : LTyCopy A} : *)
  (*   ⊢ ∅ ⊨ load : ref_mut A → A * ref_mut A. *)
  (* Proof. *)
  (*   iIntros (vs) "!> HΓ /=". *)
  (*   iApply wp_value. *)
  (*   iIntros "!>" (v) "Hv". rewrite /load. wp_pures. *)
  (*   iDestruct "Hv" as (l w ->) "[Hl #Hw]". *)
  (*   wp_load. wp_pures. *)
  (*   iExists w, #l. iSplit=> //. iFrame "Hw". *)
  (*   iExists l, w. iSplit=> //. iFrame "Hl". *)
  (*   by iModIntro. *)
  (* Qed. *)

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
    { iExists #(m + k). iFrame "Hl". by iExists (m + k)%Z. }
    by iExists m.
  Qed.

  (* TODO(COPY) *)
  (* Lemma ltyped_ref_shr_load (A : lty Σ) {copyA : LTyCopy A} : *)
  (*   ⊢ ∅ ⊨ load : ref_shr A → (A * ref_shr A). *)
  (* Proof. *)
  (*   iIntros (vs) "!> _ /=". iApply wp_value. iIntros "!>" (r) "Hr". *)
  (*   iApply wp_fupd. rewrite /load; wp_pures. *)
  (*   iDestruct "Hr" as (l ->) "Hr". *)
  (*   iMod (fupd_mask_mono with "Hr") as "#Hr"; first done. *)
  (*   wp_bind (!#l)%E. *)
  (*   iInv (ref_shrN .@ l) as (v) "[>Hl #HA]" "Hclose". *)
  (*   wp_load. *)
  (*   iMod ("Hclose" with "[Hl HA]") as "_". *)
  (*   { iExists v. iFrame "Hl HA". } *)
  (*   iIntros "!>". wp_pures. iIntros "!>". *)
  (*   iExists _, _. *)
  (*   iSplit; first done. *)
  (*   iFrame "HA". *)
  (*   iExists _. *)
  (*   iSplit; first done. *)
  (*   by iFrame "Hr". *)
  (* Qed. *)

  Lemma ltyped_ref_shrstore A :
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
      iAssert (∃ inner, l ↦ inner ∗ ltty_car A inner)%I with "[Hl Hv]" as "Hlock".
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
      iAssert (∃ inner : val, l ↦ inner ∗ ltty_car A inner)%I
        with "[Hinner Hw1]" as "Hinner".
      { iExists w1. iFrame "Hinner Hw1". }
      wp_bind (release _).
      wp_apply (release_spec γ _ (∃ inner, l ↦ inner ∗ ltty_car A inner)%I
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
      wp_apply (par_spec (ltty_car A) (ltty_car B) with "[Hfa] [Hfb]").
      - by wp_apply "Hfa".
      - by wp_apply "Hfb".
      - iIntros (v1 v2) "[HA HB] !>". iExists v1, v2. eauto with iFrame.
    Qed.
  End with_spawn.

  Section with_chan.
    Context `{chanG Σ}.

    Definition chanalloc : val := λ: "u", let: "cc" := new_chan #() in "cc".
    Lemma ltyped_chanalloc S :
      ⊢ ∅ ⊨ chanalloc : () → (chan S * chan (lty_dual S)).
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
      ⊢ <[x := (chan (<??> A; S))%lty]> Γ ⊨ recv x : A ⫤ <[x:=(chan S)%lty]> Γ.
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
      (Γ ⊨ c : chan (lty_select Ss)) -∗
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
      ⊢ ∅ ⊨ chanbranch xs : chan (lty_branch Ss) ⊸
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
