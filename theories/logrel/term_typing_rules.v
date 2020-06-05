(** This file defines all of the semantic typing lemmas for term types. Most of
these lemmas are semantic versions of the syntactic typing judgments typically
found in a syntactic type system. *)
From stdpp Require Import pretty.
From iris.bi.lib Require Import core.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import metatheory.
From iris.heap_lang.lib Require Export spawn par assert.
From actris.logrel Require Export subtyping term_typing_judgment operators session_types.
From actris.logrel Require Import environments.
From actris.utils Require Import switch.
From actris.channel Require Import proofmode.

Section properties.
  Context `{heapG Σ}.
  Implicit Types A B : ltty Σ.
  Implicit Types S T : lsty Σ.
  Implicit Types Γ : gmap string (ltty Σ).

  (** Frame rule *)
  Lemma ltyped_frame Γ Γ' Γ1 Γ1' Γ2 e A :
    env_split Γ Γ1 Γ2 -∗
    env_split Γ' Γ1' Γ2 -∗
    (Γ1 ⊨ e : A ⫤ Γ1') -∗
    Γ ⊨ e : A ⫤ Γ'.
  Proof.
    iIntros "#Hsplit #Hsplit' #Htyped !>" (vs) "Henv".
    iDestruct ("Hsplit" with "Henv") as "[Henv1 Henv2]".
    iApply (wp_wand with "(Htyped Henv1)").
    iIntros (v) "[$ Henv1']".
    iApply "Hsplit'". iFrame "Henv1' Henv2".
  Qed.

  (** Variable properties *)
  Lemma ltyped_var Γ (x : string) A :
    Γ !! x = Some A → ⊢ Γ ⊨ x : A ⫤ <[x := (copy- A)%lty]> Γ.
  Proof.
    iIntros (HΓx) "!>"; iIntros (vs) "HΓ /=".
    iDestruct (env_ltyped_lookup with "HΓ") as (v Hv) "[HA HΓ]"; first done; rewrite Hv.
    iApply wp_value.
    iAssert (ltty_car (copy- A) v)%lty as "#HAm". { iApply coreP_intro. iApply "HA". }
    iFrame "HA".
    iDestruct (env_ltyped_insert _ _ x with "HAm HΓ") as "HΓ".
    rewrite /binder_insert insert_delete (insert_id _ _ _ Hv).
    iApply "HΓ".
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
  Proof. iIntros "!>" (vs) "HΓ /=". iApply wp_value. eauto. Qed.
  Lemma ltyped_bool Γ (b : bool) : ⊢ Γ ⊨ #b : lty_bool.
  Proof. iIntros "!>" (vs) "HΓ /=". iApply wp_value. eauto. Qed.
  Lemma ltyped_int Γ (i : Z) : ⊢ Γ ⊨ #i : lty_int.
  Proof. iIntros "!>" (vs) "HΓ /=". iApply wp_value. eauto. Qed.

  (** Operations *)
  Lemma ltyped_un_op Γ1 Γ2 op e A B :
    LTyUnOp op A B →
    (Γ1 ⊨ e : A ⫤ Γ2) -∗
    Γ1 ⊨ UnOp op e : B ⫤ Γ2.
  Proof.
    iIntros (Hop) "#He !>". iIntros (vs) "HΓ1"=> /=.
    wp_apply (wp_wand with "(He [HΓ1 //])"). iIntros (v1) "[HA HΓ2]".
    iDestruct (Hop with "HA") as (w Heval) "HB".
    wp_unop. iFrame.
  Qed.

  Lemma ltyped_bin_op Γ1 Γ2 Γ3 op e1 e2 A1 A2 B :
    LTyBinOp op A1 A2 B →
    (Γ1 ⊨ e2 : A2 ⫤ Γ2) -∗
    (Γ2 ⊨ e1 : A1 ⫤ Γ3) -∗
    Γ1 ⊨ BinOp op e1 e2 : B ⫤ Γ3.
  Proof.
    iIntros (Hop) "#He2 #He1 !>". iIntros (vs) "HΓ1"=> /=.
    wp_apply (wp_wand with "(He2 [HΓ1 //])"). iIntros (v2) "[HA2 HΓ2]".
    wp_apply (wp_wand with "(He1 [HΓ2 //])"). iIntros (v1) "[HA1 HΓ3]".
    iDestruct (Hop with "HA1 HA2") as (w Heval) "HB".
    wp_binop. iFrame.
  Qed.

  (** Conditionals *)
  Lemma ltyped_if Γ1 Γ2 Γ3 e1 e2 e3 A :
    (Γ1 ⊨ e1 : lty_bool ⫤ Γ2) -∗
    (Γ2 ⊨ e2 : A ⫤ Γ3) -∗
    (Γ2 ⊨ e3 : A ⫤ Γ3) -∗
    Γ1 ⊨ (if: e1 then e2 else e3) : A ⫤ Γ3.
  Proof.
    iIntros "#He1 #He2 #He3 !>" (v) "HΓ1".
    simpl.
    wp_apply (wp_wand with "(He1 [HΓ1 //])"). iIntros (b) "[Hbool HΓ2]".
    rewrite /lty_bool. iDestruct "Hbool" as ([]) "->".
    - wp_apply (wp_wand with "(He2 [HΓ2 //])"). iIntros (w) "[HA HΓ3]". iFrame.
    - wp_apply (wp_wand with "(He3 [HΓ2 //])"). iIntros (w) "[HA HΓ3]". iFrame.
  Qed.


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
    (<![x:=A1]!> Γ ⊨ e : A2 ⫤ Γ') -∗
    Γ ⊨ (λ: x, e) : A1 ⊸ A2 ⫤ ∅.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_pures. iSplitL; last by iApply env_ltyped_empty.
    iIntros (v) "HA1". wp_pures.
    iDestruct ("He" $!((binder_insert x v vs)) with "[HA1 HΓ]") as "He'".
    { iApply (env_ltyped_insert with "[HA1 //] HΓ"). }
    iDestruct (wp_wand _ _ _ _ (ltty_car A2) with "He' []") as "He'".
    { iIntros (w) "[$ _]". }
    destruct x as [|x]; rewrite /= -?subst_map_insert //.
  Qed.

  (* Typing rule for introducing copyable functions *)
  Lemma ltyped_rec Γ Γ' Γ'' f x e A1 A2 :
    env_copy Γ Γ' -∗
    (<![f:=A1 → A2]!> $ <![x:=A1]!> Γ' ⊨ e : A2 ⫤ Γ'') -∗
    Γ ⊨ (rec: f x := e) : A1 → A2 ⫤ ∅.
  Proof.
    iIntros "#Hcopy #He". iIntros (vs) "!> HΓ /=". iApply wp_fupd. wp_pures.
    iDestruct ("Hcopy" with "HΓ") as "HΓ".
    iMod (fupd_mask_mono with "HΓ") as "#HΓ"; first done.
    iModIntro. iSplitL; last by iApply env_ltyped_empty.
    iLöb as "IH".
    iIntros (v) "!> HA1". wp_pures. set (r := RecV f x _).
    iDestruct ("He" $! (<![f:=r]!> $ <![x:=v]!> vs) with "[HΓ HA1]") as "He'".
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

  Lemma ltyped_let Γ1 Γ2 Γ3 x e1 e2 A1 A2 :
    (Γ1 ⊨ e1 : A1 ⫤ Γ2) -∗ (<![x:=A1]!> Γ2 ⊨ e2 : A2 ⫤ Γ3) -∗
    Γ1 ⊨ (let: x:=e1 in e2) : A2 ⫤ binder_delete x Γ3.
  Proof.
    iIntros "#He1 #He2 !>". iIntros (vs) "HΓ1"=> /=.
    wp_apply (wp_wand with "(He1 HΓ1)").
    iIntros (v) "[HA1 HΓ2]".
    wp_pures.
    iDestruct (env_ltyped_insert _ _ x with "HA1 HΓ2") as "HΓ2".
    iDestruct ("He2" with "HΓ2") as "He2'".
    destruct x as [|x]; rewrite /= -?subst_map_insert //.
    wp_apply (wp_wand with "He2'").
    iIntros (w) "[HA2 HΓ3]".
    iFrame.
    iApply env_ltyped_delete=> //.
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

  Lemma ltyped_fst Γ A1 A2 (x : string) :
    Γ !! x = Some (A1 * A2)%lty →
    ⊢ Γ ⊨ Fst x : A1 ⫤ <[x := (copy- A1 * A2)%lty]> Γ.
  Proof.
    iIntros (Hx vs) "!> HΓ /=".
    iDestruct (env_ltyped_lookup with "HΓ") as (v Hv) "[HA HΓ]"; first done; rewrite Hv.
    iDestruct "HA" as (v1 v2 ->) "[HA1 HA2]".
    wp_pures.
    iAssert (ltty_car (copy- A1) v1)%lty as "#HA1m". { iApply coreP_intro. iApply "HA1". }
    iFrame "HA1".
    iAssert (ltty_car (copy- A1 * A2) (v1, v2))%lty with "[HA2]" as "HA".
    { iExists v1, v2. iSplit=>//. iFrame "HA1m HA2". }
    iDestruct (env_ltyped_insert _ _ x with "HA HΓ") as "HΓ".
    rewrite /binder_insert insert_delete (insert_id _ _ _ Hv).
    iFrame "HΓ".
  Qed.

  Lemma ltyped_snd Γ A1 A2 (x : string) :
    Γ !! x = Some (A1 * A2)%lty →
    ⊢ Γ ⊨ Snd x : A2 ⫤ <[x:=(A1 * copy- A2)%lty]> Γ.
  Proof.
    iIntros (Hx vs) "!> HΓ /=".
    iDestruct (env_ltyped_lookup with "HΓ") as (v Hv) "[HA HΓ]"; first done; rewrite Hv.
    iDestruct "HA" as (v1 v2 ->) "[HA1 HA2]".
    wp_pures.
    iAssert (ltty_car (copy- A2) v2)%lty as "#HA2m". { iApply coreP_intro. iApply "HA2". }
    iFrame "HA2".
    iAssert (ltty_car (A1 * copy- A2) (v1, v2))%lty with "[HA1]" as "HA".
    { iExists v1, v2. iSplit=>//. iFrame "HA2m HA1". }
    iDestruct (env_ltyped_insert _ _ x with "HA HΓ") as "HΓ".
    rewrite /binder_insert insert_delete (insert_id _ _ _ Hv).
    iFrame "HΓ".
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

  (* TODO: This probably requires there to be a rule that allows dropping arbitrary
  resources from the postcondition. Check if there is such a rule. *)
  Lemma ltyped_case Γ1 Γ2 Γ3 e1 e2 e3 A1 A2 B :
    (Γ1 ⊨ e1 : A1 + A2 ⫤ Γ2) -∗
    (Γ2 ⊨ e2 : A1 ⊸ B ⫤ Γ3) -∗
    (Γ2 ⊨ e3 : A2 ⊸ B ⫤ Γ3) -∗
    (Γ1 ⊨ Case e1 e2 e3 : B ⫤ Γ3).
  Proof.
    iIntros "#H1 #H2 #H3" (vs) "!> HΓ1 /=".
    wp_bind (subst_map vs e1).
    iSpecialize ("H1" with "HΓ1").
    iApply (wp_wand with "H1"). iIntros (s) "[Hs HΓ2]".
    iDestruct "Hs" as "[Hs|Hs]"; iDestruct "Hs" as (w ->) "HA"; wp_case.
    - wp_bind (subst_map vs e2).
      iApply (wp_wand with "(H2 HΓ2)"). iIntros (v) "[Hv HΓ3]".
      iApply (wp_wand with "(Hv HA)"). iIntros (v') "HB".
      iFrame "HΓ3 HB".
    - wp_bind (subst_map vs e3).
      iApply (wp_wand with "(H3 HΓ2)"). iIntros (v) "[Hv HΓ3]".
      iApply (wp_wand with "(Hv HA)"). iIntros (v') "HB".
      iFrame "HΓ3 HB".
  Qed.

  (** Universal Properties *)
  Lemma ltyped_tlam Γ e k (C : lty Σ k → ltty Σ) :
    (∀ M, Γ ⊨ e : C M ⫤ ∅) -∗ Γ ⊨ (λ: <>, e) : ∀ M, C M ⫤ ∅.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=". wp_pures.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros (M) "/=". wp_pures.
    iApply (wp_wand with "(He HΓ)"). iIntros (v) "[$ _]".
  Qed.

  Lemma ltyped_tapp Γ Γ2 e k (C : lty Σ k → ltty Σ) M :
    (Γ ⊨ e : ∀ M, C M ⫤ Γ2) -∗ Γ ⊨ e #() : C M ⫤ Γ2.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "[HB HΓ] /=".
    iApply (wp_wand with "HB [HΓ]"). by iIntros (v) "$".
  Qed.

  (** Existential properties *)
  Lemma ltyped_pack Γ e k (C : lty Σ k → ltty Σ) M :
    (Γ ⊨ e : C M) -∗ Γ ⊨ e : ∃ M, C M.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "[HB $]". by iExists M.
  Qed.

  Lemma ltyped_unpack {k} Γ1 Γ2 Γ3 x e1 e2 (C : lty Σ k → ltty Σ) B :
    (Γ1 ⊨ e1 : ∃ M, C M ⫤ Γ2) -∗
    (∀ Y, <![x:=C Y]!> Γ2 ⊨ e2 : B ⫤ Γ3) -∗
    Γ1 ⊨ (let: x := e1 in e2) : B ⫤ binder_delete x Γ3.
  Proof.
    iIntros "#He1 #He2 !>". iIntros (vs) "HΓ1"=> /=.
    wp_apply (wp_wand with "(He1 HΓ1)"); iIntros (v) "[HC HΓ2]".
    iDestruct "HC" as (X) "HX". wp_pures.
    iDestruct (env_ltyped_insert _ _ x with "HX HΓ2") as "HΓ2".
    iDestruct ("He2" with "HΓ2") as "He2'".
    destruct x as [|x]; rewrite /= -?subst_map_insert //.
    wp_apply (wp_wand with "He2'").
    iIntros (w) "[$ HΓ3]". by iApply env_ltyped_delete.
  Qed.

  (** Mutable Unique Reference properties *)
  Lemma ltyped_alloc Γ1 Γ2 e A :
    (Γ1 ⊨ e : A ⫤ Γ2) -∗
    (Γ1 ⊨ ref e : ref_uniq A ⫤ Γ2).
  Proof.
    iIntros "#He" (vs) "!> HΓ1 /=".
    wp_bind (subst_map vs e).
    iApply (wp_wand with "(He HΓ1)"). iIntros (v) "[Hv HΓ2]".
    wp_alloc l as "Hl".
    iFrame "HΓ2".
    iExists l, v; iSplit=>//. iFrame "Hv Hl".
  Qed.

  Lemma ltyped_free Γ1 Γ2 e A :
    (Γ1 ⊨ e : ref_uniq A ⫤ Γ2) -∗
    (Γ1 ⊨ Free e : () ⫤ Γ2).
  Proof.
    iIntros "#He" (vs) "!> HΓ1 /=".
    wp_bind (subst_map vs e).
    iApply (wp_wand with "(He HΓ1)"). iIntros (v) "[Hv HΓ2]".
    iDestruct "Hv" as (l w ->) "[Hl Hw]".
    wp_free. by iFrame "HΓ2".
  Qed.

  Lemma ltyped_load Γ (x : string) A :
    Γ !! x = Some (ref_uniq A)%lty →
    ⊢ Γ ⊨ ! x : A ⫤ <[x := (ref_uniq (copy- A))%lty]> Γ.
  Proof.
    iIntros (Hx vs) "!> HΓ".
    iDestruct (env_ltyped_lookup with "HΓ") as (v Hv) "[HA HΓ]"; first done.
    simpl. rewrite Hv.
    iDestruct "HA" as (l w ->) "[Hl Hw]".
    wp_load.
    iAssert (ltty_car (copy- A) w)%lty as "#HAm".
    { iApply coreP_intro. iApply "Hw". }
    iFrame "Hw".
    iAssert (ltty_car (ref_uniq (copy- A))%lty #l) with "[Hl]" as "HA".
    { iExists l, w. iSplit=>//. iFrame "Hl HAm". }
    iDestruct (env_ltyped_insert _ _ x with "HA HΓ") as "HΓ".
    rewrite /binder_insert insert_delete (insert_id _ _ _ Hv).
    iFrame "HΓ".
  Qed.

  Lemma ltyped_store Γ Γ' (x : string) e A B :
    Γ' !! x = Some (ref_uniq A)%lty →
    (Γ ⊨ e : B ⫤ Γ') -∗
    Γ ⊨ x <- e : () ⫤ <[x := (ref_uniq B)%lty]> Γ'.
  Proof.
    iIntros (Hx) "#He". iIntros (vs) "!> HΓ /=".
    wp_bind (subst_map vs e).
    iApply (wp_wand with "(He HΓ)"). iIntros (v) "[HB HΓ']".
    iDestruct (env_ltyped_lookup with "HΓ'") as (w Hw) "[HA HΓ']"; first done.
    rewrite Hw.
    iDestruct "HA" as (l v' ->) "[Hl HA]".
    wp_store. iSplitR; first done.
    iAssert (ltty_car (ref_uniq B)%lty #l) with "[Hl HB]" as "HB".
    { iExists l, v. iSplit=>//. iFrame "Hl HB". }
    iDestruct (env_ltyped_insert _ _ x with "HB HΓ'") as "HΓ'".
    rewrite /binder_insert insert_delete (insert_id _ _ _ Hw).
    iFrame "HΓ'".
  Qed.

  (** Mutable Shared Reference properties *)
  Lemma ltyped_upgrade_shared  Γ Γ' e A :
    (Γ ⊨ e : ref_uniq (copy A) ⫤ Γ') -∗
    Γ ⊨ e : ref_shr A ⫤ Γ'.
  Proof.
    iIntros "#He" (vs) "!> HΓ". iApply wp_fupd.
    iApply (wp_wand with "(He HΓ)"). iIntros (v) "[Hv HΓ']".
    iDestruct "Hv" as (l w ->) "[Hl HA]".
    iFrame "HΓ'". iExists l.
    iMod (inv_alloc (ref_shrN .@ l) _
      (∃ v : val, l ↦ v ∗ □ ltty_car A v) with "[Hl HA]") as "$"; last done.
    iExists w. iFrame "Hl HA".
  Qed.

  Lemma ltyped_load_shared Γ Γ' e A :
    (Γ ⊨ e : ref_shr A ⫤ Γ') -∗
    Γ ⊨ ! e : A ⫤ Γ'.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_bind (subst_map vs e).
    iApply (wp_wand with "(He HΓ)"). iIntros (v) "[Hv HΓ]".
    iDestruct "Hv" as (l ->) "#Hv".
    iInv (ref_shrN .@ l) as (v) "[>Hl #HA]" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hl HA]") as "_".
    { iExists v. iFrame "Hl HA". }
    by iIntros "!> {$HΓ}".
  Qed.

  Lemma ltyped_store_shared Γ1 Γ2 Γ3 e1 e2 A :
    (Γ1 ⊨ e2 : copy A ⫤ Γ2) -∗
    (Γ2 ⊨ e1 : ref_shr A ⫤ Γ3) -∗
    (Γ1 ⊨ e1 <- e2 : () ⫤ Γ3).
  Proof.
    iIntros "#H1 #H2" (vs) "!> HΓ1 /=".
    wp_bind (subst_map vs e2).
    iApply (wp_wand with "(H1 HΓ1)"). iIntros (v) "[Hv HΓ2]".
    wp_bind (subst_map vs e1).
    iApply (wp_wand with "(H2 HΓ2)"). iIntros (w) "[Hw HΓ3]".
    iDestruct "Hw" as (l ->) "#Hw".
    iInv (ref_shrN .@ l) as (?) "[>Hl HA]" "Hclose".
    wp_store.
    iMod ("Hclose" with "[Hl Hv]") as "_".
    { iExists v. iFrame "Hl Hv". }
    iModIntro. by iSplit.
  Qed.

  Lemma ltyped_fetch_and_add_shared Γ1 Γ2 Γ3 e1 e2 :
    (Γ1 ⊨ e2 : lty_int ⫤ Γ2) -∗
    (Γ2 ⊨ e1 : ref_shr lty_int ⫤ Γ3) -∗
    (Γ1 ⊨ FAA e1 e2 : lty_int ⫤ Γ3).
  Proof.
    iIntros "#H1 #H2" (vs) "!> HΓ1 /=".
    wp_bind (subst_map vs e2).
    iApply (wp_wand with "(H1 HΓ1)"). iIntros (v) "[Hv HΓ2]".
    wp_bind (subst_map vs e1).
    iApply (wp_wand with "(H2 HΓ2)"). iIntros (w) "[Hw HΓ3]".
    iDestruct "Hw" as (l ->) "#Hw".
    iInv (ref_shrN .@ l) as (w) "[Hl >Hn]" "Hclose".
    iDestruct "Hn" as %[k ->].
    iDestruct "Hv" as %[n ->].
    wp_faa.
    iMod ("Hclose" with "[Hl]") as %_.
    { iExists #(k + n). iFrame "Hl". by iExists (k + n)%Z. }
    iModIntro. iFrame "HΓ3". by iExists k.
  Qed.

  Section with_spawn.
    Context `{spawnG Σ}.

    (** Parallel composition properties *)
    Lemma ltyped_par Γ Γ' Γ1 Γ1' Γ2 Γ2' e1 e2 A B :
      env_split Γ Γ1 Γ2 -∗
      env_split Γ' Γ1' Γ2' -∗
      (Γ1 ⊨ e1 : A ⫤ Γ1') -∗
      (Γ2 ⊨ e2 : B ⫤ Γ2') -∗
      Γ ⊨ e1 ||| e2 : A * B ⫤ Γ'.
    Proof.
      iIntros "#Hsplit #Hsplit' #H1 #H2" (vs) "!> HΓ /=".
      iDestruct ("Hsplit" with "HΓ") as "[HΓ1 HΓ2]".
      wp_apply (wp_par with "[HΓ1] [HΓ2]").
      - iApply ("H1" with "HΓ1").
      - iApply ("H2" with "HΓ2").
      - iIntros (v1 v2) "[[HA HΓ1'] [HB HΓ2']]".
        iModIntro. iSplitL "HA HB".
        + iExists v1, v2. iSplit=>//. iFrame "HA HB".
        + iApply "Hsplit'". iFrame "HΓ1' HΓ2'".
    Qed.
  End with_spawn.

  (** Channel properties *)
  Section with_chan.
    Context `{chanG Σ}.

    Lemma ltyped_new_chan S :
      ⊢ ∅ ⊨ new_chan : () → (chan S * chan (lty_dual S)).
    Proof.
      iIntros (vs) "!> HΓ /=". iApply wp_value.
      iSplitL; last by iApply env_ltyped_empty.
      iIntros "!>" (u) ">->".
      iApply (new_chan_spec with "[//]"); iIntros (c1 c2) "!> [Hp1 Hp2]".
      iExists c1, c2. iSplit=>//. iFrame "Hp1 Hp2".
    Qed.

    Lemma ltyped_send Γ Γ' (x : string) e A S :
      Γ' !! x = Some (chan (<!!> TY A; S))%lty →
      (Γ ⊨ e : A ⫤ Γ') -∗
      Γ ⊨ send x e : () ⫤ <[x:=(chan S)%lty]> Γ'.
    Proof.
      iIntros (Hx) "#He !>". iIntros (vs) "HΓ"=> /=.
      wp_bind (subst_map vs e).
      iApply (wp_wand with "(He HΓ)"); iIntros (v) "[HA HΓ']".
      iDestruct (env_ltyped_lookup with "HΓ'") as (v' Heq) "[Hc HΓ']".
      { by apply Hx. }
      rewrite Heq.
      wp_send with "[HA //]".
      iSplitR; first done.
      iDestruct (env_ltyped_insert _ _ x (chan _) with "[Hc //] HΓ'")
        as "HΓ'"=> /=.
      by rewrite insert_delete (insert_id vs).
    Qed.

    Lemma iProto_le_lmsg_texist {kt : ktele Σ} (m : ltys Σ kt → iMsg Σ) :
      ⊢ (<?> (∃.. Xs : ltys Σ kt, m Xs)%lmsg) ⊑ (<? (Xs : ltys Σ kt)> m Xs).
    Proof.
      iInduction kt as [|k kt] "IH".
      { rewrite /lty_msg_texist /=. by iExists LTysO. }
      rewrite /lty_msg_texist /=. iIntros (X).
      iApply (iProto_le_trans with "IH"). iIntros (Xs). by iExists (LTysS _ _).
    Qed.

    Lemma ltyped_recv_texist {kt} Γ1 Γ2 (xc : string) (x : binder) (e : expr)
        (A : ltys Σ kt → ltty Σ) (S : ltys Σ kt → lsty Σ) (B : ltty Σ) :
      (∀ Ys,
        <![x:=A Ys]!> $ <[xc:=(chan (S Ys))%lty]> Γ1 ⊨ e : B ⫤ Γ2) -∗
      <[xc:=(chan (<??.. Xs> TY A Xs; S Xs))%lty]> Γ1 ⊨
        (let: x := recv xc in e) : B ⫤ binder_delete x Γ2.
    Proof.
      iIntros "#He !>". iIntros (vs) "HΓ /=".
      iDestruct (env_ltyped_lookup with "HΓ") as (c Hxc) "[Hc HΓ]".
      { by apply lookup_insert. }
      rewrite Hxc.
      iAssert (c ↣ <? (Xs : ltys Σ kt) (v : val)>
        MSG v {{ ▷ ltty_car (A Xs) v }}; lsty_car (S Xs)) with "[Hc]" as "Hc".
      { iApply (iProto_mapsto_le with "Hc"); iIntros "!>".
        iApply iProto_le_lmsg_texist. }
      wp_recv (Xs v) as "HA". wp_pures.
      rewrite -subst_map_binder_insert.
      wp_apply (wp_wand with "(He [-]) []").
      { iApply (env_ltyped_insert _ _ x with "HA").
        rewrite delete_insert_delete.
        iEval (rewrite -(insert_id vs xc c) // -(insert_delete Γ1)).
        by iApply (env_ltyped_insert _ _ xc with "[Hc] HΓ"). }
      iIntros (w) "[$ HΓ]". by destruct x; [|by iApply env_ltyped_delete].
    Qed.

    Lemma ltyped_recv Γ (x : string) A S :
      Γ !! x = Some (chan (<??> TY A; S))%lty →
      ⊢ Γ ⊨ recv x : A ⫤ <[x:=(chan S)%lty]> Γ.
    Proof.
      iIntros (Hx) "!>". iIntros (vs) "HΓ"=> /=.
      iDestruct (env_ltyped_lookup _ _ _ _ (Hx) with "HΓ") as (v' Heq) "[Hc HΓ]".
      rewrite Heq.
      wp_recv (v) as "HA". iFrame "HA".
      iDestruct (env_ltyped_insert _ _ x (chan _) _ with "[Hc //] HΓ") as "HΓ"=> /=.
      by rewrite insert_delete (insert_id vs).
    Qed.

    Definition select : val := λ: "c" "i", send "c" "i".
    Lemma ltyped_select Γ (x : string) (i : Z) (S : lsty Σ) Ss :
      Ss !! i = Some S →
      ⊢ <[x:=(chan (lty_select Ss))%lty]>Γ ⊨ select x #i : () ⫤
        <[x:=(chan S)%lty]>Γ.
    Proof.
      iIntros (Hin); iIntros "!>" (vs) "HΓ /=".
      iDestruct (env_ltyped_lookup with "HΓ") as (v' Heq) "[Hc HΓ]".
      { by apply lookup_insert. }
      rewrite Heq /select.
      wp_send with "[]".
      { eauto. }
      iSplitR; first done.
      iDestruct (env_ltyped_insert _ _ x (chan _) with "[Hc //] HΓ") as "HΓ' /=".
      rewrite insert_delete insert_insert (insert_id vs)=> //.
      by rewrite lookup_total_alt Hin.
    Qed.

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

    Definition branch (xs : list Z) : val := λ: "c",
      switch_lams "f" 0 (length xs) $
      let: "y" := recv "c" in
      switch_body "y" 0 xs (assert: #false) $ λ i, ("f" +:+ pretty i) "c".

    Lemma ltyped_branch Ss A xs :
      (∀ x, x ∈ xs ↔ is_Some (Ss !! x)) →
      ⊢ ∅ ⊨ branch xs : chan (lty_branch Ss) ⊸
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
