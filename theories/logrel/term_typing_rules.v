(** This file defines all of the semantic typing lemmas for term types. Most of
these lemmas are semantic versions of the syntactic typing judgments typically
found in a syntactic type system. *)
From stdpp Require Import pretty.
From iris.bi.lib Require Import core.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import metatheory.
From iris.heap_lang.lib Require Export spawn par assert.
From actris.logrel Require Export subtyping_rules term_typing_judgment operators.
From actris.utils Require Import switch.
From actris.channel Require Import proofmode.

Section properties.
  Context `{heapG Σ}.
  Implicit Types A B : ltty Σ.
  Implicit Types S T : lsty Σ.
  Implicit Types Γ : env Σ.

  (** Frame rule *)
  Lemma ltyped_frame Γ Γ1 Γ2 e A :
    (Γ1 ⊨ e : A ⫤ Γ2) -∗
    (Γ1 ++ Γ ⊨ e : A ⫤ Γ2 ++ Γ).
  Proof.
    iIntros "#He !>" (vs) "HΓ".
    iDestruct (env_ltyped_app with "HΓ") as "[HΓ1 HΓ]".
    iApply (wp_wand with "(He HΓ1)").
    iIntros (v) "[$ HΓ2]". by iApply (env_ltyped_app with "[$]").
  Qed.

  (** Variable properties *)
  Lemma ltyped_var Γ (x : string) A :
    env_filter_eq x Γ = [EnvItem x A] →
    ⊢ Γ ⊨ x : A ⫤ env_cons x (copy- A) Γ.
  Proof.
    iIntros (HΓx%env_filter_eq_perm') "!>"; iIntros (vs) "HΓ /=".
    rewrite {1}HΓx /=.
    iDestruct (env_ltyped_cons with "HΓ") as (v Hvs) "[HA HΓ]". rewrite Hvs.
    iAssert (ltty_car (copy- A) v)%lty as "#HAm"; [by iApply coreP_intro|].
    iApply wp_value. iFrame "HA". iApply env_ltyped_cons. eauto with iFrame.
  Qed.

  (** Subtyping *)
  Theorem ltyped_subsumption Γ1 Γ2 Γ1' Γ2' e τ τ' :
    env_le Γ1 Γ1' -∗ τ' <: τ -∗ env_le Γ2' Γ2 -∗
    (Γ1' ⊨ e : τ' ⫤ Γ2') -∗ (Γ1 ⊨ e : τ ⫤ Γ2).
  Proof.
    iIntros "#HleΓ1 #Hle #HleΓ2 #He" (vs) "!> HΓ1".
    iApply (wp_wand with "(He (HleΓ1 HΓ1))").
    iIntros (v) "[Hτ HΓ2]". iSplitL "Hτ"; [by iApply "Hle"|by iApply "HleΓ2"].
  Qed.
  Lemma ltyped_post_nil Γ1 Γ2 e τ :
    (Γ1 ⊨ e : τ ⫤ Γ2) -∗ (Γ1 ⊨ e : τ ⫤ []).
  Proof.
    iApply ltyped_subsumption;
      [iApply env_le_refl|iApply lty_le_refl|iApply env_le_nil].
  Qed.

  (** Basic properties *)
  Lemma ltyped_unit Γ : ⊢ Γ ⊨ #() : ().
  Proof. iIntros "!>" (vs) "$ /=". iApply wp_value. eauto. Qed.
  Lemma ltyped_bool Γ (b : bool) : ⊢ Γ ⊨ #b : lty_bool.
  Proof. iIntros "!>" (vs) "$ /=". iApply wp_value. eauto. Qed.
  Lemma ltyped_int Γ (i : Z) : ⊢ Γ ⊨ #i : lty_int.
  Proof. iIntros "!>" (vs) "$ /=". iApply wp_value. eauto. Qed.

  (** Operations *)
  Lemma ltyped_un_op Γ1 Γ2 op e A B :
    LTyUnOp op A B →
    (Γ1 ⊨ e : A ⫤ Γ2) -∗
    Γ1 ⊨ UnOp op e : B ⫤ Γ2.
  Proof.
    iIntros (Hop) "#He !>". iIntros (vs) "HΓ1 /=".
    wp_apply (wp_wand with "(He [HΓ1 //])"). iIntros (v1) "[HA $]".
    iDestruct (Hop with "HA") as (w ?) "HB". by wp_unop.
  Qed.

  Lemma ltyped_bin_op Γ1 Γ2 Γ3 op e1 e2 A1 A2 B :
    LTyBinOp op A1 A2 B →
    (Γ1 ⊨ e2 : A2 ⫤ Γ2) -∗
    (Γ2 ⊨ e1 : A1 ⫤ Γ3) -∗
    Γ1 ⊨ BinOp op e1 e2 : B ⫤ Γ3.
  Proof.
    iIntros (Hop) "#He2 #He1 !>". iIntros (vs) "HΓ1 /=".
    wp_apply (wp_wand with "(He2 [HΓ1 //])"). iIntros (v2) "[HA2 HΓ2]".
    wp_apply (wp_wand with "(He1 [HΓ2 //])"). iIntros (v1) "[HA1 $]".
    iDestruct (Hop with "HA1 HA2") as (w ?) "HB". by wp_binop.
  Qed.

  (** Conditionals *)
  Lemma ltyped_if Γ1 Γ2 Γ3 e1 e2 e3 A :
    (Γ1 ⊨ e1 : lty_bool ⫤ Γ2) -∗
    (Γ2 ⊨ e2 : A ⫤ Γ3) -∗
    (Γ2 ⊨ e3 : A ⫤ Γ3) -∗
    Γ1 ⊨ (if: e1 then e2 else e3) : A ⫤ Γ3.
  Proof.
    iIntros "#He1 #He2 #He3 !>" (v) "HΓ1 /=".
    wp_apply (wp_wand with "(He1 [HΓ1 //])"). iIntros (b) "[Hbool HΓ2]".
    rewrite /lty_bool. iDestruct "Hbool" as ([]) "->".
    - wp_apply (wp_wand with "(He2 [HΓ2 //])"). iIntros (w) "[$$]".
    - wp_apply (wp_wand with "(He3 [HΓ2 //])"). iIntros (w) "[$$]".
  Qed.

  (** Arrow properties *)
  Lemma ltyped_app Γ1 Γ2 Γ3 e1 e2 A1 A2 :
    (Γ1 ⊨ e2 : A1 ⫤ Γ2) -∗ (Γ2 ⊨ e1 : A1 ⊸ A2 ⫤ Γ3) -∗
    Γ1 ⊨ e1 e2 : A2 ⫤ Γ3.
  Proof.
    iIntros "#H2 #H1". iIntros (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(H2 [HΓ //])"). iIntros (v) "[HA1 HΓ]".
    wp_apply (wp_wand with "(H1 [HΓ //])"). iIntros (f) "[Hf $]".
    iApply ("Hf" $! v with "HA1").
  Qed.

  Lemma ltyped_lam Γ1 Γ2 x e A1 A2 :
    (env_cons x A1 Γ1 ⊨ e : A2 ⫤ []) -∗
    Γ1 ++ Γ2 ⊨ (λ: x, e) : A1 ⊸ A2 ⫤ Γ2.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=". wp_pures.
    iDestruct (env_ltyped_app with "HΓ") as "[HΓ1 $]".
    iIntros (v) "HA1". wp_pures.
    iDestruct ("He" $! (binder_insert x v vs) with "[HA1 HΓ1]") as "He'".
    { by iApply (env_ltyped_insert' with "HA1"). }
    rewrite subst_map_binder_insert.
    iApply (wp_wand with "He'"). by iIntros (w) "[$ _]".
  Qed.

  (* Typing rule for introducing copyable functions *)
  Definition env_copy_minus : env Σ → env Σ :=
    fmap (λ xA, EnvItem (env_item_name xA) (lty_copy_minus  (env_item_type xA))).

  Lemma ltyped_rec Γ1 Γ2 f x e A1 A2 :
    (env_cons f (A1 → A2) (env_cons x A1 (env_copy_minus Γ1)) ⊨ e : A2 ⫤ []) -∗
    Γ1 ++ Γ2 ⊨ (rec: f x := e) : A1 → A2 ⫤ Γ2.
  Proof.
    iIntros "#He". iIntros (vs) "!> HΓ /=". wp_pures.
    iDestruct (env_ltyped_app with "HΓ") as "[HΓ1 $]".
    iAssert (<pers> env_ltyped vs (env_copy_minus Γ1))%I as "{HΓ1} #HΓ1".
    { iClear "He". rewrite /env_copy_minus big_sepL_persistently big_sepL_fmap.
      iApply (big_sepL_impl with "HΓ1"). iIntros "!>" (k [y B] _) "/=".
      iDestruct 1 as (v ?) "HB". iExists v. iSplit; [by auto|].
      by iDestruct (coreP_intro with "HB") as "{HB} #HB". }
    iLöb as "IH".
    iIntros (v) "!> HA1". wp_pures. set (r := RecV f x _).
    iDestruct ("He" $! (binder_insert f r (binder_insert x v vs))
      with "[HΓ1 HA1]") as "He'".
    { iApply (env_ltyped_insert' with "IH").
      by iApply (env_ltyped_insert' with "HA1"). }
    rewrite !subst_map_binder_insert_2.
    iApply (wp_wand with "He'"). iIntros (w) "[$ _]".
  Qed.

  Lemma ltyped_let Γ1 Γ2 Γ3 x e1 e2 A1 A2 :
    (Γ1 ⊨ e1 : A1 ⫤ Γ2) -∗
    (env_cons x A1 Γ2 ⊨ e2 : A2 ⫤ Γ3) -∗
    Γ1 ⊨ (let: x:=e1 in e2) : A2 ⫤ env_filter_eq x Γ2 ++ env_filter_ne x Γ3.
  Proof.
    iIntros "#He1 #He2 !>". iIntros (vs) "HΓ1 /=".
    wp_apply (wp_wand with "(He1 HΓ1)"); iIntros (v) "[HA1 HΓ2]". wp_pures.
    rewrite {3}(env_filter_eq_perm Γ2 x).
    iDestruct (env_ltyped_app with "HΓ2") as "[HΓ2eq HΓ2neq]".
    iDestruct ("He2" $! (binder_insert x v vs) with "[HA1 HΓ2neq]") as "He'".
    { by iApply (env_ltyped_insert with "HA1"). }
    rewrite subst_map_binder_insert. iApply (wp_wand with "He'").
    iIntros (w) "[$ HΓ3]".
    iApply env_ltyped_app. iFrame "HΓ2eq". by iApply env_ltyped_delete.
  Qed.

  Lemma ltyped_seq Γ1 Γ2 Γ3 e1 e2 A B :
    (Γ1 ⊨ e1 : A ⫤ Γ2) -∗
    (Γ2 ⊨ e2 : B ⫤ Γ3) -∗
    Γ1 ⊨ (e1 ;; e2) : B ⫤ Γ3.
  Proof.
    iIntros "#He1 #He2 !>". iIntros (vs) "HΓ1 /=".
    wp_apply (wp_wand with "(He1 HΓ1)"); iIntros (v) "[_ HΓ2]". wp_pures.
    wp_apply (wp_wand with "(He2 HΓ2)"); iIntros (w) "[HB HΓ3]". wp_pures.
    iFrame "HB HΓ3".
  Qed.

  (** Product properties  *)
  Lemma ltyped_pair Γ1 Γ2 Γ3 e1 e2 A1 A2 :
    (Γ1 ⊨ e2 : A2 ⫤ Γ2) -∗ (Γ2 ⊨ e1 : A1 ⫤ Γ3) -∗
    Γ1 ⊨ (e1,e2) : A1 * A2 ⫤ Γ3.
  Proof.
    iIntros "#H2 #H1". iIntros (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(H2 [HΓ //])"); iIntros (w2) "[HA2 HΓ]".
    wp_apply (wp_wand with "(H1 [HΓ //])"); iIntros (w1) "[HA1 HΓ]".
    wp_pures. iFrame "HΓ". iExists w1, w2. by iFrame.
  Qed.

  Lemma ltyped_fst Γ A1 A2 (x : string) :
    env_filter_eq x Γ = [EnvItem x (A1 * A2)] →
    ⊢ Γ ⊨ Fst x : A1 ⫤ env_cons x (copy- A1 * A2) Γ.
  Proof.
    iIntros (HΓx%env_filter_eq_perm' vs) "!> HΓ /=". rewrite {1}HΓx /=.
    iDestruct (env_ltyped_cons with "HΓ") as (v Hvs) "[HA HΓ]"; rewrite Hvs.
    iDestruct "HA" as (v1 v2 ->) "[HA1 HA2]". wp_pures.
    iAssert (ltty_car (copy- A1) v1)%lty as "#HA1m"; [by iApply coreP_intro|].
    iFrame "HA1". iApply env_ltyped_cons. iExists _; iSplit; [done|]; iFrame "HΓ".
    iExists v1, v2. eauto with iFrame.
  Qed.

  Lemma ltyped_snd Γ A1 A2 (x : string) :
    env_filter_eq x Γ = [EnvItem x (A1 * A2)] →
    ⊢ Γ ⊨ Snd x : A2 ⫤ env_cons x (A1 * copy- A2) Γ.
  Proof.
    iIntros (HΓx%env_filter_eq_perm' vs) "!> HΓ /=". rewrite {1}HΓx /=.
    iDestruct (env_ltyped_cons with "HΓ") as (v Hvs) "[HA HΓ]"; rewrite Hvs.
    iDestruct "HA" as (v1 v2 ->) "[HA1 HA2]". wp_pures.
    iAssert (ltty_car (copy- A2) v2)%lty as "#HA2m"; [by iApply coreP_intro|].
    iFrame "HA2". iApply env_ltyped_cons. iExists _; iSplit; [done|]; iFrame "HΓ".
    iExists v1, v2. eauto with iFrame.
  Qed.

  (** Sum Properties *)
  Lemma ltyped_injl Γ1 Γ2 e A1 A2 :
    (Γ1 ⊨ e : A1 ⫤ Γ2) -∗ Γ1 ⊨ InjL e : A1 + A2 ⫤ Γ2.
  Proof.
    iIntros "#HA" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(HA [HΓ //])").
    iIntros (v) "[HA' $]". wp_pures.
    iLeft. iExists v. auto.
  Qed.

  Lemma ltyped_injr Γ1 Γ2 e A1 A2 :
    (Γ1 ⊨ e : A2 ⫤ Γ2) -∗ Γ1 ⊨ InjR e : A1 + A2 ⫤ Γ2.
  Proof.
    iIntros "#HA" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(HA [HΓ //])").
    iIntros (v) "[HA' $]". wp_pures.
    iRight. iExists v. auto.
  Qed.

  Lemma ltyped_case Γ1 Γ2 Γ3 e1 e2 e3 A1 A2 B :
    (Γ1 ⊨ e1 : A1 + A2 ⫤ Γ2) -∗
    (Γ2 ⊨ e2 : A1 ⊸ B ⫤ Γ3) -∗
    (Γ2 ⊨ e3 : A2 ⊸ B ⫤ Γ3) -∗
    (Γ1 ⊨ Case e1 e2 e3 : B ⫤ Γ3).
  Proof.
    iIntros "#H1 #H2 #H3" (vs) "!> HΓ1 /=".
    wp_apply (wp_wand with "(H1 HΓ1)"). iIntros (s) "[[Hs|Hs] HΓ2]";
      iDestruct "Hs" as (w ->) "HA"; wp_case.
    - wp_apply (wp_wand with "(H2 HΓ2)"). iIntros (v) "[Hv $]".
      iApply (wp_wand with "(Hv HA)"). auto.
    - wp_apply (wp_wand with "(H3 HΓ2)"). iIntros (v) "[Hv $]".
      iApply (wp_wand with "(Hv HA)"). auto.
  Qed.

  (** Universal Properties *)
  Lemma ltyped_tlam Γ1 Γ2 Γ' e k (C : lty Σ k → ltty Σ) :
    (∀ M, Γ1 ⊨ e : C M ⫤ []) -∗
    Γ1 ++ Γ2 ⊨ (λ: <>, e) : ∀ M, C M ⫤ Γ2.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=". wp_pures.
    iDestruct (env_ltyped_app with "HΓ") as "[HΓ1 $]".
    iIntros (M) "/=". wp_pures.
    iApply (wp_wand with "(He HΓ1)"). iIntros (v) "[$ _]".
  Qed.

  Lemma ltyped_tapp Γ Γ2 e k (C : lty Σ k → ltty Σ) M :
    (Γ ⊨ e : ∀ M, C M ⫤ Γ2) -∗ Γ ⊨ e #() : C M ⫤ Γ2.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "[HB HΓ] /=".
    iApply (wp_wand with "HB [HΓ]"). by iIntros (v) "$".
  Qed.

  (** Existential properties *)
  Lemma ltyped_pack Γ1 Γ2 e k (C : lty Σ k → ltty Σ) M :
    (Γ1 ⊨ e : C M ⫤ Γ2) -∗ Γ1 ⊨ e : ∃ M, C M ⫤ Γ2.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "[HB $]". by iExists M.
  Qed.

  Lemma ltyped_unpack {k} Γ1 Γ2 Γ3 x e1 e2 (C : lty Σ k → ltty Σ) B :
    (Γ1 ⊨ e1 : ∃ M, C M ⫤ Γ2) -∗
    (∀ Y, env_cons x (C Y) Γ2 ⊨ e2 : B ⫤ Γ3) -∗
    Γ1 ⊨ (let: x := e1 in e2) : B ⫤ env_filter_eq x Γ2 ++ env_filter_ne x Γ3.
  Proof.
    iIntros "#He1 #He2 !>". iIntros (vs) "HΓ1 /=".
    wp_apply (wp_wand with "(He1 HΓ1)"); iIntros (v) "[HC HΓ2]".
    iDestruct "HC" as (X) "HX". wp_pures.
    rewrite {3}(env_filter_eq_perm Γ2 x).
    iDestruct (env_ltyped_app with "HΓ2") as "[HΓ2eq HΓ2neq]".
    iDestruct ("He2" $! X (binder_insert x v vs) with "[HX HΓ2neq]") as "He'".
    { by iApply (env_ltyped_insert with "HX"). }
    rewrite subst_map_binder_insert. iApply (wp_wand with "He'").
    iIntros (w) "[$ HΓ3]". iApply env_ltyped_app.
    iFrame "HΓ2eq". by iApply env_ltyped_delete.
  Qed.

  (** Mutable Unique Reference properties *)
  Lemma ltyped_alloc Γ1 Γ2 e A :
    (Γ1 ⊨ e : A ⫤ Γ2) -∗
    (Γ1 ⊨ ref e : ref_uniq A ⫤ Γ2).
  Proof.
    iIntros "#He" (vs) "!> HΓ1 /=".
    wp_apply (wp_wand with "(He HΓ1)"). iIntros (v) "[Hv $]".
    wp_alloc l as "Hl". iExists l, v; eauto with iFrame.
  Qed.

  Lemma ltyped_free Γ1 Γ2 e A :
    (Γ1 ⊨ e : ref_uniq A ⫤ Γ2) -∗
    (Γ1 ⊨ Free e : () ⫤ Γ2).
  Proof.
    iIntros "#He" (vs) "!> HΓ1 /=".
    wp_apply (wp_wand with "(He HΓ1)"). iIntros (v) "[Hv $]".
    iDestruct "Hv" as (l w ->) "[Hl Hw]". by wp_free.
  Qed.

  Lemma ltyped_load Γ (x : string) A :
    env_filter_eq x Γ = [EnvItem x (ref_uniq A)] →
    ⊢ Γ ⊨ ! x : A ⫤ env_cons x (ref_uniq (copy- A)) Γ.
  Proof.
    iIntros (HΓx%env_filter_eq_perm' vs) "!> HΓ /=". rewrite {1}HΓx /=.
    iDestruct (env_ltyped_cons with "HΓ") as (v Hvs) "[HA HΓ]"; rewrite Hvs.
    iDestruct "HA" as (l w ->) "[? HA]". wp_load.
    iAssert (ltty_car (copy- A) w)%lty as "#HAm"; [by iApply coreP_intro|].
    iFrame "HA". iApply env_ltyped_cons. iExists _; iSplit; [done|]; iFrame "HΓ".
    iExists l, w. eauto with iFrame.
  Qed.

  Lemma ltyped_store Γ Γ' (x : string) e A B :
    env_filter_eq x Γ' = [EnvItem x (ref_uniq A)] →
    (Γ ⊨ e : B ⫤ Γ') -∗
    Γ ⊨ x <- e : () ⫤ env_cons x (ref_uniq B) Γ'.
  Proof.
    iIntros (HΓx%env_filter_eq_perm') "#He"; iIntros (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He HΓ)"). iIntros (v) "[HB HΓ']".
    rewrite {2}HΓx /=.
    iDestruct (env_ltyped_cons with "HΓ'") as (vl Hvs) "[HA HΓ']"; rewrite Hvs.
    iDestruct "HA" as (l w ->) "[? HA]". wp_store. iSplit; [done|].
    iApply env_ltyped_cons. iExists _; iSplit; [done|]; iFrame "HΓ'".
    iExists l, v. eauto with iFrame.
  Qed.

  (** Mutable Shared Reference properties *)
  Lemma ltyped_upgrade_shared  Γ Γ' e A :
    (Γ ⊨ e : ref_uniq (copy A) ⫤ Γ') -∗
    Γ ⊨ e : ref_shr A ⫤ Γ'.
  Proof.
    iIntros "#He" (vs) "!> HΓ". iApply wp_fupd.
    iApply (wp_wand with "(He HΓ)"). iIntros (v) "[Hv $]".
    iDestruct "Hv" as (l w ->) "[Hl HA]". iExists l.
    iMod (inv_alloc (ref_shrN .@ l) _
      (∃ v : val, l ↦ v ∗ □ ltty_car A v) with "[Hl HA]") as "$"; last done.
    iExists w. iFrame "Hl HA".
  Qed.

  Lemma ltyped_load_shared Γ Γ' e A :
    (Γ ⊨ e : ref_shr A ⫤ Γ') -∗
    Γ ⊨ ! e : A ⫤ Γ'.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(He HΓ)"). iIntros (v) "[Hv $]".
    iDestruct "Hv" as (l ->) "#Hv".
    iInv (ref_shrN .@ l) as (v) "[>Hl #HA]" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hl HA]") as "_"; last done.
    iExists v. iFrame "Hl HA".
  Qed.

  Lemma ltyped_store_shared Γ1 Γ2 Γ3 e1 e2 A :
    (Γ1 ⊨ e2 : copy A ⫤ Γ2) -∗
    (Γ2 ⊨ e1 : ref_shr A ⫤ Γ3) -∗
    (Γ1 ⊨ e1 <- e2 : () ⫤ Γ3).
  Proof.
    iIntros "#H1 #H2" (vs) "!> HΓ1 /=".
    wp_apply (wp_wand with "(H1 HΓ1)"). iIntros (v) "[Hv HΓ2]".
    wp_bind (subst_map vs e1).
    iApply (wp_wand with "(H2 HΓ2)"). iIntros (w) "[Hw $]".
    iDestruct "Hw" as (l ->) "#Hw".
    iInv (ref_shrN .@ l) as (?) "[>Hl HA]" "Hclose".
    wp_store.
    iMod ("Hclose" with "[Hl Hv]") as "_"; eauto.
  Qed.

  Lemma ltyped_fetch_and_add_shared Γ1 Γ2 Γ3 e1 e2 :
    (Γ1 ⊨ e2 : lty_int ⫤ Γ2) -∗
    (Γ2 ⊨ e1 : ref_shr lty_int ⫤ Γ3) -∗
    (Γ1 ⊨ FAA e1 e2 : lty_int ⫤ Γ3).
  Proof.
    iIntros "#H1 #H2" (vs) "!> HΓ1 /=".
    wp_apply (wp_wand with "(H1 HΓ1)"). iIntros (v) "[Hv HΓ2]".
    wp_apply (wp_wand with "(H2 HΓ2)"). iIntros (w) "[Hw $]".
    iDestruct "Hw" as (l ->) "#Hw".
    iInv (ref_shrN .@ l) as (w) "[Hl >Hn]" "Hclose".
    iDestruct "Hn" as %[k ->].
    iDestruct "Hv" as %[n ->].
    wp_faa.
    iMod ("Hclose" with "[Hl]") as %_.
    { iExists #(k + n). iFrame "Hl". by iExists (k + n)%Z. }
    by iExists k.
  Qed.

  (** Parallel composition properties *)
  Lemma ltyped_par `{spawnG Σ} Γ1 Γ1' Γ2 Γ2' e1 e2 A B :
    (Γ1 ⊨ e1 : A ⫤ Γ1') -∗
    (Γ2 ⊨ e2 : B ⫤ Γ2') -∗
    Γ1 ++ Γ2 ⊨ e1 ||| e2 : A * B ⫤ Γ1' ++ Γ2'.
  Proof.
    iIntros "#He1 #He2 !>" (vs) "HΓ /=".
    iDestruct (env_ltyped_app with "HΓ") as "[HΓ1 HΓ2]".
    wp_apply (wp_par with "(He1 HΓ1) (He2 HΓ2)").
    iIntros (v1 v2) "[[HA HΓ1'] [HB HΓ2']] !>". iSplitL "HA HB".
    + iExists v1, v2. by iFrame.
    + iApply env_ltyped_app. by iFrame.
  Qed.

  (** Channel properties *)
  Section with_chan.
    Context `{chanG Σ}.

    Lemma ltyped_new_chan Γ S :
      ⊢ Γ ⊨ new_chan : () ⊸ (chan S * chan (lty_dual S)) ⫤ Γ.
    Proof.
      iIntros (vs) "!> HΓ /=". iApply wp_value. iFrame "HΓ".
      iIntros (u) ">->".
      iApply (new_chan_spec with "[//]"); iIntros (c1 c2) "!> [Hp1 Hp2]".
      iExists c1, c2. by iFrame "Hp1 Hp2".
    Qed.

    Lemma ltyped_send Γ Γ' (x : string) e A S :
      env_filter_eq x Γ' = [EnvItem x (chan (<!!> TY A; S))] →
      (Γ ⊨ e : A ⫤ Γ') -∗
      Γ ⊨ send x e : () ⫤ env_cons x (chan S) Γ'.
    Proof.
      iIntros (HΓx%env_filter_eq_perm') "#He !>". iIntros (vs) "HΓ /=".
      wp_apply (wp_wand with "(He HΓ)"); iIntros (v) "[HA HΓ']".
      rewrite {2}HΓx /=.
      iDestruct (env_ltyped_cons with "HΓ'") as (c Hvs) "[Hc HΓ']". rewrite Hvs.
      wp_send with "[HA //]". iSplitR; [done|].
      iDestruct (env_ltyped_insert _ _ x (chan _) with "[Hc //] HΓ'") as "HΓ' /=".
      by rewrite  (insert_id vs).
   Qed.

    Lemma iProto_le_lmsg_texist {kt : ktele Σ} (m : ltys Σ kt → iMsg Σ) :
      ⊢ (<?> (∃.. Xs : ltys Σ kt, m Xs)%lmsg) ⊑ (<? (Xs : ltys Σ kt)> m Xs).
    Proof.
      iInduction kt as [|k kt] "IH".
      { rewrite /lty_msg_texist /=. by iExists LTysO. }
      rewrite /lty_msg_texist /=. iIntros (X).
      iApply (iProto_le_trans with "IH"). iIntros (Xs). by iExists (LTysS _ _).
    Qed.

    Lemma ltyped_recv_texist {kt} Γ1 Γ2 M x (xc : string) (e : expr)
        (A : kt -k> ltty Σ) (S : kt -k> lsty Σ) (B : ltty Σ) :
      env_filter_eq xc Γ1 = [EnvItem xc (chan (<??> M))] →
      LtyMsgTele M A S →
      (∀ Ys,
        env_cons x (ktele_app A Ys) (env_cons xc (chan (ktele_app S Ys)) Γ1) ⊨ e : B ⫤ Γ2) -∗
      Γ1 ⊨ (let: x := recv xc in e) : B ⫤
            env_filter_eq x (env_filter_ne xc Γ1) ++ env_filter_ne x Γ2.
    Proof.
      rewrite /LtyMsgTele.
      iIntros (HΓxc%env_filter_eq_perm' HM) "#He !>". iIntros (vs) "HΓ1 /=".
      rewrite {2}HΓxc /=.
      iDestruct (env_ltyped_cons with "HΓ1") as (c Hvs) "[Hc HΓ1]". rewrite Hvs.
      rewrite {2}(env_filter_eq_perm (env_filter_ne xc Γ1) x).
      iDestruct (env_ltyped_app with "HΓ1") as "[HΓ1eq HΓ1neq]".
      iAssert (c ↣ <? (Xs : ltys Σ kt) (v : val)>
        MSG v {{ ltty_car (ktele_app A Xs) v }};
          lsty_car (ktele_app S Xs)) with "[Hc]" as "Hc".
      { iApply (iProto_mapsto_le with "Hc"); iIntros "!>". rewrite HM.
        iApply iProto_le_lmsg_texist. }
      wp_recv (Xs v) as "HA". wp_pures. rewrite -subst_map_binder_insert.
      wp_apply (wp_wand with "(He [- HΓ1eq])").
      { iApply (env_ltyped_insert _ _ x with "HA").
        destruct (decide (x = xc)) as [->|].
        - by rewrite env_filter_ne_cons.
        - rewrite env_filter_ne_cons_ne //.
          iApply env_ltyped_cons. eauto with iFrame. }
      iIntros (w) "[$ HΓ]".
      iApply env_ltyped_app. iFrame "HΓ1eq". by iApply env_ltyped_delete.
    Qed.

    Lemma ltyped_recv Γ (x : string) A S :
      env_filter_eq x Γ = [EnvItem x (chan (<??> TY A; S))] →
      ⊢ Γ ⊨ recv x : A ⫤ env_cons x (chan S) Γ.
    Proof.
      iIntros (HΓx%env_filter_eq_perm') "!>". iIntros (vs) "HΓ /=".
      rewrite {1}HΓx /=.
      iDestruct (env_ltyped_cons with "HΓ") as (c Hvs) "[Hc HΓ]". rewrite Hvs.
      wp_recv (v) as "HA". iFrame "HA". iApply env_ltyped_cons; eauto with iFrame.
    Qed.

    Definition select : val := λ: "c" "i", send "c" "i".

    Lemma ltyped_select Γ (x : string) (i : Z) (S : lsty Σ) Ss :
      Ss !! i = Some S →
      env_filter_eq x Γ = [EnvItem x (chan (lty_select Ss))] →
      ⊢ Γ ⊨ select x #i : () ⫤ env_cons x (chan S) Γ.
    Proof.
      iIntros (Hin HΓx%env_filter_eq_perm'); iIntros "!>" (vs) "HΓ /=".
      rewrite {1}HΓx /=.
      iDestruct (env_ltyped_cons with "HΓ") as (c Hvs) "[Hc HΓ]". rewrite Hvs.
      rewrite /select. wp_send with "[]"; [by eauto|]. iSplit; [done|].
      iDestruct (env_ltyped_insert _ _ x (chan _) with "[Hc //] HΓ") as "HΓ' /=".
      by rewrite insert_id // lookup_total_alt Hin.
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

    Lemma ltyped_branch Γ Ss A xs :
      (∀ x, x ∈ xs ↔ is_Some (Ss !! x)) →
      ⊢ Γ ⊨ branch xs : chan (lty_branch Ss) ⊸
        lty_arr_list ((λ x, (chan (Ss !!! x) ⊸ A)%lty) <$> xs) A ⫤ Γ.
    Proof.
      iIntros (Hdom) "!>". iIntros (vs) "$". iApply wp_value.
      iIntros (c) "Hc". wp_lam.
      rewrite -subst_map_singleton.
      iApply lty_arr_list_spec; [by rewrite fmap_length|].
      iIntros (ws) "H".
      rewrite big_sepL2_fmap_l.
      iDestruct (big_sepL2_length with "H") as %Heq.
      rewrite -insert_union_singleton_r; last by apply lookup_map_string_seq_None.
      rewrite /= lookup_insert.
      wp_recv (x) as "HPsx". iDestruct "HPsx" as %HPs_Some.
      wp_pures. rewrite -subst_map_insert.
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
