(** This file contains the definitions of Actris's tactics for symbolic
execution of message-passing programs. The API of these tactics is documented
in the [README.md] file. The implementation follows the same pattern for the
implementation of these tactics that is used in Iris. In addition, it uses a
standard pattern using type classes to perform the normalization.

In addition to the tactics for symbolic execution, this file defines the tactic
[solve_proto_contractive], which can be used to automatically prove that
recursive protocols are contractive. *)
From iris.algebra Require Import gmap.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.heap_lang Require Export proofmode notation.
From multi_actris.channel Require Import proto_model.
From multi_actris.channel Require Export channel.
Set Default Proof Using "Type".

(** * Tactics for proving contractiveness of protocols *)
Ltac f_dist_le :=
  match goal with
  | H : _ ≡{?n}≡ _ |- _ ≡{?n'}≡ _ => apply (dist_le n); [apply H|lia]
  end.

Ltac solve_proto_contractive :=
  solve_proper_core ltac:(fun _ =>
    first [f_contractive; simpl in * | f_equiv | f_dist_le]).

(** * Normalization of protocols *)
Class ActionDualIf (d : bool) (a1 a2 : action) :=
  dual_action_if : a2 = if d then action_dual a1 else a1.
Global Hint Mode ActionDualIf ! ! - : typeclass_instances.

Global Instance action_dual_if_false a : ActionDualIf false a a := eq_refl.
Global Instance action_dual_if_true_send i : ActionDualIf true (Send,i) (Recv,i) := eq_refl.
Global Instance action_dual_if_true_recv i : ActionDualIf true (Recv,i) (Send,i) := eq_refl.

Class ProtoNormalize {Σ} (d : bool) (p : iProto Σ)
    (pas : list (bool * iProto Σ)) (q : iProto Σ) :=
  proto_normalize :
    ⊢ iProto_dual_if d p <++>
        foldr (iProto_app ∘ uncurry iProto_dual_if) END%proto pas ⊑ q.
Global Hint Mode ProtoNormalize ! ! ! ! - : typeclass_instances.
Arguments ProtoNormalize {_} _ _%proto _%proto _%proto.

Notation ProtoUnfold p1 p2 := (∀ d pas q,
  ProtoNormalize d p2 pas q → ProtoNormalize d p1 pas q).

Class MsgNormalize {Σ} (d : bool) (m1 : iMsg Σ)
    (pas : list (bool * iProto Σ)) (m2 : iMsg Σ) :=
  msg_normalize a :
    ProtoNormalize d (<a> m1) pas (<(if d then action_dual a else a)> m2).
Global Hint Mode MsgNormalize ! ! ! ! - : typeclass_instances.
Arguments MsgNormalize {_} _ _%msg _%msg _%msg.

Section classes.
  Context `{!chanG Σ, !heapGS Σ}.
  Implicit Types TT : tele.
  Implicit Types p : iProto Σ.
  Implicit Types m : iMsg Σ.
  Implicit Types P : iProp Σ.

  Lemma proto_unfold_eq p1 p2 : p1 ≡ p2 → ProtoUnfold p1 p2.
  Proof. rewrite /ProtoNormalize=> Hp d pas q. by rewrite Hp. Qed.

  Global Instance proto_normalize_done p : ProtoNormalize false p [] p | 0.
  Proof. rewrite /ProtoNormalize /= right_id. auto. Qed.
  Global Instance proto_normalize_done_dual p :
    ProtoNormalize true p [] (iProto_dual p) | 0.
  Proof. rewrite /ProtoNormalize /= right_id. auto. Qed.
  Global Instance proto_normalize_done_dual_end :
    ProtoNormalize (Σ:=Σ) true END [] END | 0.
  Proof. rewrite /ProtoNormalize /= right_id iProto_dual_end. auto. Qed.

  Global Instance proto_normalize_dual d p pas q :
    ProtoNormalize (negb d) p pas q →
    ProtoNormalize d (iProto_dual p) pas q.
  Proof. rewrite /ProtoNormalize. by destruct d; rewrite /= ?involutive. Qed.

  Global Instance proto_normalize_app_l d p1 p2 pas q :
    ProtoNormalize d p1 ((d,p2) :: pas) q →
    ProtoNormalize d (p1 <++> p2) pas q.
  Proof.
    rewrite /ProtoNormalize /=. rewrite assoc.
    by destruct d; by rewrite /= ?iProto_dual_app.
  Qed.

  Global Instance proto_normalize_end d d' p pas q :
    ProtoNormalize d p pas q →
    ProtoNormalize d' END ((d,p) :: pas) q | 0.
  Proof.
    rewrite /ProtoNormalize /=.
    destruct d'; by rewrite /= ?iProto_dual_end left_id.
  Qed.

  Global Instance proto_normalize_app_r d p1 p2 pas q :
    ProtoNormalize d p2 pas q →
    ProtoNormalize false p1 ((d,p2) :: pas) (p1 <++> q) | 0.
  Proof. rewrite /ProtoNormalize /= => H. by iApply iProto_le_app. Qed.

  Global Instance proto_normalize_app_r_dual d p1 p2 pas q :
    ProtoNormalize d p2 pas q →
    ProtoNormalize true p1 ((d,p2) :: pas) (iProto_dual p1 <++> q) | 0.
  Proof. rewrite /ProtoNormalize /= => H. by iApply iProto_le_app. Qed.

  Global Instance msg_normalize_base d v P p q pas :
    ProtoNormalize d p pas q →
    MsgNormalize d (MSG v {{ P }}; p) pas (MSG v {{ P }}; q).
  Proof.
    rewrite /MsgNormalize /ProtoNormalize=> H a.
    iApply iProto_le_trans; [|by iApply iProto_le_base].
    destruct d; by rewrite /= ?iProto_dual_message ?iMsg_dual_base
      iProto_app_message iMsg_app_base.
  Qed.

  Global Instance msg_normalize_exist {A} d (m1 m2 : A → iMsg Σ) pas :
    (∀ x, MsgNormalize d (m1 x) pas (m2 x)) →
    MsgNormalize d (∃ x, m1 x) pas (∃ x, m2 x).
  Proof.
    rewrite /MsgNormalize /ProtoNormalize=> H a.
    destruct d, a as [[|]];
                simpl in *; rewrite ?iProto_dual_message ?iMsg_dual_exist
      ?iProto_app_message ?iMsg_app_exist /=; iIntros (x); iExists x; first
      [move: (H x (Send,n)); by rewrite ?iProto_dual_message ?iProto_app_message
      |move: (H x (Recv,n)); by rewrite ?iProto_dual_message ?iProto_app_message].
  Qed.

  Global Instance proto_normalize_message d a1 a2 m1 m2 pas :
    ActionDualIf d a1 a2 →
    MsgNormalize d m1 pas m2 →
    ProtoNormalize d (<a1> m1) pas (<a2> m2).
  Proof. by rewrite /ActionDualIf /MsgNormalize /ProtoNormalize=> ->. Qed.

  (** Automatically perform normalization of protocols in the proof mode when
  using [iAssumption] and [iFrame]. *)
  Global Instance pointsto_proto_from_assumption q c p1 p2 :
    ProtoNormalize false p1 [] p2 →
    FromAssumption q (c ↣ p1) (c ↣ p2).
  Proof.
    rewrite /FromAssumption /ProtoNormalize /= right_id.
    rewrite bi.intuitionistically_if_elim.
    iIntros (?) "H". by iApply (iProto_pointsto_le with "H").
  Qed.
  Global Instance pointsto_proto_from_frame q c p1 p2 :
    ProtoNormalize false p1 [] p2 →
    Frame q (c ↣ p1) (c ↣ p2) True.
  Proof.
    rewrite /Frame /ProtoNormalize /= right_id.
    rewrite bi.intuitionistically_if_elim.
    iIntros (?) "[H _]". by iApply (iProto_pointsto_le with "H").
  Qed.
End classes.

(** * Symbolic execution tactics *)
(* TODO: Maybe strip laters from other hypotheses in the future? *)
Lemma tac_wp_recv `{!chanG Σ, !heapGS Σ} {TT : tele} Δ i j K v (n:nat) c p m tv tP tP' tp Φ :
  v = #n →
  envs_lookup i Δ = Some (false, c ↣ p)%I →
  ProtoNormalize false p [] (<(Recv,n)> m) →
  MsgTele m tv tP tp →
  (∀.. x, MaybeIntoLaterN false 1 (tele_app tP x) (tele_app tP' x)) →
  let Δ' := envs_delete false i false Δ in
  (∀.. x : TT,
    match envs_app false
        (Esnoc (Esnoc Enil j (tele_app tP' x)) i (c ↣ tele_app tp x)) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (of_val (tele_app tv x)) {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (recv c v) {{ Φ }}).
Proof.
  intros ->.
  rewrite envs_entails_unseal /ProtoNormalize /MsgTele /MaybeIntoLaterN /=.
  rewrite !tforall_forall right_id.
  intros ? Hp Hm HP HΦ. rewrite envs_lookup_sound //; simpl.
  assert (c ↣ p ⊢ c ↣ <(Recv,n) @ x>
    MSG tele_app tv x {{ ▷ tele_app tP' x }}; tele_app tp x) as ->.
  { iIntros "Hc". iApply (iProto_pointsto_le with "Hc"). iIntros "!>".
    iApply iProto_le_trans; [iApply Hp|rewrite Hm].
    iApply iProto_le_texist_elim_l; iIntros (x).
    iExists _. iIntros "H". by iDestruct (HP with "H") as "$". }
  rewrite -wp_bind. eapply bi.wand_apply;
    [by eapply bi.wand_entails, (recv_spec _ n (tele_app tv) (tele_app tP') (tele_app tp))|f_equiv; first done].
  rewrite -bi.later_intro; apply bi.forall_intro=> x.
  specialize (HΦ x). destruct (envs_app _ _) as [Δ'|] eqn:HΔ'=> //.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΦ.
Qed.

Tactic Notation "wp_recv_core" tactic3(tac_intros) "as" tactic3(tac) :=
  let solve_pointsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣ _)%I) => c end in
    iAssumptionCore || fail "wp_recv: cannot find" c "↣ ? @ ?" in
  wp_pures;
  let Hnew := iFresh in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_recv _ _ Hnew K))
      |fail 1 "wp_recv: cannot find 'recv' in" e];
    [|solve_pointsto ()
       |tc_solve || fail 1 "wp_recv: protocol not of the shape <?>"
    |tc_solve || fail 1 "wp_recv: cannot convert to telescope"
    |tc_solve
    |pm_reduce; simpl; tac_intros;
     tac Hnew;
     wp_finish];[try done|]
  | _ => fail "wp_recv: not a 'wp'"
  end.


Tactic Notation "wp_recv" "as" constr(pat) :=
  wp_recv_core (idtac) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as"
    "(" ne_simple_intropattern_list(ys) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => _iDestructHyp H ys pat).
    
Lemma tac_wp_send `{!chanG Σ, !heapGS Σ} {TT : tele} Δ neg i js K (n:nat) w c v p m tv tP tp Φ :
  w = #n →
  envs_lookup i Δ = Some (false, c ↣ p)%I →
  ProtoNormalize false p [] (<(Send,n)> m) →
  MsgTele m tv tP tp →
  let Δ' := envs_delete false i false Δ in
  (∃.. x : TT,
    match envs_split (if neg is true then base.Right else base.Left) js Δ' with
    | Some (Δ1,Δ2) =>
       match envs_app false (Esnoc Enil i (c ↣ tele_app tp x)) Δ2 with
       | Some Δ2' =>
          v = tele_app tv x ∧
          envs_entails Δ1 (tele_app tP x) ∧
          envs_entails Δ2' (WP fill K (of_val #()) {{ Φ }})
       | None => False
       end
    | None => False
    end) →
  envs_entails Δ (WP fill K (send c w v) {{ Φ }}).
Proof.
  intros ->.
  rewrite envs_entails_unseal /ProtoNormalize /MsgTele /= right_id texist_exist.
  intros ? Hp Hm [x HΦ]. rewrite envs_lookup_sound //; simpl.
  destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:? => //.
  destruct (envs_app _ _ _) as [Δ2'|] eqn:? => //.
  rewrite envs_split_sound //; rewrite (envs_app_sound Δ2) //; simpl.
  destruct HΦ as (-> & -> & ->). rewrite right_id assoc.
  assert (c ↣ p ⊢
    c ↣ <(Send,n) @.. (x : TT)> MSG tele_app tv x {{ tele_app tP x }}; tele_app tp x) as ->.
  { iIntros "Hc". iApply (iProto_pointsto_le with "Hc"); iIntros "!>".
    iApply iProto_le_trans; [iApply Hp|]. by rewrite Hm. }
  eapply bi.wand_apply; [rewrite -wp_bind; by eapply bi.wand_entails, send_spec_tele|].
  by rewrite -bi.later_intro.
Qed.

Tactic Notation "wp_send_core" tactic3(tac_exist) "with" constr(pat) :=
  let solve_pointsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣ _)%I) => c end in
    iAssumptionCore || fail "wp_send: cannot find" c "↣ ? @ ?" in
  let solve_done d :=
    lazymatch d with
    | true =>
       done ||
       let Q := match goal with |- envs_entails _ ?Q => Q end in
       fail "wp_send: cannot solve" Q "using done"
    | false => idtac
    end in
  lazymatch spec_pat.parse pat with
  | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in
     wp_pures;
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_send _ neg _ Hs' K))
         |fail 1 "wp_send: cannot find 'send' in" e];
       [|solve_pointsto ()
       |tc_solve || fail 1 "wp_send: protocol not of the shape <!>"
       |tc_solve || fail 1 "wp_send: cannot convert to telescope"
       |pm_reduce; simpl; tac_exist;
        repeat lazymatch goal with
        | |- ∃ _, _ => eexists _
        end;
        lazymatch goal with
        | |- False => fail "wp_send:" Hs' "not found"
        | _ => notypeclasses refine (conj (eq_refl _) (conj _ _));
                [iFrame Hs_frame; solve_done d
                |wp_finish]
        end]; [try done|..]
     | _ => fail "wp_send: not a 'wp'"
     end
  | _ => fail "wp_send: only a single goal spec pattern supported"
  end.

Tactic Notation "wp_send" "with" constr(pat) :=
  wp_send_core (idtac) with pat.
Tactic Notation "wp_send" "(" ne_uconstr_list(xs) ")" "with" constr(pat) :=
  wp_send_core (ltac1_list_iter ltac:(fun x => eexists x) xs) with pat.

Lemma iProto_consistent_equiv_proof {Σ} (ps : list (iProto Σ)) :
  (∀ i j, valid_target ps i j) ∗
  (∀ i j m1 m2,
     (ps !!! i ≡ (<(Send, j)> m1)%proto) -∗
     (ps !!! j ≡ (<(Recv, i)> m2)%proto) -∗
     ∃ m1' m2' (TT1:tele) (TT2:tele) tv1 tP1 tp1 tv2 tP2 tp2,
       (<(Send, j)> m1')%proto ≡ (<(Send, j)> m1)%proto ∗
       (<(Recv, i)> m2')%proto ≡ (<(Recv, i)> m2)%proto ∗
       ⌜MsgTele (TT:=TT1) m1' tv1 tP1 tp1⌝ ∗
       ⌜MsgTele (TT:=TT2) m2' tv2 tP2 tp2⌝ ∗
   ∀.. (x : TT1), tele_app tP1 x -∗
   ∃.. (y : TT2), ⌜tele_app tv1 x = tele_app tv2 y⌝ ∗
                  tele_app tP2 y ∗
                  ▷ (iProto_consistent
                       (<[i:=tele_app tp1 x]>(<[j:=tele_app tp2 y]>ps)))) -∗
  iProto_consistent ps.
Proof.
  iIntros "[H' H]".
  rewrite iProto_consistent_unfold.
  iFrame.
  iIntros (i j m1 m2) "Hm1 Hm2".
  iDestruct ("H" with "Hm1 Hm2")
    as (m1' m2' TT1 TT2 tv1 tP1 tp1 tv2 tP2 tp2)
         "(Heq1 & Heq2& %Hm1' & %Hm2' & H)".
  rewrite !iProto_message_equivI.
  iDestruct "Heq1" as "[_ Heq1]".
  iDestruct "Heq2" as "[_ Heq2]".
  iIntros (v p1) "Hm1".
  iSpecialize ("Heq1" $! v (Next p1)).
  iRewrite -"Heq1" in "Hm1".
  rewrite Hm1'.
  rewrite iMsg_base_eq. rewrite iMsg_texist_exist.
  iDestruct "Hm1" as (x Htv1) "[Hp1 HP1]".
  iDestruct ("H" with "HP1") as (y Htv2) "[HP2 H]".
  iExists (tele_app tp2 y).
  iSpecialize ("Heq2" $! v (Next (tele_app tp2 y))).
  iRewrite -"Heq2".
  rewrite Hm2'. rewrite iMsg_base_eq. rewrite iMsg_texist_exist.
  iSplitL "HP2".
  { iExists y. iFrame.
    iSplit; [|done].
    iPureIntro. subst. done. }
  iNext. iRewrite -"Hp1". done.
Qed.

(* TODO: Improve automation *)
Tactic Notation "iProto_consistent_take_step_step" :=
  let i := fresh in
  let j := fresh in
  let m1 := fresh in
  let m2 := fresh in
  iIntros (i j m1 m2) "#Hm1 #Hm2";
  repeat (destruct i as [|i]=> /=;
          [try (by rewrite iProto_end_message_equivI);
           iDestruct (iProto_message_equivI with "Hm1")
                  as "[%Heq1 Hm1']";simplify_eq=> /=|
            try (by rewrite iProto_end_message_equivI)]);
  try (by rewrite iProto_end_message_equivI);
  iDestruct (iProto_message_equivI with "Hm2")
    as "[%Heq2 Hm2']";simplify_eq=> /=;
  try (iClear "Hm1' Hm2'";
       iExists _,_,_,_,_,_,_,_,_,_;
       iSplitL "Hm1"; [iFrame "#"|];
       iSplitL "Hm2"; [iFrame "#"|];
       iSplit; [iPureIntro; tc_solve|];
       iSplit; [iPureIntro; tc_solve|];
       simpl; iClear "Hm1 Hm2"; clear m1 m2).

Tactic Notation "iProto_consistent_take_step_target" :=
  let i := fresh in
  iIntros (i j a m); rewrite /valid_target;
            iIntros "#Hm1";
  repeat (destruct i as [|i]=> /=;
          [try (by rewrite iProto_end_message_equivI);
           by iDestruct (iProto_message_equivI with "Hm1")
                    as "[%Heq1 _]" ; simplify_eq=> /=|
           try (by rewrite iProto_end_message_equivI)]).

Tactic Notation "iProto_consistent_take_step" :=
  try iNext;
  iApply iProto_consistent_equiv_proof;
  iSplitR; [iProto_consistent_take_step_target|
             iProto_consistent_take_step_step].

Tactic Notation "iProto_consistent_resolve_step" :=
  repeat iIntros (?); repeat iIntros "?";
  repeat iExists _; repeat (iSplit; [done|]); try iFrame.

Tactic Notation "iProto_consistent_take_steps" :=
  repeat (iProto_consistent_take_step; iProto_consistent_resolve_step).

Tactic Notation "wp_get_chan" "(" simple_intropattern(c) ")" constr(pat) :=
  wp_smart_apply (get_chan_spec with "[$]"); iIntros (c) "[_TMP ?]";
  iRevert "_TMP"; iIntros pat.

Ltac ltac1_list_iter2 tac l1 l2 :=
  let go := ltac2:(tac l1 l2 |- List.iter2 (ltac1:(tac x y |- tac x y) tac)
                                          (of_ltac1_list l1) (of_ltac1_list l2)) in
  go tac l1 l2.

Tactic Notation "wp_new_chan" constr(prot) "as"
       "(" simple_intropattern_list(xs) ")" constr_list(pats) :=
  wp_smart_apply (new_chan_spec prot);
    [set_solver| |iIntros (?) "?"];
    [|ltac1_list_iter2 ltac:(fun x y => wp_get_chan (x) y) xs pats].

Tactic Notation "wp_new_chan" constr(prot) "with" constr(lem) "as"
       "(" simple_intropattern_list(xs) ")" constr_list(pats) :=
  wp_smart_apply (new_chan_spec prot);
    [set_solver|by iApply lem|iIntros (?) "?"];
    ltac1_list_iter2 ltac:(fun x y => wp_get_chan (x) y) xs pats.
