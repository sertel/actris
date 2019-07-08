From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export tactics.
From actris Require Export proto_channel.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.

(* TODO: strip laters *)
Lemma tac_wp_recv `{!proto_chanG Σ, !heapG Σ} {TT : tele} Δ i j K N
    c p (pc : TT → val * iProp Σ * iProto Σ) Φ :
  envs_lookup i Δ = Some (false, c ↣ p @ N)%I →
  ProtoNormalize false p [] (iProto_message Receive pc) →
  let Δ' := envs_delete false i false Δ in
  (∀.. x : TT,
    match envs_app false
        (Esnoc (Esnoc Enil j ((pc x).1.2)) i (c ↣ (pc x).2 @ N)) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (of_val (pc x).1.1) {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (recv c) {{ Φ }}).
Proof.
  rewrite envs_entails_eq /ProtoNormalize /= tforall_forall right_id=> ? Hp HΦ.
  rewrite envs_lookup_sound //; simpl. rewrite -Hp.
  rewrite -wp_bind. eapply bi.wand_apply; [by eapply recv_proto_spec|f_equiv].
  rewrite -bi.later_intro bi_tforall_forall; apply bi.forall_intro=> x.
  specialize (HΦ x). destruct (envs_app _ _) as [Δ'|] eqn:HΔ'=> //.
  rewrite envs_app_sound //; simpl.
  by rewrite right_id HΦ bi.wand_curry.
Qed.

Tactic Notation "wp_recv_core" tactic3(tac_intros) "as" tactic3(tac) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣ _ @ _)%I) => c end in
    iAssumptionCore || fail "wp_recv: cannot find" c "↣ ? @ ?" in
  wp_pures;
  let Hnew := iFresh in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_recv _ _ Hnew K))
      |fail 1 "wp_recv: cannot find 'recv' in" e];
    [solve_mapsto ()
       |iSolveTC || fail 1 "wp_send: protocol not of the shape <?>"
    |pm_reduce; simpl; tac_intros;
     tac Hnew;
     wp_finish]
  | _ => fail "wp_recv: not a 'wp'"
  end.

Tactic Notation "wp_recv" "as" constr(pat) :=
  wp_recv_core (idtac) as (fun H => iDestructHyp H as pat).

Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).

Lemma tac_wp_send `{!proto_chanG Σ, !heapG Σ} {TT : tele} Δ neg i js K N
    c v p (pc : TT → val * iProp Σ * iProto Σ) Φ :
  envs_lookup i Δ = Some (false, c ↣ p @ N)%I →
  ProtoNormalize false p [] (iProto_message Send pc) →
  let Δ' := envs_delete false i false Δ in
  (∃.. x : TT,
    match envs_split (if neg is true then Right else Left) js Δ' with
    | Some (Δ1,Δ2) =>
       match envs_app false (Esnoc Enil i (c ↣ (pc x).2 @ N)) Δ2 with
       | Some Δ2' =>
          v = (pc x).1.1 ∧
          envs_entails Δ1 (pc x).1.2 ∧
          envs_entails Δ2' (WP fill K (of_val #()) {{ Φ }})
       | None => False
       end
    | None => False
    end) →
  envs_entails Δ (WP fill K (send c v) {{ Φ }}).
Proof.
  rewrite envs_entails_eq /ProtoNormalize /= right_id texist_exist=> ? Hp [x HΦ].
  rewrite envs_lookup_sound //; simpl. rewrite -Hp.
  rewrite -wp_bind. eapply bi.wand_apply; [by eapply send_proto_spec|f_equiv].
  rewrite bi_texist_exist -(bi.exist_intro x).
  destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:? => //.
  destruct (envs_app _ _ _) as [Δ2'|] eqn:? => //.
  rewrite envs_split_sound //; rewrite (envs_app_sound Δ2) //; simpl.
  destruct HΦ as (-> & -> & ->). rewrite bi.pure_True // left_id.
  by rewrite -bi.later_intro right_id.
Qed.

Tactic Notation "wp_send_core" tactic3(tac_exist) "with" constr(pat) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣ _ @ _)%I) => c end in
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
       [solve_mapsto ()
       |iSolveTC || fail 1 "wp_send: protocol not of the shape <!>"
       |pm_reduce; simpl; tac_exist;
        repeat lazymatch goal with
        | |- ∃ _, _ => eexists _
        end;
        lazymatch goal with
        | |- False => fail "wp_send:" Hs' "not found"
        | _ => split; [try fast_done|split;[iFrame Hs_frame; solve_done d|wp_finish]]
        end]
     | _ => fail "wp_send: not a 'wp'"
     end
  | _ => fail "wp_send: only a single goal spec pattern supported"
  end.

Tactic Notation "wp_send" "with" constr(pat) :=
  wp_send_core (idtac) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) ")" "with" constr(pat) :=
  wp_send_core (eexists x1) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) ")"
    "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4)
    uconstr(x5) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) uconstr(x7) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6; eexists x7) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) uconstr(x7) uconstr(x8) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6; eexists x7; eexists x8) with pat.

Lemma tac_wp_branch `{!proto_chanG Σ, !heapG Σ} Δ i j K N
    c p P1 P2 (p1 p2 : iProto Σ) Φ :
  envs_lookup i Δ = Some (false, c ↣ p @ N)%I →
  ProtoNormalize false p [] (p1 <{P1}&{P2}> p2) →
  let Δ' := envs_delete false i false Δ in
  (∀ b : bool,
    match envs_app false
        (Esnoc (Esnoc Enil j (if b then P1 else P2)) i (c ↣ (if b then p1 else p2) @ N)) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (of_val #b) {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (recv c) {{ Φ }}).
Proof.
  rewrite envs_entails_eq /ProtoNormalize /= right_id=> ? Hp HΦ.
  rewrite envs_lookup_sound //; simpl. rewrite -Hp.
  rewrite -wp_bind. eapply bi.wand_apply; [by eapply branch_spec|f_equiv].
  rewrite -bi.later_intro; apply bi.forall_intro=> b.
  specialize (HΦ b). destruct (envs_app _ _) as [Δ'|] eqn:HΔ'=> //.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΦ.
Qed.

Tactic Notation "wp_branch_core" "as" tactic3(tac1) tactic3(tac2) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣ _ @ _)%I) => c end in
    iAssumptionCore || fail "wp_branch: cannot find" c "↣ ? @ ?" in
  wp_pures;
  let Hnew := iFresh in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_branch _ _ Hnew K))
      |fail 1 "wp_branch: cannot find 'recv' in" e];
    [solve_mapsto ()
       |iSolveTC || fail 1 "wp_send: protocol not of the shape <&>"
    |pm_reduce; intros []; [tac1 Hnew|tac2 Hnew]; wp_finish]
  | _ => fail "wp_branch: not a 'wp'"
  end.

Tactic Notation "wp_branch" "as" constr(pat1) "|" constr(pat2) :=
  wp_branch_core as (fun H => iDestructHyp H as pat1) (fun H => iDestructHyp H as pat2).
Tactic Notation "wp_branch" "as" "%" intropattern(pat1) "|" constr(pat2) :=
  wp_branch_core as (fun H => iPure H as pat1) (fun H => iDestructHyp H as pat2).
Tactic Notation "wp_branch" "as" constr(pat1) "|" "%" intropattern(pat2) :=
  wp_branch_core as (fun H => iDestructHyp H as pat1) (fun H => iPure H as pat2).
Tactic Notation "wp_branch" "as" "%" intropattern(pat1) "|" "%" intropattern(pat2) :=
  wp_branch_core as (fun H => iPure H as pat1) (fun H => iPure H as pat2).
Tactic Notation "wp_branch" := wp_branch as %_ | %_.

Lemma tac_wp_select `{!proto_chanG Σ, !heapG Σ} Δ neg i js K N
    c (b : bool) p P1 P2 (p1 p2 : iProto Σ) Φ :
  envs_lookup i Δ = Some (false, c ↣ p @ N)%I →
  ProtoNormalize false p [] (p1 <{P1}+{P2}> p2) →
  let Δ' := envs_delete false i false Δ in
  match envs_split (if neg is true then Right else Left) js Δ' with
  | Some (Δ1,Δ2) =>
     match envs_app false (Esnoc Enil i (c ↣ if b then p1 else p2 @ N)) Δ2 with
     | Some Δ2' =>
        envs_entails Δ1 (if b then P1 else P2) ∧
        envs_entails Δ2' (WP fill K (of_val #()) {{ Φ }})
     | None => False
     end
  | None => False
  end →
  envs_entails Δ (WP fill K (send c #b) {{ Φ }}).
Proof.
  rewrite envs_entails_eq /ProtoNormalize /= right_id=> ? Hp HΦ.
  rewrite envs_lookup_sound //; simpl. rewrite -Hp.
  rewrite -wp_bind. eapply bi.wand_apply; [by eapply select_spec|].
  rewrite -assoc; f_equiv.
  destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:? => //.
  destruct (envs_app _ _ _) as [Δ2'|] eqn:? => //.
  rewrite envs_split_sound //; rewrite (envs_app_sound Δ2) //; simpl.
  destruct HΦ as [-> ->]. by rewrite -bi.later_intro right_id.
Qed.

Tactic Notation "wp_select" "with" constr(pat) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣ _ @ _)%I) => c end in
    iAssumptionCore || fail "wp_select: cannot find" c "↣ ? @ ?" in
  let solve_done d :=
    lazymatch d with
    | true =>
       done ||
       let Q := match goal with |- envs_entails _ ?Q => Q end in
       fail "wp_select: cannot solve" Q "using done"
    | false => idtac
    end in
  lazymatch spec_pat.parse pat with
  | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in
     wp_pures;
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_select _ neg _ Hs' K))
         |fail 1 "wp_select: cannot find 'send' in" e];
       [solve_mapsto ()
       |iSolveTC || fail 1 "wp_select: protocol not of the shape <+>"
       |pm_reduce;
        lazymatch goal with
        | |- False => fail "wp_select:" Hs' "not fresh"
        | _ => split;[iFrame Hs_frame; solve_done d|wp_finish]
        end]
     | _ => fail "wp_select: not a 'wp'"
     end
  | _ => fail "wp_select: only a single goal spec pattern supported"
  end.

Tactic Notation "wp_select" := wp_select with "[//]".
