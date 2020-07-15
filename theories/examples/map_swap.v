(** This file implements a distributed mapper service, a specification thereof,
and its proofs. *)
From actris.channel Require Import proofmode.
From iris.heap_lang Require Import lib.spin_lock.
From actris.utils Require Import llist contribution.
From iris.algebra Require Import gmultiset.

(** * Correctness proofs of the distributed version *)
Class mapG Σ A `{Countable A} := {
  map_contributionG :> contributionG Σ (gmultisetUR A);
  map_lockG :> lockG Σ;
}.

Section map.
  Context `{Countable A} {B : Type}.
  Context `{!heapG Σ, !chanG Σ, !mapG Σ A}.
  Context (IA : A → val → iProp Σ) (IB : B → val → iProp Σ) (map : A → list B).
  Local Open Scope nat_scope.
  Implicit Types n : nat.

  Definition map_spec (vmap : val) : iProp Σ := (∀ x v,
    {{{ IA x v }}} vmap v {{{ l, RET #l; llist IB l (map x) }}})%I.

  Definition map_protocol_recv_aux (rec : gmultiset A -d> iProto Σ) :
    gmultiset A -d> iProto Σ :=
    λ X,
    (if decide (X ≠ ∅) then END else
      <! x (l : loc)> MSG #l {{ ⌜ x ∈ X ⌝ ∗ llist IB l (map x) }};
    rec (X ∖ {[ x ]}))%proto.
  Instance map_protocol_recv_aux_contractive : Contractive map_protocol_recv_aux.
  Proof. solve_proper_prepare. f_equiv. solve_proto_contractive. Qed.
  Definition map_protocol_recv := fixpoint map_protocol_recv_aux.
  Global Instance map_protocol_recv_unfold X :
    ProtoUnfold (map_protocol_recv X) (map_protocol_recv_aux map_protocol_recv X).
  Proof. apply proto_unfold_eq, (fixpoint_unfold map_protocol_recv_aux). Qed.

  Definition map_protocol_aux (rec : nat -d> gmultiset A -d> iProto Σ) :
      nat -d> gmultiset A -d> iProto Σ := λ n X,
    let rec : nat → gmultiset A → iProto Σ := rec in
    (if n is 0 then map_protocol_recv X else
     ((<?x v> MSG v {{ IA x v }}; rec n (X ⊎ {[ x ]}))
        <&>
      rec (pred n) X))%proto.

  Instance map_protocol_aux_contractive : Contractive map_protocol_aux.
  Proof. solve_proper_prepare. f_equiv. solve_proto_contractive. Qed.
  Definition map_protocol := fixpoint map_protocol_aux.
  Global Instance map_protocol_unfold n X :
    ProtoUnfold (map_protocol n X) (map_protocol_aux map_protocol n X).
  Proof. apply proto_unfold_eq, (fixpoint_unfold map_protocol_aux). Qed.

  Lemma sub_proof n x X :
    ⊢ (map_protocol n ({[ x ]} ⊎ X) ⊑
       <? (l : loc)> MSG #l {{ llist IB l (map x) }} ; map_protocol n X)%proto.
  Proof. Admitted.

End map.
