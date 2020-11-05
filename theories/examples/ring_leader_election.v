From actris.channel Require Import proofmode.
From iris.heap_lang Require Import proofmode.
From actris.utils Require Import contribution.

Definition cont := true.
Definition elected := false.

Definition process : val :=
  rec: "go" "id" "cl" "cr" :=
    if: ~ (recv "cr") then
      send "cl" #elected;; send "cl" (recv "cr");;
      #() (* Do termination of non-leader here *)
    else
      let: "id'" := recv "cr" in
      if: "id" = "id'" then send "cl" #elected;; send "cl" "id";;
                            #() (* Do termination of leader here *)
      else if: "id" < "id'" then send "cl" #cont;; send "cl" "id'";;
                                 "go" "id" "cl" "cr"
      else send "cl" #cont;; send "cl" "id";;
           "go" "id" "cl" "cr".

Section ring_leader_election_example.
  Context `{!heapG Σ, chanG Σ}.

  Definition rle_prot_aux (rec : Z -d> iProto Σ) : Z -d> iProto Σ :=
    λ (max_id : Z),
      ((<! (id:Z)> MSG #id ; rec (Z.max max_id id))
         <+>
       (<!> MSG #max_id ; END))%proto.
  Instance rle_prot_aux_contractive : Contractive rle_prot_aux.
  Proof. solve_proto_contractive. Qed.
  Definition rle_prot := fixpoint rle_prot_aux.
  Instance rle_prot_unfold max_id :
    ProtoUnfold (rle_prot max_id) (rle_prot_aux rle_prot max_id).
  Proof. apply proto_unfold_eq, (fixpoint_unfold rle_prot_aux). Qed.
  
  Lemma process_spec id cl cr :
    {{{ cl ↣ (rle_prot id) ∗ cr ↣ iProto_dual (rle_prot id) }}}
      process #id cl cr
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[Hcl Hcr] HΦ".
    iLöb as "IH" forall (id).
    wp_rec.
    wp_branch.
    - wp_recv (id') as "_".
      wp_pures. case_bool_decide; wp_pures; [ | case_bool_decide ]; wp_pures.
      + wp_select. wp_send with "[//]".
        wp_pures. by iApply "HΦ".
      + wp_select. wp_send with "[//]".
        wp_pures.
        replace (id `max` id')%Z with id' by lia.
        iApply ("IH" with "[Hcl] [Hcr]").
        { admit. }
        { admit. }
        iApply "HΦ".
      + wp_select. wp_send with "[//]".
        wp_pures.
        replace (id `max` id')%Z with id by lia.
        iApply ("IH" with "[Hcl] [Hcr]").
        { admit. }
        { admit. }
        iApply "HΦ".
    - wp_pures. wp_select.
      wp_pures.
      wp_recv as "_".
      wp_send with "[//]".
      wp_pures. by iApply "HΦ".
  Admitted.

End ring_leader_election_example.
