From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel.
From iris.heap_lang Require Import proofmode notation.
From osiris.utils Require Import list.
From osiris.examples Require Import list_sort.

Definition loop_sort_service : val :=
  rec: "go" "c" :=
    if: recv "c" then list_sort_service "c";; "go" "c"
    else if: recv "c" then
      let: "d" := start_chan "go" in
      send "c" "d";;
      "go" "c"
    else #().

Section loop_sort.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  
  Definition loop_sort_protocol_aux (rec : iProto Σ) : iProto Σ :=
    ((sort_protocol <++> rec) <+> ((<?> c, MSG c {{ c ↣ rec @ N }}; rec) <+> END))%proto.

  Instance loop_sort_protocol_aux_contractive : Contractive loop_sort_protocol_aux.
  Proof.
    intros n p p' Hp. rewrite /loop_sort_protocol_aux.
    f_contractive; f_equiv=> //. apply iProto_message_ne=> c /=; by repeat f_equiv.
  Qed.
  Definition loop_sort_protocol : iProto Σ := fixpoint loop_sort_protocol_aux.
  Lemma loop_sort_protocol_unfold :
    loop_sort_protocol ≡ loop_sort_protocol_aux loop_sort_protocol.
  Proof. apply (fixpoint_unfold loop_sort_protocol_aux). Qed.

  Lemma loop_sort_service_spec c :
    {{{ c ↣ iProto_dual loop_sort_protocol @ N }}}
      loop_sort_service c
    {{{ RET #(); c ↣ END @ N }}}.
  Proof.
    iIntros (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
    wp_rec. rewrite {2}loop_sort_protocol_unfold.
    wp_apply (branch_spec with "Hc"); iIntros ([]) "/= [Hc _]"; wp_if.
    { wp_apply (list_sort_service_spec with "Hc"); iIntros "Hc".
      by wp_apply ("IH" with "Hc"). }
    wp_apply (branch_spec with "Hc"); iIntros ([]) "/= [Hc _]"; wp_if.
    - wp_apply (start_chan_proto_spec N loop_sort_protocol); iIntros (d) "Hd".
      { wp_apply ("IH" with "Hd"); auto. }
      wp_apply (send_proto_spec with "Hc"); simpl.
      iExists d; iSplit; first done. iIntros "{$Hd} !> Hc".
      by wp_apply ("IH" with "Hc").
    - by iApply "HΨ".
  Qed.

End loop_sort.