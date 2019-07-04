From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From osiris.utils Require Import list compare.
From osiris.examples Require Import sort_elem.

Definition send_all : val :=
  rec: "go" "c" "xs" :=
    match: "xs" with
      SOME "p" => send "c" #cont;; send "c" (Fst "p");; "go" "c" (Snd "p")
    | NONE => send "c" #stop
    end.

Definition recv_all : val :=
  rec: "go" "c" :=
    if: recv "c"
    then let: "x" := recv "c" in lcons "x" ("go" "c")
    else lnil #().

Definition sort_elem_client : val :=
  λ: "cmp" "xs",
    let: "c" := start_chan sort_elem_service_top in
    send "c" "cmp";;
    send_all "c" "xs";;
    recv_all "c".

Section sort_elem_client.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).
  Context {A} (I : A → val → iProp Σ) (R : relation A) `{!RelDecision R, !Total R}.

  Lemma send_all_spec c p xs' xs vs :
    {{{ c ↣ sort_elem_head_protocol I R xs' <++> p @ N ∗ [∗ list] x;v ∈ xs;vs, I x v }}}
      send_all c (llist vs)
    {{{ RET #(); c ↣ sort_elem_tail_protocol I R (xs' ++ xs) [] <++> p @ N }}}.
  Proof.
    iIntros (Φ) "[Hc HI] HΦ".
    iInduction xs as [|x xs] "IH" forall (xs' vs); destruct vs as [|v vs]=>//.
    { wp_lam; wp_pures. wp_select. iApply "HΦ". rewrite right_id_L. iFrame. }
    iDestruct "HI" as "[HIxv HI]". wp_lam; wp_pures.
    wp_select. wp_send with "[$HIxv]". wp_apply ("IH" with "Hc HI").
    by rewrite -assoc_L.
  Qed.

  Lemma recv_all_spec c p xs ys' :
    Sorted R ys' →
    {{{ c ↣ sort_elem_tail_protocol I R xs ys' <++> p @ N }}}
      recv_all c
    {{{ ys ws, RET (llist ws);
        ⌜Sorted R (ys' ++ ys)⌝ ∗ ⌜ys' ++ ys ≡ₚ xs⌝ ∗
        c ↣ p @ N ∗ [∗ list] y;w ∈ ys;ws, I y w
    }}}.
  Proof.
    iIntros (Hsort Φ) "Hc HΦ".
    iLöb as "IH" forall (xs ys' Φ Hsort).
    wp_lam. wp_branch as %_ | %Hperm; wp_pures.
    - wp_recv (y v) as (Htl) "HIxv".
      wp_apply ("IH" with "[] Hc"); first by auto using Sorted_snoc.
      iIntros (ys ws). rewrite -!assoc_L. iDestruct 1 as (??) "[Hc HI]".
      wp_apply (lcons_spec with "[//]"); iIntros (_).
      iApply ("HΦ" $! (y :: ys)). simpl; iFrame; auto.
    - wp_apply (lnil_spec with "[//]"); iIntros (_).
      iApply ("HΦ" $! [] []); rewrite /= right_id_L; by iFrame.
  Qed.

  Lemma sort_client_spec cmp vs xs :
    cmp_spec I R cmp -∗
    {{{ [∗ list] x;v ∈ xs;vs, I x v }}}
      sort_elem_client cmp (llist vs)
    {{{ ys ws, RET (llist ws); ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗
               [∗ list] y;w ∈ ys;ws, I y w }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "HI HΦ". wp_lam.
    wp_apply (start_chan_proto_spec N (sort_elem_top_protocol <++> END)%proto);
      iIntros (c) "Hc".
    { wp_apply (sort_elem_service_top_spec N with "Hc"); auto. }
    rewrite /sort_elem_top_protocol.
    wp_send (A I R) with "[$Hcmp]".
    wp_apply (send_all_spec with "[$HI $Hc]"); iIntros "Hc".
    wp_apply (recv_all_spec _ _ _ [] with "[$Hc]"); auto.
    iIntros (ys ws) "/=". iDestruct 1 as (??) "[_ HI]".
    iApply "HΦ"; auto.
  Qed.
End sort_elem_client.