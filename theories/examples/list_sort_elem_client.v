From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From osiris.utils Require Import list compare.
From osiris.examples Require Import list_sort_elem.

Definition send_all : val :=
  rec: "go" "c" "xs" :=
    match: "xs" with
      SOME "p" => send "c" #cont;; send "c" (Fst "p");; "go" "c" (Snd "p")
    | NONE => send "c" #stop
    end.

Definition recv_all : val :=
  rec: "go" "c" :=
    if: recv "c"
    then lcons (recv "c") ("go" "c")
    else lnil #().

Definition list_sort_elem_client : val :=
  λ: "cmp" "xs",
    let: "c" := start_chan list_sort_elem_service_top in
    send "c" "cmp";;
    send_all "c" ("xs");;
    recv_all "c".

Section list_sort_elem_client.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  Lemma send_all_spec 
    {A : Type} (I : A → val → iProp Σ) R `{!RelDecision R, !Total R} 
    (xs : list A) (vs : list val) c :
    {{{ ([∗ list] x;v ∈ xs ; vs, I x v) ∗
        c ↣ head_protocol I R [] @ N }}}
      send_all c (val_encode vs)
    {{{ RET #(); 
        ([∗ list] x;v ∈ xs ; vs, I x v) ∗
        c ↣ tail_protocol I R (zip xs vs) [] @ N }}}.
  Proof. Admitted.

  Lemma recv_all_spec 
    {A : Type} (I : A → val → iProp Σ) R `{!RelDecision R, !Total R} 
    (xs : list A) (vs : list val) c :
    {{{ ([∗ list] x;v ∈ xs ; vs, I x v) ∗
        c ↣ tail_protocol I R (zip xs vs) [] @ N }}}
      recv_all c
    {{{ ys ws, RET (val_encode ws);
        c ↣ END @ N ∗
        ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗
        [∗ list] y;w ∈ ys;ws, I y w
    }}}.
  Proof. Admitted.

  Lemma list_sort_client_spec {A} (I : A → val → iProp Σ) R
       `{!RelDecision R, !Total R} cmp (vs : list val) (xs : list A) :
    cmp_spec I R cmp -∗
    {{{ [∗ list] x;v ∈ xs;vs, I x v }}}
      list_sort_elem_client cmp (val_encode vs)
    {{{ ys ws, RET (val_encode ws); ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗
               [∗ list] y;w ∈ ys;ws, I y w }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hinterp HΦ". wp_lam.
    wp_apply (start_chan_proto_spec N list_sort_elem_top_protocol); iIntros (c) "Hc".
    { wp_apply (list_sort_elem_service_top_spec N with "Hc"); auto. }
    wp_pures.
    rewrite /list_sort_elem_top_protocol.
    simpl.
    wp_send with "[$Hcmp]".
    wp_pures.
    wp_apply (send_all_spec with "[Hinterp Hc]")=> //.
    iFrame.
    iIntros "Hc".
    wp_pures.
    wp_apply (recv_all_spec with "[Hc]")=>//.
    iIntros (ys ws) "(Hc & Hsorted & Hperm & Hinterp)".
    iApply "HΦ".
    iFrame.
  Qed.

End list_sort_elem_client.