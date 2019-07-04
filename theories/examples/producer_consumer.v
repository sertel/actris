From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From osiris.utils Require Import list compare spin_lock.

Definition qnew : val := λ: <>, #().
Definition qenqueue : val := λ: "q" "v", #().
Definition qdequeue : val := λ: "q", #().
Definition qis_empty : val := λ: "q", #().

Definition enq := true.
Definition deq := false.

Definition cont := true.
Definition stop := false.

Definition some := true.
Definition none := false.

Definition pd_loop : val :=
  rec: "go" "q" "pc" "cc" "c" :=
    if: "cc" ≤ #0 then #() else 
    if: recv "c" then (* enq/deq *)
      if: recv "c" then (* cont/stop *)
        "go" (qenqueue "q" (recv "c")) "pc" "cc" "c"
      else "go" "q" ("pc"-#1) "cc" "c"
    else
      if: (qis_empty "q") then
        if: "pc" ≤ #0 then
          send "c" #stop;;
          "go" "q" "pc" ("cc"-#1) "c"
        else
          send "c" #cont;; send "c" #none;;
          "go" "q" "pc" "cc" "c"
      else
        send "c" #cont;; send "c" #some;;
        let: "qv" := qdequeue "q" in
        send "c" (Snd "qv");;
        "go" (Fst "qv") "pc" "cc" "c".

Definition new_pd : val := λ: "pc" "cc",
  let: "q" := qnew #() in
  let: "c" := start_chan (λ: "c", pd_loop "q" "pc" "cc" "c") in
  let: "l" := new_lock #() in
  ("c", "l").

Definition pd_send : val := λ: "cl" "x",
  acquire (Snd "cl");;
  send (Fst "cl") #enq;; send (Fst "cl") #cont;; send (Fst "cl") "x";;
  release (Snd "cl").

Definition pd_stop : val := λ: "cl",
  acquire (Fst "cl");;
  send (Snd "cl") #enq;; send (Snd "cl") #stop;;
  release (Fst "cl").

Definition pd_recv : val :=
  rec: "go" "cl" :=
    acquire (Fst "cl");;
    send (Snd "cl") #deq;;
    if: recv (Snd "cl") then    (* cont/stop *)
       if: recv (Snd "cl") then (* some/none *)
         let: "v" := recv (Snd "cl") in
         release (Fst "cl");; SOME "v"
       else release (Fst "cl");; "go" "c" "l"
    else release (Fst "cl");; NONE.

Section sort_elem.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  Definition queue_prot : iProto Σ := (END)%proto.

  Lemma dist_queue_spec c :
    {{{ c ↣ queue_prot @ N }}}
      dist_queue (qnew #()) #0 #0 c
    {{{ RET #(); c ↣ END @ N }}}.
  Proof. Admitted.

  (* Need predicate for end of production? *)
  Definition produce_spec σ P (produce : val) :=
    ∀ vs,
    {{{ σ vs }}}
      produce #()
    {{{ v, RET v; (∃ w, ⌜v = SOMEV w⌝ ∧ P w ∗ σ (w::vs)) ∨ (⌜v = NONEV⌝) }}}.

  Definition consume_spec σ P Q (consume : val) :=
    ∀ vs, ∀ v : val,
    {{{ σ vs ∗ P v }}}
      consume v
    {{{ RET #(); σ (v::vs) ∗ Q v }}}.

  Lemma produce_consume_spec produce consume pσ cσ P Q pc cc :
    pc > 0 → cc > 0 → 
    produce_spec pσ P produce →
    consume_spec cσ P Q consume →
    {{{ pσ [] ∗ cσ [] }}}
      produce_consume produce consume #pc #cc
    {{{ vs, RET #(); pσ vs ∗ cσ vs ∗ [∗ list] v ∈ vs, Q v }}}.
  Proof. Admitted.

  (* Example producer *)
  Definition ints_to_n (l : val) (n:nat) : val:=
    λ: <>, let: "v" := !l in
           if: "v" < #n
           then l <- "v" + #1;; SOME "v"
           else NONE.

  Lemma ints_to_n_spec l n :
    produce_spec (λ vs, (∃ loc, ⌜loc = LitV $ LitLoc l⌝ ∗ l ↦ #(length vs))%I)
                 (λ v, ⌜∃ i, v = LitV $ LitInt i⌝%I) (ints_to_n #l n).
  Proof.
    iIntros (vs Φ) "Hσ HΦ".
    iDestruct "Hσ" as (loc ->) "Hσ".
    wp_lam. wp_load. wp_pures.
    case_bool_decide.
    - wp_store. wp_pures. iApply "HΦ".
      (* Does this not exist? *)
      assert (∀ n : nat, (n + 1) = (S n)). intros m. lia. rewrite H0.
      by eauto 10 with iFrame.
    - wp_pures. iApply "HΦ". by iRight.
  Qed.

  Definition consume_to_list l : val:=
    λ: "v", 
      let: "xs" := !l in
      l <- lcons "v" "xs".

  Lemma consume_to_list_spec l :
    consume_spec (λ vs, (∃ loc, ⌜loc = LitV $ LitLoc l⌝ ∗ l ↦ val_encode vs)%I)
                 (λ v, ⌜True⌝%I) (λ v, ⌜True⌝%I) (consume_to_list #l).
  Proof. Admitted.
