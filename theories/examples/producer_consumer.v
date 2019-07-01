From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From iris.heap_lang.lib Require Import spin_lock.
From osiris.utils Require Import list compare.


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

Definition dist_queue : val :=
  rec: "go" "q" "pc" "cc" "c" :=
    if: "cc" ≤ #0 then #() else 
    if: recv "c"                (* enq/deq *)
    then if: recv "c"           (* cont/stop *)
         then "go" (qenqueue "q" (recv "c")) "pc" "cc" "c"
         else "go" "q" ("pc"-#1) "cc" "c"
    else if: (qis_empty "q")
         then if: "pc" ≤ #0
              then send "c" #stop;; "go" "q" "pc" ("cc"-#1) "c"
              else send "c" #cont;; send "c" #none;; "go" "q" "pc" "cc" "c"
         else send "c" #cont;; send "c" #some;;
              let: "qv" := qdequeue "q" in
              send "c" (Snd "qv");; "go" (Fst "qv") "pc" "cc" "c".

Definition producer : val :=
  rec: "go" "c" "l" "produce" :=
    (* acquire "l";; *)
    match: "produce" #() with
      SOME "v" =>
        acquire "l";;
        send "c" #enq;; send "c" #cont;; send "c" "v";;
        release "l";;
        "go" "c" "l" "produce"
     | NONE =>
        acquire "l";;
        send "c" #enq;; send "c" #stop
        release "l"
    end.

Definition consumer : val :=
  rec: "go" "c" "l" "consume" :=
    acquire "l";;
    send "c" #deq;;
    if: recv "c"             (* cont/stop *)
    then if: recv "c"        (* some/none *)
         then let: "v" := SOME (recv "c") in
              release "l";; "consume" "v";; "go" "c" "l" "consume"
              (* "consume" "v";; release "l";; "go" "c" "l" "consume" *)
         else release "l";; "go" "c" "l" "consume"
    else "consume" NONE;; release "l";; #().
    (* else release "l";; "consume" NONE;; #(). *)

(* Makes n producers and m consumers *)
Definition produce_consume : val :=
  λ: "produce" "consume" "pc" "cc",
  #().

Section list_sort_elem.
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
