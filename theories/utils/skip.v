From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.

Definition skipN : val :=
  rec: "go" "n" := if: #0 < "n" then "go" ("n" - #1) else #().

Lemma skipN_spec `{heapG Σ} Φ (n : nat) : ▷^n (Φ #()) -∗ WP skipN #n {{ Φ }}.
Proof.
  iIntros "HΦ". iInduction n as [|n] "IH"; wp_rec; wp_pures; [done|].
  rewrite Z.sub_1_r Nat2Z.inj_succ Z.pred_succ. by iApply "IH".
Qed.
