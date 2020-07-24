From actris.channel Require Import proofmode proto channel.
From iris.proofmode Require Import tactics.
From actris.utils Require Import llist.

Section basics.
  Context `{heapG Σ, chanG Σ}.

  Lemma reference_example (l2' : loc) :
    l2' ↦ #22 -∗
    (<! (l1 l2 : loc)> MSG (#l1, #l2) {{ l1 ↦ #20 ∗ l2 ↦ #22 }}; END) ⊑
    (<! (l1 : loc)> MSG (#l1, #l2') {{ l1 ↦ #20 }}; END).
  Proof. iIntros "Hl2'" (l1) "Hl1". iExists l1, l2'. by iFrame "Hl1 Hl2'". Qed.

  Section program_reuse.
    Context {T U R : Type}.
    Context (IT : T -> val -> iProp Σ).
    Context (ITR : (T * R) -> val -> iProp Σ).
    Context (IU : U -> val -> iProp Σ).
    Context (IUR : (U * R) -> val -> iProp Σ).
    Context (IR : R -> iProp Σ).

    Axiom HIT : ∀ v t r, ITR (t,r) v -∗ IT t v ∗ IR r.
    Axiom HIU : ∀ v u r, (IU u v ∗ IR r) -∗ IUR (u,r) v.

    Lemma example :
      ⊢ (<! (v : val) (t : T)> MSG v {{ IT t v }};
         <? (w : val) (u : U)> MSG w {{ IU u w }}; END) ⊑
        (<! (v : val) (t : T) (r: R)> MSG v {{ ITR (t,r) v }};
         <? (w : val) (u : U)> MSG w {{ IUR (u,r) w }}; END).
    Proof.
      iIntros (v t r) "HTR".
      iDestruct (HIT with "HTR") as "[HT HR]".
      iExists v, t. iFrame "HT".
      iModIntro.
      iIntros (w u) "HU".
      iDestruct (HIU with "[$HR $HU]") as "HUR".
      iExists w, u. iFrame "HUR".
      eauto.
    Qed.
  End program_reuse.

End basics.
