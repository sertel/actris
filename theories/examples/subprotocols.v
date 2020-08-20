From actris.channel Require Import proofmode proto channel.
From iris.proofmode Require Import tactics.
From actris.utils Require Import llist.
From actris.examples Require Import swap_mapper.

Section basics.
  Context `{heapG Σ, chanG Σ}.

  Lemma reference_example (l2' : loc) :
    l2' ↦ #22 -∗
    (<! (l1 l2 : loc)> MSG (#l1, #l2) {{ l1 ↦ #20 ∗ l2 ↦ #22 }}; END) ⊑
    (<! (l1 : loc)> MSG (#l1, #l2') {{ l1 ↦ #20 }}; END).
  Proof. iIntros "Hl2'" (l1) "Hl1". iExists l1, l2'. by iFrame "Hl1 Hl2'". Qed.

  Lemma framing_example (P Q R : iProp Σ) (v w : val) :
    ⊢ ((<!> MSG v {{ P }} ; <?> MSG w {{ Q }}; END)%proto ⊑
       (<!> MSG v {{ P ∗ R }} ; <?> MSG w {{ Q ∗ R }};END)%proto)%proto.
  Proof.
    iIntros "[HP HR]". iFrame "HP". iModIntro.
    iIntros "HQ". iFrame "HQ HR". eauto.
  Qed.

  Section program_reuse.
    Context {T U R : Type}.
    Context (IT : T -> val -> iProp Σ).
    Context (ITR : (T * R) -> val -> iProp Σ).
    Context (IU : U -> val -> iProp Σ).
    Context (IUR : (U * R) -> val -> iProp Σ).
    Context (IR : R -> iProp Σ).
    Context (f : T -> U).

    Axiom HIT : ∀ v t r, ITR (t,r) v -∗ IT t v ∗ IR r.
    Axiom HIU : ∀ v u r, (IU u v ∗ IR r) -∗ IUR (u,r) v.

    Lemma example prot prot' :
      ▷ (prot ⊑ prot') -∗
           (<! (x : T) (v : val)> MSG v {{ IT x v }};
           <? (w : val)> MSG w {{ IU (f x) w }}; prot) ⊑
           (<! (x : T * R) (v : val)> MSG v {{ ITR x v }};
           <? (w : val)> MSG w {{ IUR (f x.1,x.2) w }}; prot').
    Proof.
      iIntros "Hprot".
      iIntros ([t r] v) "HTR".
      iDestruct (HIT with "HTR") as "[HT HR]".
      iExists t,v. iFrame "HT".
      iModIntro.
      iIntros (w) "HU". iDestruct (HIU with "[$HR $HU]") as "HUR".
      iExists w. iFrame "HUR".
      iModIntro. iApply "Hprot".
    Qed.

    Lemma mapper_prot_reuse_example :
      ⊢ mapper_prot IT IU f ⊑ mapper_prot ITR IUR (λ tr, (f tr.1, tr.2)).
    Proof.
      iLöb as "IH".
      iEval (rewrite /mapper_prot).
      rewrite (fixpoint_unfold (mapper_prot_aux IT _ _)).
      rewrite (fixpoint_unfold (mapper_prot_aux ITR _ _)).
      rewrite {1 3}/mapper_prot_aux.
      rewrite /iProto_choice.
      iIntros (b). iExists (b).
      destruct b=> //. iModIntro.
      iApply example. iApply "IH".
    Qed.

  End program_reuse.

End basics.
