From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants.
From osiris.encodings Require Export stype.

Class Encodable A := encode : A -> val.
Instance val_encodable : Encodable val := id.
Instance int_encodable : Encodable Z := λ n, #n.
Instance bool_encodable : Encodable bool := λ b, #b.
Instance unit_encodable : Encodable unit := λ _, #().
Instance loc_encodable : Encodable loc := λ l, #l.

Class Decodable A := decode : val -> option A.
Instance val_decodable : Decodable val := id $ Some.
Instance int_decodable : Decodable Z :=
  λ v, match v with
       | LitV (LitInt z) => Some z
       | _ => None
       end.
Instance bool_decodable : Decodable bool :=
  λ v, match v with
       | LitV (LitBool b) => Some b
       | _ => None
       end.
Instance loc_decodable : Decodable loc :=
  λ v, match v with
       | LitV (LitLoc l) => Some l
       | _ => None
       end.

Class EncDec (A : Type) {EA : Encodable A} {DA : Decodable A} :=
{
  encdec : ∀ v, decode (encode v) = Some v;
  decenc : ∀ (v : val) (w : A) , decode v = Some w -> encode w = v
}.

Ltac solve_encdec := intros v; by unfold decode, encode.
Ltac solve_decenc :=
  intros v w H;
  destruct v as [l | | | | ]; try by inversion H;
  destruct l; try by inversion H.

Ltac solve_encdec_decenc :=
  split; [solve_encdec | solve_decenc].

Instance val_encdec : EncDec val.
Proof.
  split.
  - intros v. unfold decode, encode. eauto.
  - intros v w H. by destruct v; inversion H.
Qed.
Instance int_encdec : EncDec Z.
Proof. solve_encdec_decenc. Qed.
Instance bool_encdec : EncDec bool.
Proof. solve_encdec_decenc. Qed.
Instance loc_encdec : EncDec loc.
Proof. solve_encdec_decenc. Qed.

Lemma enc_dec {A : Type} `{ED : EncDec A}
      v (w : A) : encode w = v <-> decode v = Some w.
Proof.
  split.
  - intros.
    rewrite -encdec.
    rewrite -H.
    reflexivity.
  - intros.
    apply decenc. eauto.
Qed.

Section DualStypeEnc.
  Context `{EncDec V} `{PROP: bi} .

  Definition TSR'
    (a : action) (P : V → PROP) (st : V → stype val PROP) : stype val PROP :=
  TSR a
    (λ v, if decode v is Some x then P x else False)%I
    (λ v, if decode v is Some x then st x else TEnd (* dummy *)).
  Global Instance: Params (@TSR') 3.

  Global Instance is_dual_tsr' a1 a2 P (st1 st2 : V → stype val PROP) :
    IsDualAction a1 a2 →
    (∀ x, IsDualStype (st1 x) (st2 x)) →
    IsDualStype (TSR' a1 P st1) (TSR' a2 P st2).
  Proof.
    rewrite /IsDualAction /IsDualStype. intros <- Hst.
    constructor=> x. done. by destruct (decode x).
  Qed.

End DualStypeEnc.

Notation TSend := (TSR' Send).
Notation TReceive := (TSR' Receive).

Section stype_enc_specs.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG val Σ}.

  Lemma send_st_spec (A : Type) `{EncDec A}
        st γ c s (P : A → iProp Σ) w :
    {{{ P w ∗ ⟦ c @ s : (TSend P st) ⟧{N,γ} }}}
      send c #s (encode w)
    {{{ RET #(); ⟦ c @ s : st w ⟧{N,γ} }}}.
  Proof.
    iIntros (Φ) "[HP Hsend] HΦ".
    iApply (send_st_spec with "[HP Hsend]").
    simpl.
    iFrame.
    by rewrite encdec.
    iNext.
    rewrite encdec.
    by iApply "HΦ".
  Qed.

  Lemma recv_st_spec (A : Type) `{EncDec A}
        st γ c s (P : A → iProp Σ) :
    {{{ ⟦ c @ s : (TReceive P st) ⟧{N,γ} }}}
      recv c #s
    {{{ v, RET (encode v); ⟦ c @ s : st v ⟧{N,γ} ∗ P v }}}.
  Proof.
    iIntros (Φ) "Hrecv HΦ".
    iApply (recv_st_spec with "Hrecv").
    iNext. iIntros (v).
    iIntros "[H HP]".
    iAssert ((∃ w, ⌜decode v = Some w⌝ ∗ P w)%I) with "[HP]" as (w Hw) "HP".
    { destruct (decode v).
      iExists a. by iFrame. iDestruct "HP" as %HP=>//. }
    iSpecialize ("HΦ" $!w).
    apply enc_dec in Hw. rewrite Hw.
    iApply "HΦ".
    iFrame.
    apply enc_dec in Hw.
    destruct (decode v).
    - inversion Hw. subst. iApply "H".
    - inversion Hw.
  Qed.

End stype_enc_specs.