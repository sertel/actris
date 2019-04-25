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

Inductive stype' (A : Type) :=
| TEnd'
| TSR' {V : Type} {EV : Encodable V} {DV : Decodable V}
       (a : action) (P : V → A) (st : V → stype' A).
Arguments TEnd' {_}.
Arguments TSR' {_ _ _ _} _ _ _.
Instance: Params (@TSR') 4.

Fixpoint dual_stype' {A} (st : stype' A) :=
  match st with
  | TEnd' => TEnd'
  | TSR' a P st => TSR' (dual_action a) P (λ v, dual_stype' (st v))
  end.
Instance: Params (@dual_stype') 2.
Arguments dual_stype : simpl never.

Section Encodings.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG val Σ}.

  Example ex_st : stype' (iProp Σ) :=
    (TSR' Receive
          (λ v', ⌜v' = 5⌝%I)
          (λ v', TEnd')).

  Example ex_st2 : stype' (iProp Σ) :=
    TSR' Send
         (λ b, ⌜b = true⌝%I)
         (λ b,
          (TSR' Receive
              (λ v', ⌜(v' > 5) = b⌝%I)
              (λ _, TEnd'))).

  Fixpoint stype'_to_stype (st : stype' (iProp Σ)) : stype val (iProp Σ) :=
    match st with
    | TEnd' => TEnd
    | TSR' a P st =>
      TSR a
          (λ v, match decode v with
                | Some v => P v
                | None => False
                end%I)
          (λ v, match decode v with
                | Some v => stype'_to_stype (st v)
                | None => TEnd
                end)
    end.
  Global Instance: Params (@stype'_to_stype) 1.
  Global Arguments stype'_to_stype : simpl never.

  Lemma dual_stype'_comm st :
    stype'_to_stype (dual_stype' st) ≡ dual_stype (stype'_to_stype st).
  Proof.
    induction st.
    - by simpl.
    - unfold stype'_to_stype. simpl.
      constructor.
      + intros v. eauto.
      + intros v. destruct (decode v); eauto.
  Qed.

  Notation "⟦ c @ s : sτ ⟧{ γ }" := (interp_st N γ sτ c s)
    (at level 10, s at next level, sτ at next level, γ at next level,
     format "⟦  c  @  s  :  sτ  ⟧{ γ }").

  Lemma new_chan_st_enc_spec st :
    {{{ True }}}
      new_chan #()
    {{{ c γ, RET c; ⟦ c @ Left : (stype'_to_stype st) ⟧{γ} ∗
                    ⟦ c @ Right : (stype'_to_stype (dual_stype' st)) ⟧{γ} }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    iApply (new_chan_st_spec). eauto.
    iNext.
    iIntros (c γ) "[Hl Hr]".
    iApply "HΦ".
    iFrame.
    iDestruct "Hr" as "[Hown Hctx]".
    iFrame.
    unfold st_own. simpl.
    iApply (own_mono with "Hown").
    apply (auth_frag_mono).
    apply Some_included.
    left.
    f_equiv.
    f_equiv.
    apply stype_map_equiv=> //.
    apply dual_stype'_comm.
  Qed.

  Lemma send_st_enc_spec (A : Type) `{Encodable A} `{Decodable A} `{EncDec A}
        st γ c s (P : A → iProp Σ) w :
    {{{ P w ∗ ⟦ c @ s : (stype'_to_stype (TSR' Send P st)) ⟧{γ} }}}
      send c #s (encode w)
    {{{ RET #(); ⟦ c @ s : stype'_to_stype (st w) ⟧{γ} }}}.
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

  Lemma recv_st_enc_spec (A : Type) `{EncDec A}
        st γ c s (P : A → iProp Σ) :
    {{{ ⟦ c @ s : (stype'_to_stype (TSR' Receive P st)) ⟧{γ} }}}
      recv c #s
    {{{ v, RET (encode v); ⟦ c @ s : stype'_to_stype (st v) ⟧{γ} ∗ P v }}}.
  Proof.
    iIntros (Φ) "Hrecv HΦ".
    iApply (recv_st_spec with "Hrecv").
    iNext. iIntros (v). (* iSpecialize ("HΦ" $!v). *)
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

End Encodings.