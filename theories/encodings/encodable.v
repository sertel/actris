From iris.heap_lang Require Import proofmode notation.

Class Encodable A := encode : A -> val.
Class Decodable A := decode : val -> option A.
Class EncDec (A : Type) {EA : Encodable A} {DA : Decodable A} :=
{
  encdec : ∀ v, decode (encode v) = Some v;
  decenc : ∀ (v : val) (w : A) , decode v = Some w -> encode w = v
}.

Ltac solve_encdec := intros v; by unfold decode, encode.
Ltac solve_decenc :=
  intros ?v ?w ?H;
  destruct v as [?l | | | | ]; try by inversion H;
  destruct l; try by inversion H.
Ltac solve_encdec_decenc :=
  split; [solve_encdec | solve_decenc].

(* Instances *)
Instance val_encodable : Encodable val := id.
Instance val_decodable : Decodable val := id $ Some.
Instance val_encdec : EncDec val.
Proof.
  split.
  - intros v. unfold decode, encode. eauto.
  - intros v w H. by destruct v; inversion H.
Qed.

Instance int_encodable : Encodable Z := λ n, #n.
Instance int_decodable : Decodable Z :=
  λ v, match v with
       | LitV (LitInt z) => Some z
       | _ => None
       end.
Instance int_encdec : EncDec Z.
Proof. solve_encdec_decenc. Qed.

Instance bool_encodable : Encodable bool := λ b, #b.
Instance bool_decodable : Decodable bool :=
  λ v, match v with
       | LitV (LitBool b) => Some b
       | _ => None
       end.
Instance bool_encdec : EncDec bool.
Proof. solve_encdec_decenc. Qed.

Instance loc_encodable : Encodable loc := λ l, #l.
Instance loc_decodable : Decodable loc :=
  λ v, match v with
       | LitV (LitLoc l) => Some l
       | _ => None
       end.
Instance loc_encdec : EncDec loc.
Proof. solve_encdec_decenc. Qed.

Instance unit_encodable : Encodable unit := λ _, #().
Instance unit_decodable : Decodable unit :=
  λ v, match v with
       | LitV (LitUnit) => Some ()
       | _ => None
       end.
Instance unit_encdec : EncDec unit.
Proof.
  split.
  - intros v. destruct v. by unfold decode, encode.
  - solve_decenc.
Qed.

Instance pair_encodable `{Encodable A, Encodable B} : Encodable (A * B) :=
  λ p, (encode p.1, encode p.2)%V.
Instance pair_decodable `{Decodable A, Decodable B} : Decodable (A * B) :=
  λ v, match v with
       | PairV v1 v2 => match decode v1, decode v2 with
                        | Some v1, Some v2 => Some (v1, v2)
                        | _, _ => None
                        end
       | _ => None
       end.
Instance pair_encdec `{EncDec A, EncDec B} : EncDec (A * B).
Proof.
  split.
  - intros v. destruct v. unfold decode, encode. simpl.
    rewrite encdec. rewrite encdec. reflexivity.
  - intros v w Heq. destruct w.
    unfold decode, encode in *.
    unfold pair_encodable, pair_decodable in *. simpl.
    destruct v; inversion Heq.
    by f_equiv;
    apply decenc;
    destruct (decode v1); inversion Heq;
    destruct (decode v2); inversion Heq.
Qed.

Instance option_encodable `{Encodable A} : Encodable (option A) := λ mx,
  match mx with Some x => SOMEV (encode x) | None => NONEV end%V.
Instance option_decodable `{Decodable A} : Decodable (option A) :=
  λ v, match v with
       | SOMEV v => match decode v with
                    | Some v => Some (Some v)
                    | None => None
                    end
       | NONEV => Some (None)
       | _ => None
       end.
Instance option_encdec `{EncDec A} : EncDec (option A).
Proof.
  split.
  - intros v. unfold decode, encode.
    destruct v; simpl. rewrite encdec. eauto. eauto.
  - intros v w Heq.
    destruct w.
    + unfold decode, encode in *.
      unfold option_encodable, option_decodable in *.
      destruct v; inversion Heq.
      destruct v; inversion Heq.
      destruct l; inversion Heq.
      f_equiv.
      apply decenc.
        by destruct (decode v); inversion Heq.
    + unfold decode, encode in *.
      simpl.
      unfold option_encodable, option_decodable in *.
      destruct v; inversion Heq.
      * destruct v; inversion Heq.
        destruct l; inversion Heq.
        eauto.
      * destruct (decode v); inversion Heq.
Qed.

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

Lemma enc_inj {A : Type} `{ED : EncDec A}
      x y : encode x = encode y -> x = y.
Proof.
  intros Heq.
  assert (decode (encode x) = decode (encode y)).
  { by f_equiv. }
  erewrite encdec in H=> //.
  erewrite encdec in H=> //.
  by inversion H.
Qed.