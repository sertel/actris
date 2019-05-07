From iris.heap_lang Require Import proofmode notation.

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

(* Common Functional structures *)
Instance pair_encodable `{Encodable A, Encodable B} : Encodable (A * B) :=
  λ p, (encode p.1, encode p.2)%V.

Instance option_encodable `{Encodable A} : Encodable (option A) := λ mx,
  match mx with Some x => SOMEV (encode x) | None => NONEV end%V.
