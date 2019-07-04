From iris.heap_lang Require Export notation.

Class ValEnc A := val_encode : A → val.
Class ValDec A := val_decode : val → option A.
Class ValEncDec A `{!ValEnc A, !ValDec A} := {
  val_encode_decode v : val_decode (val_encode v) = Some v;
  val_decode_encode v x : val_decode v = Some x → val_encode x = v;
}.

Local Arguments val_encode _ _ !_ /.
Local Arguments val_decode _ _ !_ /.

Lemma val_encode_decode_iff `{ValEncDec A} v x :
  val_encode x = v ↔ val_decode v = Some x.
Proof.
  split; last apply val_decode_encode. intros <-. by rewrite -val_encode_decode.
Qed.
Instance val_encode_inj `{ValEncDec A} : Inj (=) (=) val_encode.
Proof.
  intros x y Heq. apply (inj Some).
  by rewrite -(val_encode_decode x) Heq val_encode_decode.
Qed.

(* Instances *)
Instance val_val_enc : ValEnc val := id.
Instance val_val_dec : ValDec val := id $ Some.
Instance val_val_enc_dec : ValEncDec val.
Proof. split. done. by intros ?? [= ->]. Qed.

Instance int_val_enc : ValEnc Z := λ n, #n.
Instance int_val_dec : ValDec Z := λ v,
  match v with LitV (LitInt z) => Some z | _ => None end.
Instance int_val_enc_dec : ValEncDec Z.
Proof. split. done. by intros [[]| | | |] ? [= ->]. Qed.

Instance bool_val_enc : ValEnc bool := λ b, #b.
Instance bool_val_dec : ValDec bool := λ v,
  match v with LitV (LitBool b) => Some b | _ => None end.
Instance bool_val_enc_dec : ValEncDec bool.
Proof. split. done. by intros [[]| | | |] ? [= ->]. Qed.

Instance loc_val_enc : ValEnc loc := λ l, #l.
Instance loc_val_dec : ValDec loc := λ v,
  match v with LitV (LitLoc l) => Some l | _ => None end.
Instance loc_val_enc_dec : ValEncDec loc.
Proof. split. done. by intros [[]| | | |] ? [= ->]. Qed.

Instance unit_val_enc : ValEnc unit := λ _, #().
Instance unit_val_dec : ValDec unit := λ v,
  match v with LitV LitUnit => Some () | _ => None end.
Instance unit_val_enc_dec : ValEncDec unit.
Proof. split. by intros []. by intros [[]| | | |] ? [= <-]. Qed.

Instance pair_val_enc `{ValEnc A, ValEnc B} : ValEnc (A * B) := λ p,
  (val_encode p.1, val_encode p.2)%V.
Arguments pair_val_enc {_ _ _ _} !_ /.
Instance pair_val_dec `{ValDec A, ValDec B} : ValDec (A * B) := λ v,
  match v with
  | PairV v1 v2 => x1 ← val_decode v1; x2 ← val_decode v2; Some (x1, x2)
  | _ => None
  end.
Arguments pair_val_dec {_ _ _ _} !_ /.
Instance pair_val_enc_dec `{ValEncDec A, ValEncDec B} : ValEncDec (A * B).
Proof.
  split.
  - intros []. by rewrite /= val_encode_decode /= val_encode_decode.
  - intros [] ??; simplify_option_eq;
      by repeat match goal with
      | H : val_decode _ = Some _ |- _ => apply val_decode_encode in H as <-
      end.
Qed.

Instance option_val_enc `{ValEnc A} : ValEnc (option A) := λ mx,
  match mx with Some x => SOMEV (val_encode x) | None => NONEV end%V.
Arguments option_val_enc {_ _} !_ /.
Instance option_val_dec `{ValDec A} : ValDec (option A) := λ v,
  match v with
  | SOMEV v => x ← val_decode v; Some (Some x)
  | NONEV => Some None
  | _ => None
  end.
Arguments option_val_dec {_ _} !_ /.
Instance option_val_enc_dec `{ValEncDec A} : ValEncDec (option A).
Proof.
  split.
  - intros []=> //. by rewrite /= val_encode_decode.
  - intros [] ??; repeat (simplify_option_eq || case_match);
      by repeat match goal with
      | H : val_decode _ = Some _ |- _ => apply val_decode_encode in H as <-
      end.
Qed.
