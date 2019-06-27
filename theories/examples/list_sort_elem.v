From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From osiris.utils Require Import list.

Definition list_sort_service_split : val :=
  rec: "go" "c" "c1" "c2" :=
    match: recv "c" with
      NONE => send "c1" NONE;; send "c2" NONE
    | SOME "x" => send "c1" (SOME "x");; "go" "c" "c2" "c1"
    end.

Definition list_sort_service_copy : val :=
  rec: "go" "c" "cin" :=
    match: recv "cin" with
      NONE => send "c" NONE
    | SOME "x" => send "c" (SOME "x");; "go" "c" "cin"
    end.

Definition list_sort_service_merge : val :=
  rec: "go" "cmp" "c" "x1" "c1" "c2" :=
    match: recv "c2" with
      NONE => send "c" (SOME "x1");; list_sort_service_copy "c" "c1"
    | SOME "x2" =>
       if: "cmp" "x1" "x2"
       then send "c" (SOME "x1");; "go" "cmp" "c" "x2" "c2" "c1"
       else send "c" (SOME "x2");; "go" "cmp" "c" "x1" "c1" "c2"
    end.

Definition list_sort_service : val :=
  rec: "go" "cmp" "c" :=
    match: recv "c" with
      NONE => send "c" NONE
    | SOME "x1" =>
       match: recv "c" with
         NONE => send "c" (SOME "x1");; send "c" NONE
       | SOME "x2" =>
          let: "c1" := start_chan ("go" "cmp") in
          let: "c2" := start_chan ("go" "cmp") in
          send "c1" (SOME "x1");;
          send "c2" (SOME "x2");;
          list_sort_service_split "c" "c1" "c2";;
          let: "x" := match: recv "c1" with NONE => assert #false | SOME "x" => "x" end in
          list_sort_service_merge "cmp" "c" "x" "c1" "c2"
       end
    end.

Section list_sort_elem.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  (* 
     tail xs ys n := if n > 0 then ?y.tail xs (y::ys) (n-1) else end
     helper xs n := (!x.helper (x :: xs) (S N)) <+> (tail (rev xs) [] n)
     prot = helper [] 0
   *)

  (* 
     tail xs ys n := 
       if n > 0
       then ?Some y.tail xs (y::ys) (n-1)
       else ?None{ sorted_of (rev ys) xs }.end
     
      helper xs n :=
        !v. match v with
        | Some v => helper (x :: xs) (S N))
        | None => (tail (rev xs) [] n)
        end

      prot = helper [] 0
   *)

  (* Definition test (rec : Z -d> iProto Σ) : (Z -d> iProto Σ) := *)
  (*   λ x, (<?> o (n:Z), MSG o; (rec : _ -> iProto Σ) n)%proto. *)

  (* (* No "Branching" *) *)
  (* Definition tail_protocol_aux (rec : nat -d> list Z -d> list Z -d> iProto Σ) *)
  (*   : (nat -d> list Z -d> list Z -d> iProto Σ) := *)
  (*   λ n xs ys, *)
  (*   (match n with *)
  (*    | S n => <?> (x:Z), MSG (SOMEV (LitV $ LitInt x)); rec n xs ys *)
  (*    | O   => <?> (a:unit) , *)
  (*             MSG NONEV {{ ⌜ Sorted (≤) (rev ys) ⌝ ∗ ⌜ (rev ys) ≡ₚ xs ⌝ }}; END *)
  (*    end)%proto. *)

  (* Check tail_protocol_aux. *)

  (* Instance tail_protocol_aux_contractive : Contractive (tail_protocol_aux). *)
  (* Proof. *)
  (*   intros n p p' Hp. rewrite /tail_protocol_aux. *)
  (*   intros x xs ys. simpl. *)
  (*   destruct x. *)
  (*   - done. *)
  (*   - admit. *)
  (* Admitted. *)
  
  (* Definition tail_protocol : (nat -d> list Z -d> list Z -d> iProto Σ) := fixpoint (tail_protocol_aux). *)
  (* Lemma tail_protocol_unfold : *)
  (*   tail_protocol ≡ tail_protocol_aux tail_protocol. *)
  (* Proof. apply (fixpoint_unfold tail_protocol_aux). Qed. *)

  (* (* helper n xs := *) *)
  (* (*   !v. match v with *) *)
  (* (*   | Some x => helper (x :: xs) (S N)) *) *)
  (* (*   | None => (tail n (rev xs) []) *) *)
  (* (*   end *) *)
  
  (* Definition helper_protocol_aux (rec : nat -d> list Z -d> iProto Σ) *)
  (*   : (nat -d> list Z -d> iProto Σ) := *)
  (*   λ n xs, *)
  (*   (<!> (z:Z) o, MSG o {{ ⌜o = NONEV ∨ o = SOMEV (LitV $ LitInt z)⌝ }}; *)
  (*     match o with *)
  (*     | SOMEV v => rec (S n) (z :: xs) *)
  (*     | NONEV   => tail_protocol n (rev xs) [] *)
  (*     | _ => END *)
  (*     end)%proto. *)

  
  (* "Branching" *)
  Definition tail_protocol_aux (rec : list Z -d> list Z -d> iProto Σ)
    : (list Z -d> list Z -d> iProto Σ) :=
    λ xs ys,
    (<?> (b:bool), MSG #b
        {{ if b then True else ⌜ Sorted (≤) (rev ys) ⌝ ∗ ⌜ (rev ys) ≡ₚ xs ⌝ }};
      if b
      then <?> (y:Z), MSG #y; (rec : _ -> _ -> iProto Σ) xs (y::ys)
      else END)%proto.

  Instance tail_protocol_aux_contractive : Contractive (tail_protocol_aux).
  Proof.
    intros n p p' Hp. rewrite /tail_protocol_aux.
    intros xs ys.
    apply iProto_message_ne=> b //=.
    destruct b.
    - apply iProto_message_contractive=> //=.
      intros x.
      destruct n as [|n]; simpl in *; try done. apply Hp.
    - done.
  Qed.
  
  Definition tail_protocol : (list Z -d> list Z -d> iProto Σ) := fixpoint (tail_protocol_aux).
  Lemma tail_protocol_unfold xs ys:
    tail_protocol xs ys≡ tail_protocol_aux tail_protocol xs ys.
  Proof. apply (fixpoint_unfold tail_protocol_aux). Qed.
  
  Definition helper_protocol_aux (rec : list Z -d> iProto Σ)
    : (list Z -d> iProto Σ) :=
    λ xs,
    (<!> (b:bool), MSG #b;
       if b
       then <!> (x:Z), MSG #x; (rec : _ → iProto Σ) (x::xs)
       else tail_protocol (rev xs) [])%proto.
  
  Instance helper_protocol_aux_contractive : Contractive (helper_protocol_aux).
  Proof.
    intros n p p' Hp. rewrite /helper_protocol_aux.
    intros xs.
    apply iProto_message_ne=> b //=.
    destruct b.
    - apply iProto_message_contractive=> //=.
      intros x.
      destruct n as [|n]; simpl in *; done.
    - done.
  Qed.
  
  Definition helper_protocol : (list Z -d> iProto Σ) := fixpoint (helper_protocol_aux).
  Lemma helper_protocol_unfold xs :
    helper_protocol xs ≡ helper_protocol_aux helper_protocol xs.
  Proof. apply (fixpoint_unfold helper_protocol_aux). Qed.

  Definition list_sort_elem_protocol := helper_protocol [].

End list_sort_elem.