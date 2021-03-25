From iris.heap_lang Require Import lib.spin_lock lib.par.
From actris.utils Require Import llist.
From actris.channel Require Import proofmode.
From stdpp Require Import list.

Inductive pizza :=
  | Margherita
  | Calzone.

Section example.
  Context `{heapG Σ, chanG Σ, spawnG Σ}.

  Definition pizza_to_val (p : pizza) :=
    match p with
    | Margherita => #true
    | Calzone => #false
    end.

  Fixpoint list_to_val {T} (f : T -> val) (xs : list T) :=
    match xs with
    | [] => NONEV
    | x::xs => SOMEV (PairV (f x) (list_to_val f xs))
    end.

  Definition pizza_list_to_val := list_to_val pizza_to_val.

  Fixpoint is_list {T} (f : T -> val) (v : val) (ws : list T) : iProp Σ :=
    match ws with
    | []    => ⌜v = NONEV⌝
    | w::ws => ∃ (v' : val), ⌜v = SOMEV (PairV (f w) v')⌝ ∗ is_list f v' ws
  end.

  Definition is_int_list : val → list Z → iProp Σ :=
    is_list (λ v, LitV $ LitInt $ v).

  Definition is_pizza_list : val → list pizza → iProp Σ :=
    is_list pizza_to_val.

  Fixpoint int_list_sum (xs : list Z) : Z :=
    match xs with
    | []    => 0
    | x::xs => x + int_list_sum xs
    end.

  Definition sum_list : val :=
    rec: "go" "xs" :=
      match: "xs" with
        NONE => #0
      | SOME "xs" => Fst "xs" + "go" (Snd "xs")
      end.

  Lemma sum_list_spec v xs :
    {{{ is_int_list v xs }}}
      sum_list v
    {{{ RET #(int_list_sum xs)%Z; True }}}.
  Proof.
    unfold is_int_list.
    iIntros (Φ) "Hxs HΦ".
    iInduction xs as [|x xs] "IH" forall (v Φ).
    - wp_rec. iDestruct "Hxs" as "->".
      wp_pures. by iApply "HΦ".
    - wp_rec. unfold is_int_list. simpl.
      iDestruct "Hxs" as (v') "[-> Hrec]".
      wp_pures.
      wp_apply ("IH" with "Hrec").
      iIntros "_". wp_pures.
      by iApply "HΦ".
  Qed.

  Definition order_pizza : val :=
    λ: "cc" "c",
    send "c" (pizza_list_to_val [Margherita; Calzone]);;
    send "c" "cc";;
    let: "receipt" := recv "c" in
    (sum_list "receipt", !"cc").

  Definition pizza_prot_aux (rec : iProto Σ) : iProto Σ :=
    (<! (v1 : val) (xs1 : list pizza)> MSG v1 {{ is_pizza_list v1 xs1 }} ;
     <! (l : loc) (x : Z)> MSG #l {{ l ↦ #x }};
     <? (v2 : val) (xs2 : list Z)> MSG v2 {{ is_int_list v2 xs2 ∗
                                             ⌜Zlength xs1 = Zlength xs2⌝ ∗
                                             l ↦ #(x - int_list_sum xs2)%Z }};
    rec)%proto.

  Instance pizza_prot_aux_contractive : Contractive pizza_prot_aux.
  Proof. solve_proto_contractive. Qed.

  Definition pizza_prot := fixpoint pizza_prot_aux.
  Global Instance pizza_prot_unfold :
    ProtoUnfold pizza_prot (pizza_prot_aux pizza_prot).
  Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

  Lemma order_pizza_spec c cc (x : Z) :
    {{{ c ↣ pizza_prot ∗ cc ↦ #x }}}
      order_pizza #cc c
    {{{ (y x2 : Z), RET PairV #y #x2;
        c ↣ pizza_prot ∗ cc ↦ #x2 ∗ ⌜x2 = (x - y)%Z⌝ }}}.
  Proof.
    iIntros (Φ) "[Hc Hcc] HΦ".
    wp_lam.
    wp_send (_ [Margherita; Calzone]) with "[]".
    { unfold is_pizza_list. simpl. eauto. }
    wp_send with "[Hcc]"=> //.
    wp_recv (v2 xs2) as "[Hxs2 [_ Hcc]]".
    wp_load.
    wp_apply (sum_list_spec with "Hxs2").
    iIntros "_".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    eauto with iFrame.
  Qed.


  Definition lock_example : val :=
    λ: "c",
    let: "lk" := newlock #() in
    (
      (let: "jesper_cc" := ref #0 in
       acquire "lk";;
       send "c" (pizza_list_to_val [Margherita]);;
       send "c" "jesper_cc";;
       let: "jesper_receipt" := recv "c" in
       "jesper_receipt")
      |||
      (let: "robbert_cc" := ref #0 in
       acquire "lk";;
       send "c" (pizza_list_to_val [Calzone]);;
       send "c" "robbert_cc";;
       let: "robbert_receipt" := recv "c" in
       "robbert_receipt")
    ).

  Lemma lock_example_spec c :
    {{{ c ↣ pizza_prot }}}
      lock_example c
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_lam.
    wp_apply (newlock_spec with "Hc").
    iIntros (lk γ) "#Hlk".
    wp_pures.
    wp_apply wp_par.
    - wp_alloc cc as "Hcc".
      wp_pures.
      wp_apply (acquire_spec with "Hlk").
      iIntros "[Hlocked Hc]".
      wp_send (_ [Margherita]) with "[]".
      { eauto. }
      wp_send with "[Hcc]"=> //.
      wp_recv (v2 xs2) as "[Hxs2 [_ Hcc]]".
      wp_pures. eauto.
    - wp_alloc cc as "Hcc".
      wp_pures.
      wp_apply (acquire_spec with "Hlk").
      iIntros "[Hlocked Hc]".
      wp_send (_ [Calzone]) with "[]".
      { eauto. }
      wp_send with "[Hcc]"=> //.
      wp_recv (v2 xs2) as "[Hxs2 [_ Hcc]]".
      wp_pures. eauto.
    - iIntros (v1 v2) "[_ _]".
      by iApply "HΦ".
  Qed.

End example.
