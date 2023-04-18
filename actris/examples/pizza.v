From iris.heap_lang Require Import lib.spin_lock lib.par.
From actris.utils Require Import llist.
From actris.channel Require Import proofmode.
From stdpp Require Import list.

Inductive pizza :=
  | Margherita
  | Calzone.

Section example.
  Context `{heapGS Σ, chanG Σ, spawnG Σ}.

  Definition pizza_to_val (p : pizza) :=
    match p with
    | Margherita => #0
    | Calzone => #1
    end.

  Fixpoint list_to_val {T} (f : T → val) (xs : list T) :=
    match xs with
    | [] => NONEV
    | x::xs => SOMEV ((f x), (list_to_val f xs))%V
    end.

  Notation pizza_list_to_val := (list_to_val pizza_to_val).

  Fixpoint is_list {T} (f : T → val) (v : val) (ws : list T) : iProp Σ :=
    match ws with
    | []    => ⌜v = NONEV⌝
    | w::ws => ∃ (v' : val), ⌜v = SOMEV ((f w), v')%V⌝ ∗ is_list f v' ws
  end.

  Notation is_int_list := (is_list (λ v, LitV $ LitInt $ v)).
  Notation is_pizza_list := (is_list pizza_to_val).

  Lemma is_pizza_list_pizzas pizzas :
    ⊢ is_pizza_list (pizza_list_to_val pizzas) pizzas.
  Proof. induction pizzas; [eauto | iExists _; eauto]. Qed.

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
    {{{ RET #(int_list_sum xs); True }}}.
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

  Definition order_pizza (pizzas : list pizza) : val :=
    λ: "cc" "c",
    send "c" (pizza_list_to_val pizzas);;
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

  Lemma order_pizza_spec pizzas c cc (x1 : Z) :
    {{{ c ↣ pizza_prot ∗ cc ↦ #x1 }}}
      order_pizza pizzas #cc c
    {{{ (x2 : Z), RET (#x2, #(x1 - x2))%V;
        c ↣ pizza_prot ∗ cc ↦ #(x1 - x2)%Z }}}.
  Proof.
    iIntros (Φ) "[Hc Hcc] HΦ".
    wp_lam.
    wp_send (_ pizzas) with "[]".
    { iApply is_pizza_list_pizzas. }
    wp_send with "[Hcc //]".
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
    λ: "jesper_cc" "robbert_cc" "c",
    let: "lk" := newlock #() in
    (
      (acquire "lk";;
       let: "v1" := order_pizza [Margherita] "jesper_cc" "c" in
       release "lk";;
       "v1")
      |||
      (acquire "lk";;
       let: "v2" := order_pizza [Calzone] "robbert_cc" "c" in
       release "lk";;
       "v2")
    ).

  Lemma lock_example_spec jcc rcc c (x1 y1 : Z) :
    {{{ c ↣ pizza_prot ∗ jcc ↦ #x1 ∗ rcc ↦ #y1 }}}
      lock_example #jcc #rcc c
    {{{ (x2 y2 : Z), RET ((#x2, #(x1 - x2)), (#y2, #(y1 - y2)))%V;
        jcc ↦ #(x1 - x2) ∗ rcc ↦ #(y1 - y2) }}}.
  Proof.
    iIntros (Φ) "[Hc [Hjcc Hrcc]] HΦ".
    wp_lam. wp_pures.
    wp_apply (newlock_spec with "Hc").
    iIntros (lk γ) "#Hlk".
    wp_pures.
    wp_apply (wp_par (λ v, ∃ (x2:Z), ⌜v = (#x2, #(x1 - x2))%V⌝ ∗
                                     jcc ↦ #(x1 - x2)%Z)%I
                     (λ v, ∃ (y2:Z), ⌜v = (#y2, #(y1 - y2))%V⌝ ∗
                                     rcc ↦ #(y1 - y2)%Z)%I
                with "[Hjcc] [Hrcc]").
    - wp_pures.
      wp_apply (acquire_spec with "Hlk").
      iIntros "[Hlocked Hc]".
      wp_pures. wp_apply (order_pizza_spec with "[$Hc $Hjcc]").
      iIntros (x2) "[Hc Hjcc]".
      wp_pures.
      wp_apply (release_spec with "[$Hlk $Hlocked $Hc]").
      iIntros "_".
      wp_pures.
      eauto.
    - wp_pures.
      wp_apply (acquire_spec with "Hlk").
      iIntros "[Hlocked Hc]".
      wp_pures. wp_apply (order_pizza_spec with "[$Hc $Hrcc]").
      iIntros (y2) "[Hc Hrcc]".
      wp_pures.
      wp_apply (release_spec with "[$Hlk $Hlocked $Hc]").
      iIntros "_".
      wp_pures.
      eauto.
    - iIntros (v1 v2) "[HΨ1 HΨ2]".
      iIntros "!>".
      iDestruct "HΨ1" as (x2) "[-> HΨ1]".
      iDestruct "HΨ2" as (y2) "[-> HΨ2]".
      iApply ("HΦ" with "[$HΨ1 $HΨ2]").
  Qed.

End example.
