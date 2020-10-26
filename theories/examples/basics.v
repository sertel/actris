(** This file includes basic examples that each describe a unique feature of
dependent separation protocols. *)
From actris.channel Require Import proofmode.
From iris.heap_lang Require Import lib.spin_lock.
From actris.utils Require Import contribution.

(** Basic *)
Definition prog : val := λ: <>,
  let: "c" := start_chan (λ: "c'", send "c'" #42) in
  recv "c".

(** Tranfering References *)
Definition prog_ref : val := λ: <>,
  let: "c" := start_chan (λ: "c'", send "c'" (ref #42)) in
  ! (recv "c").

(** Delegation, i.e. transfering channels *)
Definition prog_del : val := λ: <>,
  let: "c1" := start_chan (λ: "c1'",
    let: "cc2" := new_chan #() in
    send "c1'" (Fst "cc2");;
    send (Snd "cc2") #42) in
  recv (recv "c1").

(** Dependent protocols *)
Definition prog_dep : val := λ: <>,
  let: "c" := start_chan (λ: "c'",
    let: "x" := recv "c'" in send "c'" ("x" + #2)) in
  send "c" #40;;
  recv "c".

Definition prog_dep_ref : val := λ: <>,
  let: "c" := start_chan (λ: "c'",
    let: "l" := recv "c'" in "l" <- !"l" + #2;; send "c'" #()) in
  let: "l" := ref #40 in send "c" "l";; recv "c";; !"l".

Definition prog_dep_del : val := λ: <>,
  let: "c1" := start_chan (λ: "c1'",
    let: "cc2" := new_chan #() in
    send "c1'" (Fst "cc2");;
    let: "x" := recv (Snd "cc2") in send (Snd "cc2") ("x" + #2)) in
  let: "c2'" := recv "c1" in send "c2'" #40;; recv "c2'".

Definition prog_dep_del_2 : val := λ: <>,
  let: "c1" := start_chan (λ: "c1'",
    send (recv "c1'") #40;;
    send "c1'" #()) in
  let: "c2" := start_chan (λ: "c2'",
    let: "x" := recv "c2'" in send "c2'" ("x" + #2)) in
  send "c1" "c2";; recv "c1";; recv "c2".

Definition prog_dep_del_3 : val := λ: <>,
  let: "c1" := start_chan (λ: "c1'",
    let: "c" := recv "c1'" in let: "y" := recv "c1'" in
    send "c" "y";; send "c1'" #()) in
  let: "c2" := start_chan (λ: "c2'",
    let: "x" := recv "c2'" in send "c2'" ("x" + #2)) in
  send "c1" "c2";; send "c1" #40;; recv "c1";; recv "c2".

(** Loops *)
Definition prog_loop : val := λ: <>,
  let: "c" := start_chan (rec: "go" "c'" :=
    let: "x" := recv "c'" in send "c'" ("x" + #2);; "go" "c'") in
  send "c" #18;;
  let: "x1" := recv "c" in
  send "c" #20;;
  let: "x2" := recv "c" in
  "x1" + "x2".

(** Transfering higher-order functions *)
Definition prog_fun : val := λ: <>,
  let: "c" := start_chan (λ: "c'",
    let: "f" := recv "c'" in send "c'" (λ: <>, "f" #() + #2)) in
  let: "r" := ref #40 in
  send "c" (λ: <>, !"r");;
  recv "c" #().

(** Lock protected channel endpoints *)
Definition prog_lock : val := λ: <>,
  let: "c" := start_chan (λ: "c'",
    let: "l" := newlock #() in
    Fork (acquire "l";; send "c'" #21;; release "l");;
    acquire "l";; send "c'" #21;; release "l") in
  recv "c" + recv "c".

(** Swapping of sends *)
Definition prog_swap : val := λ: <>,
  let: "c" := start_chan (λ: "c'",
    send "c'" #20;;
    let: "y" := recv "c'" in
    send "c'" "y") in
  send "c" #22;;
  recv "c" + recv "c".

Definition prog_swap_twice : val := λ: <>,
  let: "c" := start_chan (λ: "c'",
    send "c'" #20;;
    let: "y1" := recv "c'" in
    let: "y2" := recv "c'" in
    send "c'" ("y1" + "y2")) in
  send "c" #11;; send "c" #11;;
  recv "c" + recv "c".

Definition prog_swap_loop : val := λ: <>,
  let: "c" := start_chan (rec: "go" "c'" :=
    let: "x" := recv "c'" in send "c'" ("x" + #2);; "go" "c'") in
  send "c" #18;;
  send "c" #20;;
  let: "x1" := recv "c" in
  let: "x2" := recv "c" in
  "x1" + "x2".

Definition prog_ref_swap_loop : val := λ: <>,
  let: "c" := start_chan (rec: "go" "c'" :=
     let: "l" := recv "c'" in
     "l" <- !"l" + #2;; send "c'" #();; "go" "c'") in
  let: "l1" := ref #18 in
  let: "l2" := ref #20 in
  send "c" "l1";;
  send "c" "l2";;
  recv "c";; recv "c";;
  !"l1" + !"l2".

Section proofs.
Context `{heapG Σ, chanG Σ}.

(** Protocols for the respective programs *)
Definition prot : iProto Σ :=
  (<?> MSG #42; END)%proto.

Definition prot_ref : iProto Σ :=
  (<? (l : loc)> MSG #l {{ l ↦ #42 }}; END)%proto.

Definition prot_del : iProto Σ :=
  (<? c> MSG c {{ c ↣ prot }}; END)%proto.

Definition prot_dep : iProto Σ :=
  (<! (x : Z)> MSG #x; <?> MSG #(x + 2); END)%proto.

Definition prot_dep_ref : iProto Σ :=
  (<! (l : loc) (x : Z)> MSG #l {{ l ↦ #x }};
   <?> MSG #() {{ l ↦ #(x + 2) }};
   END)%proto.

Definition prot_dep_del : iProto Σ :=
  (<? c> MSG c {{ c ↣ prot_dep }}; END)%proto.

Definition prot_dep_del_2 : iProto Σ :=
  (<! c> MSG c {{ c ↣ prot_dep }};
   <?> MSG #() {{ c ↣ <?> MSG #42; END }};
   END)%proto.

Definition prot_dep_del_3 : iProto Σ :=
  (<! c> MSG c {{ c ↣ prot_dep }};
   <! (y : Z)> MSG #y; <?> MSG #() {{ c ↣ <?> MSG #(y + 2); END }};
   END)%proto.

Definition prot_loop_aux (rec : iProto Σ) : iProto Σ :=
  (<! (x : Z)> MSG #x; <?> MSG #(x + 2); rec)%proto.
Instance prot_loop_contractive : Contractive prot_loop_aux.
Proof. solve_proto_contractive. Qed.
Definition prot_loop : iProto Σ := fixpoint prot_loop_aux.
Global Instance prot_loop_unfold :
  ProtoUnfold prot_loop (prot_loop_aux prot_loop).
Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

Definition prot_ref_loop_aux (rec : iProto Σ) : iProto Σ :=
  (<! (l : loc) (x : Z)> MSG #l {{ l ↦ #x }}; <?> MSG #() {{ l ↦ #(x+2) }}; rec)%proto.
Instance prot_ref_loop_contractive : Contractive prot_ref_loop_aux.
Proof. solve_proto_contractive. Qed.
Definition prot_ref_loop : iProto Σ := fixpoint prot_ref_loop_aux.
Global Instance prot_ref_loop_unfold :
  ProtoUnfold prot_ref_loop (prot_ref_loop_aux prot_ref_loop).
Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

Definition prot_fun : iProto Σ :=
  (<! (P : iProp Σ) (Φ : Z → iProp Σ) (vf : val)>
     MSG vf {{ {{{ P }}} vf #() {{{ x, RET #x; Φ x }}} }};
   <? (vg : val)>
     MSG vg {{ {{{ P }}} vg #() {{{ x, RET #(x + 2); Φ x }}} }};
   END)%proto.

Fixpoint prot_lock (n : nat) : iProto Σ :=
  match n with
  | 0 => END
  | S n' => <?> MSG #21; prot_lock n'
  end%proto.

Definition prot_swap : iProto Σ :=
  (<! (x : Z)> MSG #x;
   <?> MSG #20;
   <?> MSG #x; END)%proto.

Definition prot_swap_twice : iProto Σ :=
  (<! (x : Z)> MSG #x;
   <! (y : Z)> MSG #y;
   <?> MSG #20;
   <?> MSG #(x+y); END)%proto.

Definition prot_swap_loop : iProto Σ :=
  (<! (x : Z)> MSG #x;
   <! (y : Z)> MSG #y;
   <?> MSG #(x+2);
   <?> MSG #(y+2); prot_loop)%proto.

(** Specs and proofs of the respective programs *)
Lemma prog_spec : {{{ True }}} prog #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot); iIntros (c) "Hc".
  - by wp_send with "[]".
  - wp_recv as "_". by iApply "HΦ".
Qed.

Lemma prog_ref_spec : {{{ True }}} prog_ref #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_ref); iIntros (c) "Hc".
  - wp_alloc l as "Hl". by wp_send with "[$Hl]".
  - wp_recv (l) as "Hl". wp_load. by iApply "HΦ".
Qed.

Lemma prog_del_spec : {{{ True }}} prog_del #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_del); iIntros (c) "Hc".
  - wp_apply (new_chan_spec prot with "[//]").
    iIntros (c2 c2') "[Hc2 Hc2']". wp_send with "[$Hc2]". by wp_send with "[]".
  - wp_recv (c2) as "Hc2". wp_recv as "_". by iApply "HΦ".
Qed.

Lemma prog_dep_spec : {{{ True }}} prog_dep #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_dep); iIntros (c) "Hc".
  - wp_recv (x) as "_". by wp_send with "[]".
  - wp_send with "[//]". wp_recv as "_". by iApply "HΦ".
Qed.

Lemma prog2_ref_spec : {{{ True }}} prog_dep_ref #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_dep_ref); iIntros (c) "Hc".
  - wp_recv (l x) as "Hl". wp_load. wp_store. by wp_send with "[Hl]".
  - wp_alloc l as "Hl". wp_send with "[$Hl]". wp_recv as "Hl". wp_load.
    by iApply "HΦ".
Qed.

Lemma prog_dep_del_spec : {{{ True }}} prog_dep_del #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_dep_del); iIntros (c) "Hc".
  - wp_apply (new_chan_spec prot_dep with "[//]"); iIntros (c2 c2') "[Hc2 Hc2']".
    wp_send with "[$Hc2]". wp_recv (x) as "_". by wp_send with "[]".
  - wp_recv (c2) as "Hc2". wp_send with "[//]". wp_recv as "_".
    by iApply "HΦ".
Qed.

Lemma prog_dep_del_2_spec : {{{ True }}} prog_dep_del_2 #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_dep_del_2); iIntros (c) "Hc".
  { wp_recv (c2) as "Hc2". wp_send with "[//]". by wp_send with "[$Hc2]". }
  wp_apply (start_chan_spec prot_dep); iIntros (c2) "Hc2".
  { wp_recv (x) as "_". by wp_send with "[//]". }
  wp_send with "[$Hc2]". wp_recv as "Hc2". wp_recv as "_". by iApply "HΦ".
Qed.

Lemma prog_dep_del_3_spec : {{{ True }}} prog_dep_del_3 #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_dep_del_3); iIntros (c) "Hc".
  { wp_recv (c2) as "Hc2". wp_recv (y) as "_".
    wp_send with "[//]". by wp_send with "[$Hc2]". }
  wp_apply (start_chan_spec prot_dep); iIntros (c2) "Hc2".
  { wp_recv (x) as "_". by wp_send with "[//]". }
  wp_send with "[$Hc2]". wp_send with "[//]".
  wp_recv as "Hc2". wp_recv as "_". by iApply "HΦ".
Qed.

Lemma prog_loop_spec : {{{ True }}} prog_loop #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_loop); iIntros (c) "Hc".
  - iLöb as "IH".
    wp_recv (x) as "_". wp_send with "[//]".
    do 2 wp_pure _. by iApply "IH".
  - wp_send with "[//]". wp_recv as "_". wp_send with "[//]". wp_recv as "_".
    wp_pures. by iApply "HΦ".
Qed.

Lemma prog_fun_spec : {{{ True }}} prog_fun #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_fun); iIntros (c) "Hc".
  - wp_recv (P Ψ vf) as "#Hf". wp_send with "[]"; last done.
    iIntros "!>" (Ψ') "HP HΨ'". wp_apply ("Hf" with "HP"); iIntros (x) "HΨ".
    wp_pures. by iApply "HΨ'".
  - wp_alloc l as "Hl".
    wp_send ((l ↦ #40)%I (λ w, ⌜ w = 40%Z ⌝ ∗ l ↦ #40)%I) with "[]".
    { iIntros "!>" (Ψ') "Hl HΨ'". wp_load. iApply "HΨ'"; auto. }
    wp_recv (vg) as "#Hg". wp_apply ("Hg" with "Hl"); iIntros (x) "[-> Hl]".
    by iApply "HΦ".
Qed.

Lemma prog_lock_spec `{!lockG Σ, contributionG Σ unitUR} :
  {{{ True }}} prog_lock #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec (prot_lock 2)); iIntros (c) "Hc".
  - iMod contribution_init as (γ) "Hs".
    iMod (alloc_client with "Hs") as "[Hs Hcl1]".
    iMod (alloc_client with "Hs") as "[Hs Hcl2]".
    wp_apply (newlock_spec (∃ n, server γ n ε ∗
      c ↣ iProto_dual (prot_lock n))%I
      with "[Hc Hs]"); first by eauto with iFrame.
    iIntros (lk γlk) "#Hlk".
    iAssert (client γ ε -∗
      WP acquire lk;; send c #21;; release lk {{ _, True }})%I with "[]" as "#Hhelp".
    { iIntros "Hcl".
      wp_apply (acquire_spec with "[$]"); iIntros "[Hl H]".
      iDestruct "H" as (n) "[Hs Hc]".
      iDestruct (server_agree with "Hs Hcl") as %[? _].
      destruct n as [|n]=> //=. wp_send with "[//]".
      iMod (dealloc_client with "Hs Hcl") as "Hs /=".
      wp_apply (release_spec with "[$Hlk $Hl Hc Hs]"); eauto with iFrame. }
    wp_apply (wp_fork with "[Hcl1]").
    { iNext. by iApply "Hhelp". }
    by wp_apply "Hhelp".
  - wp_recv as "_". wp_recv as "_". wp_pures. by iApply "HΦ".
Qed.

Lemma prog_swap_spec : {{{ True }}} prog_swap #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_swap); iIntros (c) "Hc".
  - wp_send with "[//]". wp_recv (x) as "_". by wp_send with "[//]".
  - wp_send with "[//]". wp_recv as "_". wp_recv as "_".
    wp_pures. by iApply "HΦ".
Qed.

Lemma prog_swap_twice_spec : {{{ True }}} prog_swap_twice #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_swap_twice); iIntros (c) "Hc".
  - wp_send with "[//]". wp_recv (x1) as "_". wp_recv (x2) as "_".
    by wp_send with "[//]".
  - wp_send with "[//]". wp_send with "[//]". wp_recv as "_". wp_recv as "_".
    wp_pures. by iApply "HΦ".
Qed.

Lemma prog_swap_loop_spec : {{{ True }}} prog_swap_loop #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_spec prot_loop); iIntros (c) "Hc".
  - iLöb as "IH".
    wp_recv (x) as "_". wp_send with "[//]".
    do 2 wp_pure _. by iApply "IH".
  - wp_send with "[//]". wp_send with "[//]". wp_recv as "_". wp_recv as "_".
    wp_pures. by iApply "HΦ".
Qed.

(** This lemma is stated as the underlying weakest precondition of the
hoare triple notation to make it equivalent to what is presented in the
Actris journal paper *)
Lemma prog_ref_swap_loop_spec : ∀ Φ, Φ #42 -∗ WP prog_ref_swap_loop #() {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ". wp_lam.
  wp_apply (start_chan_spec prot_ref_loop); iIntros (c) "Hc".
  - iLöb as "IH". wp_lam.
    wp_recv (l x) as "Hl". wp_load. wp_store. wp_send with "[$Hl]".
    do 2 wp_pure _. by iApply "IH".
  - wp_alloc l1 as "Hl1". wp_alloc l2 as "Hl2".
    wp_send with "[$Hl1]". wp_send with "[$Hl2]".
    wp_recv as "Hl1". wp_recv as "Hl2".
    wp_load. wp_load.
    wp_pures. by iApply "HΦ".
Qed.

End proofs.
