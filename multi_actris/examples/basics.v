From multi_actris.channel Require Import proofmode.
Set Default Proof Using "Type".

Definition iProto_empty {Σ} : list (iProto Σ) := [].

Lemma iProto_consistent_empty {Σ} :
  ⊢ iProto_consistent (@iProto_empty Σ).
Proof. iProto_consistent_take_steps. Qed.

Definition iProto_binary `{!heapGS Σ} : list (iProto Σ) :=
  [(<(Send, 1) @ (x:Z)> MSG #x ; END)%proto;
   (<(Recv, 0) @ (x:Z)> MSG #x ; END)%proto].

Lemma iProto_binary_consistent `{!heapGS Σ} :
  ⊢ iProto_consistent iProto_binary.
Proof. rewrite /iProto_binary. iProto_consistent_take_steps. Qed.

Definition roundtrip_prog : val :=
  λ: <>,
     let: "cs" := new_chan #3 in
     let: "c0" := get_chan "cs" #0 in
     let: "c1" := get_chan "cs" #1 in
     let: "c2" := get_chan "cs" #2 in
     Fork (let: "x" := recv "c1" #0 in send "c1" #2 "x");;
     Fork (let: "x" := recv "c2" #1 in send "c2" #0 "x");;
     send "c0" #1 #42;; recv "c0" #2.

Section channel.
  Context `{!heapGS Σ, !chanG Σ}.

  Definition iProto_roundtrip : list (iProto Σ) :=
     [(<(Send, 1) @ (x:Z)> MSG #x ; <(Recv, 2)> MSG #x; END)%proto;
      (<(Recv, 0) @ (x:Z)> MSG #x ; <(Send, 2)> MSG #x; END)%proto;
      (<(Recv, 1) @ (x:Z)> MSG #x ; <(Send, 0)> MSG #x; END)%proto].

  Lemma iProto_roundtrip_consistent :
    ⊢ iProto_consistent iProto_roundtrip.
  Proof. rewrite /iProto_roundtrip. iProto_consistent_take_steps. Qed.

  (* TODO: Fix nat/Z coercion. *)
  Lemma roundtrip_prog_spec :
    {{{ True }}} roundtrip_prog #() {{{ RET #42 ; True }}}.
  Proof using chanG0 heapGS0 Σ.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_new_chan iProto_roundtrip with iProto_roundtrip_consistent
      as (c0 c1 c2) "Hc0" "Hc1" "Hc2".
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>". wp_recv (x) as "_". wp_send with "[//]". done. }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>". wp_recv (x) as "_". wp_send with "[//]". done. }
    wp_send with "[//]". wp_recv as "_". by iApply "HΦ".
  Qed.

End channel.

Definition roundtrip_ref_prog : val :=
  λ: <>,
     let: "cs" := new_chan #3 in
     let: "c0" := get_chan "cs" #0 in
     let: "c1" := get_chan "cs" #1 in
     let: "c2" := get_chan "cs" #2 in
     Fork (let: "l" := recv "c1" #0 in "l" <- !"l" + #1;; send "c1" #2 "l");;
     Fork (let: "l" := recv "c2" #1 in "l" <- !"l" + #1;; send "c2" #0 #());;
     let: "l" := ref #40 in send "c0" #1 "l";; recv "c0" #2;; !"l".

Section roundtrip_ref.
  Context `{!heapGS Σ, !chanG Σ}.

  Definition iProto_roundtrip_ref : list (iProto Σ) :=
    [(<(Send, 1) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
            <(Recv, 2)> MSG #() {{ l ↦ #(x+2) }} ; END)%proto;
     (<(Recv, 0) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
            <(Send, 2)> MSG #l {{ l ↦ #(x+1) }}; END)%proto;
     (<(Recv, 1) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
            <(Send, 0)> MSG #() {{ l ↦ #(x+1) }}; END)%proto].

  Lemma iProto_roundtrip_ref_consistent :
    ⊢ iProto_consistent iProto_roundtrip_ref.
  Proof.
    rewrite /iProto_roundtrip_ref.
    iProto_consistent_take_steps.
    replace (x0 + 1 + 1)%Z with (x0+2)%Z by lia. iFrame.
    iProto_consistent_take_step.
  Qed.

  Lemma roundtrip_ref_prog_spec :
    {{{ True }}} roundtrip_ref_prog #() {{{ RET #42 ; True }}}.
  Proof using chanG0.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_new_chan iProto_roundtrip_ref with iProto_roundtrip_ref_consistent
      as (c0 c1 c2) "Hc0" "Hc1" "Hc2".
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>".
      wp_recv (l x) as "Hl". wp_load. wp_store. by wp_send with "[$Hl]". }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>".
      wp_recv (l x) as "Hl". wp_load. wp_store. by wp_send with "[$Hl]". }
    wp_alloc l as "Hl". wp_send with "[$Hl]". wp_recv as "Hl". wp_load.
    by iApply "HΦ".
  Qed.

End roundtrip_ref.

Definition roundtrip_ref_rec_prog : val :=
  λ: <>,
     let: "cs" := new_chan #3 in
     let: "c0" := get_chan "cs" #0 in
     let: "c1" := get_chan "cs" #1 in
     let: "c2" := get_chan "cs" #2 in
     Fork ((rec: "go" "c1" :=
             let: "l" := recv "c1" #0 in "l" <- !"l" + #1;; send "c1" #2 "l";;
             "go" "c1") "c1");;
     Fork ((rec: "go" "c2" :=
           let: "l" := recv "c2" #1 in "l" <- !"l" + #1;; send "c2" #0 #();;
           "go" "c2") "c2");;
     let: "l" := ref #38 in
     send "c0" #1 "l";; recv "c0" #2;;
     send "c0" #1 "l";; recv "c0" #2;; !"l".

Section roundtrip_ref_rec.
  Context `{!heapGS Σ, !chanG Σ}.

  Definition iProto_roundtrip_ref_rec1_aux (rec : iProto Σ) : iProto Σ :=
    (<(Send, 1) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
     <(Recv, 2)> MSG #() {{ l ↦ #(x+2) }} ; rec)%proto.
  Instance iProto_roundtrip_ref_rec1_contractive :
    Contractive iProto_roundtrip_ref_rec1_aux.
  Proof. solve_proto_contractive. Qed.
  Definition iProto_roundtrip_ref_rec1 :=
    fixpoint iProto_roundtrip_ref_rec1_aux.
  Lemma iProto_roundtrip_ref_rec1_unfold :
    iProto_roundtrip_ref_rec1 ≡
                (iProto_roundtrip_ref_rec1_aux iProto_roundtrip_ref_rec1).
  Proof. apply (fixpoint_unfold _). Qed.
  Global Instance iProto_roundtrip_ref_rec1_proto_unfold :
    ProtoUnfold iProto_roundtrip_ref_rec1
                (iProto_roundtrip_ref_rec1_aux iProto_roundtrip_ref_rec1).
  Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

  Definition iProto_roundtrip_ref_rec2_aux (rec : iProto Σ) : iProto Σ :=
    (<(Recv, 0) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
     <(Send, 2)> MSG #l {{ l ↦ #(x+1) }}; rec)%proto.
  Instance iProto_roundtrip_ref_rec2_contractive :
    Contractive iProto_roundtrip_ref_rec2_aux.
  Proof. solve_proto_contractive. Qed.
  Definition iProto_roundtrip_ref_rec2 :=
    fixpoint iProto_roundtrip_ref_rec2_aux.
  Lemma iProto_roundtrip_ref_rec2_unfold :
    iProto_roundtrip_ref_rec2 ≡
                (iProto_roundtrip_ref_rec2_aux iProto_roundtrip_ref_rec2).
  Proof. apply (fixpoint_unfold _). Qed.

  Global Instance iProto_roundtrip_ref_rec2_proto_unfold :
    ProtoUnfold iProto_roundtrip_ref_rec2
                (iProto_roundtrip_ref_rec2_aux iProto_roundtrip_ref_rec2).
  Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.
  Definition iProto_roundtrip_ref_rec3_aux (rec : iProto Σ) : iProto Σ :=
    (<(Recv, 1) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
     <(Send, 0)> MSG #() {{ l ↦ #(x+1) }}; rec)%proto.
  Instance iProto_roundtrip_ref_rec3_contractive :
    Contractive iProto_roundtrip_ref_rec3_aux.
  Proof. solve_proto_contractive. Qed.
  Definition iProto_roundtrip_ref_rec3 :=
    fixpoint iProto_roundtrip_ref_rec3_aux.
  Lemma iProto_roundtrip_ref_rec3_unfold :
    iProto_roundtrip_ref_rec3 ≡
                (iProto_roundtrip_ref_rec3_aux iProto_roundtrip_ref_rec3).
  Proof. apply (fixpoint_unfold _). Qed.
  Global Instance iProto_roundtrip_ref_rec3_proto_unfold :
    ProtoUnfold iProto_roundtrip_ref_rec3
                (iProto_roundtrip_ref_rec3_aux iProto_roundtrip_ref_rec3).
  Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

  Definition iProto_roundtrip_ref_rec : list (iProto Σ) :=
    [iProto_roundtrip_ref_rec1;
     iProto_roundtrip_ref_rec2;
     iProto_roundtrip_ref_rec3].

  Lemma iProto_roundtrip_ref_rec_consistent :
    ⊢ iProto_consistent iProto_roundtrip_ref_rec.
  Proof.
    iLöb as "IH".
    rewrite /iProto_roundtrip_ref_rec.
    iEval (rewrite iProto_roundtrip_ref_rec1_unfold).
    iEval (rewrite iProto_roundtrip_ref_rec2_unfold).
    iEval (rewrite iProto_roundtrip_ref_rec3_unfold).
    iProto_consistent_take_step.
    iIntros (l x) "Hloc". iExists _, _. iSplit; [done|]. iFrame.
    iProto_consistent_take_step.
    iIntros "Hloc". iExists _, _. iSplit; [done|]. iFrame. iNext.
    rewrite iProto_roundtrip_ref_rec2_unfold.
    iProto_consistent_take_step.
    iIntros "Hloc". iSplit; [done|].
    replace (x + 1 + 1)%Z with (x+2)%Z by lia. iFrame.
    rewrite -iProto_roundtrip_ref_rec2_unfold.
    iApply "IH".
  Qed.

  Lemma roundtrip_ref_rec_prog_spec :
    {{{ True }}} roundtrip_ref_rec_prog #() {{{ RET #42 ; True }}}.
  Proof using chanG0.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_new_chan iProto_roundtrip_ref_rec with iProto_roundtrip_ref_rec_consistent
      as (c0 c1 c2) "Hc0" "Hc1" "Hc2".
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>". wp_pure _. iLöb as "IH".
      wp_recv (l x) as "Hl". wp_load. wp_store. wp_send with "[$Hl]".
      do 2 wp_pure _. by iApply "IH". }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>". wp_pure _. iLöb as "IH".
      wp_recv (l x) as "Hl". wp_load. wp_store. wp_send with "[$Hl]".
      do 2 wp_pure _. by iApply "IH". }
    wp_alloc l as "Hl". wp_send with "[$Hl]". wp_recv as "Hl".
    wp_send with "[$Hl]". wp_recv as "Hl". wp_load.
    by iApply "HΦ".
  Qed.

End roundtrip_ref_rec.

Definition smuggle_ref_prog : val :=
  λ: <>,
     let: "cs" := new_chan #3 in
     let: "c0" := get_chan "cs" #0 in
     let: "c1" := get_chan "cs" #1 in
     let: "c2" := get_chan "cs" #2 in
     Fork (send "c1" #2 (recv "c1" #0);; send "c1" #0 (recv "c1" #2));;
     Fork (let: "l" := recv "c2" #1 in "l" <- !"l" + #2;; send "c2" #1 #());;
     let: "l" := ref #40 in
     send "c0" #1 "l";; recv "c0" #1;; !"l".

Section smuggle_ref.
  Context `{!heapGS Σ, !chanG Σ}.

  Definition iProto_smuggle_ref : list (iProto Σ) :=
    [(<(Send, 1) @ (l:loc) (x:Z)> MSG #l {{ l ↦ #x }} ;
            <(Recv,1)> MSG #() {{ l ↦ #(x+2) }} ; END)%proto;
     (<(Recv, 0) @ (v:val)> MSG v ; <(Send,2)> MSG v ;
            <(Recv, 2)> MSG #(); <(Send,0)> MSG #() ; END)%proto;
     (<(Recv, 1) @ (l:loc) (x:Z)> MSG #l {{ l ↦ #x }} ;
            <(Send,1)> MSG #() {{ l ↦ #(x+2) }} ; END)%proto].

  Lemma iProto_smuggle_ref_consistent :
    ⊢ iProto_consistent iProto_smuggle_ref.
  Proof. rewrite /iProto_smuggle_ref. iProto_consistent_take_steps. Qed.

  Lemma smuggle_ref_spec :
    {{{ True }}} smuggle_ref_prog #() {{{ RET #42 ; True }}}.
  Proof using chanG0 heapGS0 Σ.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_new_chan iProto_smuggle_ref with iProto_smuggle_ref_consistent
      as (c0 c1 c2) "Hc0" "Hc1" "Hc2".
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>". wp_recv (v) as "_". wp_send with "[//]".
      wp_recv as "_". by wp_send with "[//]". }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>". wp_recv (l x) as "Hl". wp_load. wp_store.
      by wp_send with "[$Hl]". }
    wp_alloc l as "Hl". wp_send with "[$Hl]". wp_recv as "Hl". wp_load.
    by iApply "HΦ".
  Qed.

End smuggle_ref.

Section parallel.
  Context `{!heapGS Σ}.

  (** 
         0 
       /   \
      1     2
      |     |
      3     4
       \   /
         0
   *)

  Definition iProto_parallel : list (iProto Σ) :=
    [(<(Send, 1) @ (x1:Z)> MSG #x1 ;
            <(Send, 2) @ (x2:Z)> MSG #x2 ;
            <(Recv, 3) @ (y1:Z)> MSG #(x1+y1);
            <(Recv, 4) @ (y2:Z)> MSG #(x2+y2); END)%proto;
     (<(Recv, 0) @ (x:Z)> MSG #x ;
            <(Send, 3) @ (y:Z)> MSG #(x+y); END)%proto;
     (<(Recv, 0) @ (x:Z)> MSG #x ;
            <(Send, 4) @ (y:Z)> MSG #(x+y) ; END)%proto;
     (<(Recv, 1) @ (x:Z)> MSG #x ;
            <(Send, 0)> MSG #x; END)%proto;
     (<(Recv, 2) @ (x:Z)> MSG #x ;
            <(Send, 0)> MSG #x ; END)%proto].

  Lemma iProto_parallel_consistent :
    ⊢ iProto_consistent iProto_parallel.
  Proof. rewrite /iProto_parallel. iProto_consistent_take_steps. Qed.

End parallel.

Section forwarder.
  Context `{!heapGS Σ}.

  (** 

          0
        / | \
      /   |   \
     |    1    |
      \ /   \ /
       2     3

   *)

  Definition iProto_forwarder : list (iProto Σ) :=
    [(<(Send, 1) @ (x:Z)> MSG #x ;
            <(Send, 1) @ (b:bool)> MSG #b ;
            <(Recv, if b then 2 else 3) > MSG #x ; END)%proto;
     (<(Recv, 0) @ (x:Z)> MSG #x ;
            <(Recv, 0) @ (b:bool)> MSG #b;
            <(Send, if b then 2 else 3)> MSG #x ; END)%proto;
     (<(Recv, 1) @ (x:Z)> MSG #x ;
            <(Send, 0)> MSG #x ; END)%proto;
     (<(Recv, 1) @ (x:Z)> MSG #x ;
            <(Send, 0)> MSG #x ; END)%proto].

  (* TODO: Anonymous variable in this is unsatisfactory *)
  Lemma iProto_forwarder_consistent :
    ⊢ iProto_consistent iProto_forwarder.
  Proof.
    rewrite /iProto_forwarder.
    iProto_consistent_take_steps.
    destruct x0; iProto_consistent_take_steps.
  Qed.

End forwarder.

Section forwarder_rec.
  Context `{!heapGS Σ}.

  (** 
          0
        / | \
      /   |   \
     |    1    |
      \ /   \ /
       2     3
   *)

  Definition iProto_forwarder_rec_0_aux (rec : iProto Σ) : iProto Σ :=
    (<(Send, 1) @ (x:Z)> MSG #x ;
     <(Send, 1) @ (b:bool)> MSG #b ;
     <(Recv, if b then 2 else 3) > MSG #x ; rec)%proto.
  Instance iProto_forwarder_rec_0_contractive :
    Contractive iProto_forwarder_rec_0_aux.
  Proof. solve_proto_contractive. Qed.
  Definition iProto_forwarder_rec_0 :=
    fixpoint iProto_forwarder_rec_0_aux.
  Lemma iProto_forwarder_rec_0_unfold :
    iProto_forwarder_rec_0 ≡
                (iProto_forwarder_rec_0_aux iProto_forwarder_rec_0).
  Proof. apply (fixpoint_unfold _). Qed.

  Definition iProto_forwarder_rec_1_aux (rec : iProto Σ) : iProto Σ :=
    (<(Recv, 0) @ (x:Z)> MSG #x ;
     <(Recv, 0) @ (b:bool)> MSG #b;
     if b
     then <(Send,2)> MSG #x ; rec
     else <(Send,3)> MSG #x ; rec)%proto.
  Instance iProto_forwarder_rec_1_contractive :
    Contractive iProto_forwarder_rec_1_aux.
  Proof. solve_proto_contractive. Qed.
  Definition iProto_forwarder_rec_1 :=
    fixpoint iProto_forwarder_rec_1_aux.
  Lemma iProto_forwarder_rec_1_unfold :
    iProto_forwarder_rec_1 ≡
                (iProto_forwarder_rec_1_aux iProto_forwarder_rec_1).
  Proof. apply (fixpoint_unfold _). Qed.

  Definition iProto_forwarder_rec_n_aux (rec : iProto Σ) : iProto Σ :=
    (<(Recv, 1) @ (x:Z)> MSG #x ;
     <(Send, 0)> MSG #x ; rec)%proto.
  Instance iProto_forwarder_rec_n_contractive :
    Contractive iProto_forwarder_rec_n_aux.
  Proof. solve_proto_contractive. Qed.
  Definition iProto_forwarder_rec_n :=
    fixpoint iProto_forwarder_rec_n_aux.
  Lemma iProto_forwarder_rec_n_unfold :
    iProto_forwarder_rec_n ≡
                (iProto_forwarder_rec_n_aux iProto_forwarder_rec_n).
  Proof. apply (fixpoint_unfold _). Qed.

  Definition iProto_forwarder_rec : list (iProto Σ) :=
    [iProto_forwarder_rec_0;
     iProto_forwarder_rec_1;
     iProto_forwarder_rec_n;
     iProto_forwarder_rec_n].

  Lemma iProto_forwarder_rec_consistent :
    ⊢ iProto_consistent iProto_forwarder_rec.
  Proof.
    iLöb as "IH".
    rewrite /iProto_forwarder_rec.
    iEval (rewrite iProto_forwarder_rec_0_unfold).
    iEval (rewrite iProto_forwarder_rec_1_unfold).
    iEval (rewrite iProto_forwarder_rec_n_unfold).
    iProto_consistent_take_step.
    iIntros (x) "_". iExists _. iSplit; [done|]. iSplit; [done|].
    iProto_consistent_take_step.
    iIntros ([]) "_".
    - iExists _. iSplit; [done|]. iSplit; [done|].
      iProto_consistent_take_step.
      iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
      iNext.
      iEval (rewrite iProto_forwarder_rec_1_unfold).
      iEval (rewrite iProto_forwarder_rec_n_unfold).
      iProto_consistent_take_step.
      iIntros "_". iSplit; [done|]. iSplit; [done|].
      iEval (rewrite -iProto_forwarder_rec_1_unfold).
      iEval (rewrite -iProto_forwarder_rec_n_unfold).
      iEval (rewrite -iProto_forwarder_rec_n_unfold).
      iApply "IH".
    - iExists _. iSplit; [done|]. iSplit; [done|].
      iProto_consistent_take_step.
      iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
      iNext.
      iEval (rewrite iProto_forwarder_rec_1_unfold).
      iEval (rewrite iProto_forwarder_rec_n_unfold).
      iProto_consistent_take_step.
      iIntros "_". iSplit; [done|]. iSplit; [done|].
      iEval (rewrite -iProto_forwarder_rec_1_unfold).
      iEval (rewrite -iProto_forwarder_rec_n_unfold).
      iEval (rewrite -iProto_forwarder_rec_n_unfold).
      iApply "IH".
  Qed.

End forwarder_rec.
