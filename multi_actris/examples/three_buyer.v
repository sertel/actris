From multi_actris.channel Require Import proofmode.
Set Default Proof Using "Type".

Definition buyer1_prog : val :=
  λ: "cb1" "s" "b2",
    send "cb1" "s" #0;;
    let: "quote" := recv "cb1" "s" in
    send "cb1" "b2" ("quote" `rem` #2);;
    recv "cb1" "b2";; #().

Definition seller_prog : val :=
  λ: "cs" "b1" "b2",
    let: "title" := recv "cs" "b1" in
    send "cs" "b1" #42;; send "cs" "b2" #42;;
    let: "b" := recv "cs" "b2" in
    if: "b" then
      send "cs" "b2" #0
    else #().

Definition buyer2_prog : val :=
  λ: "cb2" "b1" "s" "cb2'" "b3",
    let: "quote" := recv "cb2" "s" in
    let: "contrib" := recv "cb2" "b1" in
    if: ("quote" - "contrib" < #100)
    then send "cb2" "s" #true;; send "cb2" "b1" #true;;
         recv "cb2" "s"
    else send "cb2'" "b3" "quote";;
         send "cb2'" "b3" ("contrib" + #100);;
         send "cb2'" "b3" "cb2".

Definition buyer3_prog : val :=
  λ: "cb3" "b1" "b2'" "s",
    let: "quote" := recv "cb3" "b2'" in
    let: "contrib" := recv "cb3" "b2'" in
    let: "cb2" := recv "cb3" "b2'" in
    if: ("quote" - "contrib" < #100)
    then send "cb2" "s" #true;; send "cb2" "b1" #true;;
         recv "cb2" "s"
    else #().

Definition three_buyer_prog : val :=
  λ: <>,
     let: "cs" := new_chan #3 in
     let: "b1" := get_chan "cs" #0 in
     let: "s" := get_chan "cs" #1 in
     let: "b2" := get_chan "cs" #2 in
     let: "cs'" := new_chan #2 in
     let: "b2'" := get_chan "cs'" #0 in
     let: "b3" := get_chan "cs'" #1 in
     Fork (seller_prog "s" #0 #2);;
     Fork (buyer2_prog "b2" #0 #1 "b2'" #1);;
     Fork (buyer3_prog "b3" #0 #1 #0);;
     buyer1_prog "b1" #1 #2.

Section three_buyer.
  Context `{!heapGS Σ, !chanG Σ}.

  Definition buyer1_prot s b2 : iProto Σ :=
    (<(Send, s) @ (title:Z)> MSG #title ;
     <(Recv, s) @ (quote:Z)> MSG #quote ;
     <(Send, b2) @ (contrib:Z)> MSG #contrib ; 
     <(Recv, b2) @ (b:bool)> MSG #b; END)%proto.

  Lemma buyer1_spec c s b2 :
    {{{ c ↣ buyer1_prot s b2 }}}
      buyer1_prog c #s #b2 
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". wp_lam.
    wp_send with "[//]".
    wp_recv (quote) as "_".
    wp_send with "[//]".
    wp_recv (b) as "_". wp_pures.
    by iApply "HΦ". 
  Qed.
  
  Definition seller_prot b1 b2 : iProto Σ :=
    (<(Recv, b1) @ (title:Z)> MSG #title ;
     <(Send, b1) @ (quote:Z)> MSG #quote ;
     <(Send, b2)> MSG #quote ;
     <(Recv, b2) @ (b:bool)> MSG #b ;
     if b then
       <(Send, b2) @ (date:Z)> MSG #date ; END
     else END)%proto.

  Lemma seller_spec c b1 b2 :
    {{{ c ↣ seller_prot b1 b2 }}}
      seller_prog c #b1 #b2 
    {{{ b, RET #b; True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". wp_lam.
    wp_recv (title) as "_".
    wp_send with "[//]".
    wp_send with "[//]".
    wp_recv (b) as "_".
    destruct b.
    - wp_pures. wp_send with "[//]". by iApply "HΦ". 
    - wp_pures. by iApply "HΦ".
  Qed.
  
  Definition buyer2_prot b1 s : iProto Σ :=
    (<(Recv, s) @ (quote:Z)> MSG #quote ;
     <(Recv, b1) @ (contrib:Z)> MSG #contrib ;
     <(Send, s) @ (b:bool)> MSG #b ;
     <(Send, b1)> MSG #b ;
     if b then <(Recv, s) @ (date:Z)> MSG #date ; END
     else <(Send, s)> MSG #false ; END)%proto.

  Definition buyer2_prot' b3 b1 s : iProto Σ :=
    (<(Send, b3) @ (quote:Z)> MSG #quote ;
     <(Send, b3) @ (contrib:Z)> MSG #contrib ;
     <(Send, b3) @ (c:val)> MSG c
                               {{ c ↣ (<(Send, s) @ (b:bool)> MSG #b ;
                                  <(Send, b1)> MSG #b ;
                                  if b then <(Recv, s) @ (date:Z)> MSG #date ; END
                                  else <(Send, s)> MSG #false ; END)%proto }} ;
     END)%proto.

  Lemma buyer2_spec c b1 s c' b3 :
    {{{ c ↣ buyer2_prot b1 s ∗ c' ↣ buyer2_prot' b3 b1 s }}}
      buyer2_prog c #b1 #s c' #b3
    {{{ b, RET #b; True }}}.
  Proof.
    iIntros (Φ) "[Hc Hc'] HΦ". wp_lam.
    wp_recv (quote) as "_".
    wp_recv (contrib) as "_".
    wp_pures. case_bool_decide.
    - wp_send with "[//]". wp_send with "[//]". wp_recv (date) as "_".
      by iApply "HΦ".
    - wp_send with "[//]". wp_send with "[//]". wp_send with "[Hc//]".
      by iApply "HΦ".
  Qed.

  Definition buyer3_prot b1 b2' s : iProto Σ :=
    (<(Recv, b2') @ (quote:Z)> MSG #quote ;
     <(Recv, b2') @ (contrib:Z)> MSG #contrib ;
     <(Recv, b2') @ (c:val)> MSG c
                               {{ c ↣ (<(Send, s) @ (b:bool)> MSG #b ;
                                  <(Send, b1)> MSG #b ;
                                  if b then <(Recv, s) @ (date:Z)> MSG #date ; END
                                  else <(Send, s)> MSG #false ; END)%proto }} ;
     END)%proto.

  Lemma buyer3_spec c b1 b2' s :
    {{{ c ↣ buyer3_prot b1 b2' s }}}
      buyer3_prog c #b1 #b2' #s 
    {{{ b, RET #b; True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". wp_lam. wp_pures.
    wp_recv (quote) as "_".
    wp_recv (contrib) as "_".
    wp_recv (c') as "Hc'".
    wp_pures.
    case_bool_decide.
    - wp_send with "[//]". wp_send with "[//]". wp_recv (date) as "_".
      by iApply "HΦ".
    - wp_pures. by iApply "HΦ".
  Qed.

  Definition two_buyer_prot : list (iProto Σ) :=
    [buyer1_prot 1 2 ; seller_prot 0 2; buyer2_prot 0 1].

  Lemma two_buyer_prot_consistent :
    ⊢ iProto_consistent two_buyer_prot.
  Proof.
    rewrite /two_buyer_prot. iProto_consistent_take_steps.
    destruct x2; iProto_consistent_take_steps.
  Qed.

  Definition three_buyer_prot : list (iProto Σ) :=
    [buyer2_prot' 1 0 1; buyer3_prot 0 1 0].

  Lemma three_buyer_prot_consistent :
    ⊢ iProto_consistent three_buyer_prot.
  Proof. rewrite /three_buyer_prot. iProto_consistent_take_steps. Qed.

  Lemma three_buyer_spec :
    {{{ True }}}
      three_buyer_prog #()
    {{{ RET #(); True }}}.
  Proof using chanG0 heapGS0 Σ.
    iIntros (Φ) "Hc HΦ". wp_lam.
    wp_new_chan two_buyer_prot with two_buyer_prot_consistent
      as (???) "Hcb1" "Hcs" "Hcb2".
    wp_pures.
    wp_new_chan three_buyer_prot with three_buyer_prot_consistent
      as (??) "Hcb2'" "Hcb3".
    wp_smart_apply (wp_fork with "[Hcs]").
    { by iApply (seller_spec with "Hcs"). }
    wp_smart_apply (wp_fork with "[Hcb2 Hcb2']").
    { by iApply (buyer2_spec with "[$Hcb2 $Hcb2']"). }
    wp_smart_apply (wp_fork with "[Hcb3]").
    { by iApply (buyer3_spec with "Hcb3"). }
    wp_smart_apply (buyer1_spec with "Hcb1").
    by iApply "HΦ".
  Qed.

End three_buyer.
