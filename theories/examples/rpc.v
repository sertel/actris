From iris.heap_lang Require Import proofmode.
From actris.channel Require Import proofmode.

Definition server : val :=
  rec: "go" "dict" "c" :=
    if: ~ (recv "c") then #()
    else
      let: "f" := "dict" (recv "c") in
      let: "res" := "f" (recv "c") in
      send "c" "res";;
      "go" "dict" "c".

Definition Left : val := #true.
Definition Right : val := #false.

Notation plus_id := 1%Z.
Notation incr_ref_id := 2%Z.

Definition client : val :=
  λ: "c",
    send "c" Left;;
    send "c" #plus_id;; send "c" (#40,#2);; let: "res1" := recv "c" in
    send "c" Left;;
    let: "l" := ref #41 in
    send "c" #incr_ref_id;; send "c" "l";; let: "res2" := ! (recv "c") in
    send "c" Right;;
    ("res1","res2").

Definition program : val :=
  λ: "dict",
    let: "c" := new_chan #() in
    Fork (server "dict" (Snd "c"));;
    client (Fst "c").

Section rpc_example.
  Context `{!heapG Σ, !chanG Σ}.

  Definition f_spec {T U} (IT : T → val → iProp Σ) (IU : U → val → iProp Σ)
             (f : T → U) (fv : val) : iProp Σ :=
    (∀ x v, {{{ IT x v }}} fv v {{{ w, RET w; IU (f x) w }}})%I.

  Definition rpc_prot_aux (f_specs : gmap Z (val → iProp Σ)) (rec : iProto Σ)
    : iProto Σ :=
    ((<! (T U:Type) IT IU (f : T → U) (id:Z)> MSG #id
        {{ ⌜f_specs !! id = Some (f_spec IT IU f)⌝ }};
      <! (x:T) (v:val)> MSG v {{ IT x v }} ;
      <? (w:val)> MSG w {{ IU (f x) w }} ; rec)
    <+> END)%proto.

  Instance rpc_prot_aux_contractive (f_specs : gmap Z (val → iProp Σ)) :
    Contractive (rpc_prot_aux f_specs).
  Proof. solve_proto_contractive. Qed.
  Definition rpc_prot (f_specs : gmap Z (val → iProp Σ)) : iProto Σ :=
    fixpoint (rpc_prot_aux f_specs).
  Global Instance rpc_prot_unfold f_specs :
    ProtoUnfold (rpc_prot f_specs) (rpc_prot_aux f_specs (rpc_prot f_specs)).
  Proof. apply proto_unfold_eq, fixpoint_unfold. Qed.

  Definition dict_spec (dict : val) (f_specs : gmap Z _) : iProp Σ :=
    ∀ (T U : Type) (id : Z) (IT : T → val → iProp Σ) (IU : U → val → iProp Σ)
      (f : T → U),
      {{{ ⌜f_specs !! id = Some (f_spec IT IU f)⌝ }}}
        dict #id
      {{{ fv, RET fv; f_spec IT IU f fv }}}.

  Lemma server_spec dict f_specs c prot :
    {{{ dict_spec dict f_specs ∗
        c ↣ (iProto_dual (rpc_prot f_specs) <++> prot)%proto }}}
      server dict c
    {{{ RET #(); c ↣ prot }}}.
  Proof.
    iIntros (Φ) "[#Hdict Hc] HΦ".
    iLöb as "IH".
    wp_rec.
    wp_branch; last first.
    { wp_pures. by iApply "HΦ". }
    wp_recv (T U IT IU f id) as "Hlookup".
    wp_apply ("Hdict" with "Hlookup"); iIntros (fv) "Hfv".
    wp_recv (x v) as "HIT".
    wp_apply ("Hfv" with "HIT"); iIntros (w) "HIU".
    wp_send (w) with "[$HIU]".
    wp_pures. by iApply ("IH" with "Hc").
  Qed.

  Definition plus_spec :=
    f_spec (λ (x:Z*Z) (v:val), ⌜(#(fst x), #(snd x))%V = v⌝)%I
           (λ y w, ⌜#y = w⌝)%I
           (λ (x:Z*Z), (fst x) + (snd x))%Z.

  Definition incr_ref_spec :=
    f_spec (λ (x:Z) (v:val), ∃ (l : loc), ⌜v = #l⌝ ∗ l ↦ #x)%I
           (λ (y:Z) (w:val), ∃ (l : loc), ⌜w = #l⌝ ∗ l ↦ #y)%I
           (λ (x:Z), x+1)%Z.

  Definition client_f_specs : gmap Z (val → iProp Σ) :=
    {[ plus_id := plus_spec ]} ∪
    {[ incr_ref_id := incr_ref_spec ]}.

  Lemma client_spec c :
    {{{ c ↣ rpc_prot client_f_specs }}}
      client c
    {{{ RET (#42, #42); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_lam.
    (** plus *)
    wp_select.
    wp_send with "[//]". wp_send with "[]".
    { by instantiate (1:=(40,2)%Z). }
    wp_recv (w) as "<-".
    (** incr_ref *)
    wp_select.
    wp_alloc l as "Hl".
    wp_send with "[//]". wp_send with "[Hl]".
    { eauto. }
    wp_recv (w) as (l') "[-> Hl]".
    wp_load.
    (** Termination *)
    wp_select.
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma program_spec dict :
    {{{ dict_spec dict client_f_specs }}}
      program dict
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "#Hdict HΦ".
    wp_lam.
    wp_apply (new_chan_spec (rpc_prot client_f_specs))=> //.
    iIntros (c1 c2) "[Hc1 Hc2]".
    wp_apply (wp_fork with "[Hc2]").
    - iIntros "!>". wp_apply (server_spec _ _ _ END%proto with "[Hc2]").
      rewrite right_id. iFrame "Hdict Hc2". by iIntros "_".
    - by wp_apply (client_spec with "Hc1").
  Qed.

End rpc_example.
