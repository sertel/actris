From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl.
From iris.heap_lang.lib Require Import lock.
From iris.heap_lang.lib Require Import spin_lock.
From osiris Require Import list.
Set Default Proof Using "Type".

Definition new_list : val :=
  λ: <>, lnil #().

Definition new_chan : val := 
  λ: <>,
     let l := ref new_list #() in
     let r := ref new_list #() in
     let lk := newlock #() in
     ((l,r),lk).

Notation left := (#true) (only parsing).
Notation right := (#false) (only parsing).

Definition get_buffs c := Fst c.
Definition get_left c := Fst (get_buffs c).
Definition get_right c := Snd (get_buffs c).
Definition get_lock c := Snd c.

Definition dual_side s :=
  (if: s = left then right else left)%E.

Definition get_side c s :=
  (if: s = left then (get_left c) else (get_right c))%E.

Definition send : val :=
  λ: "c" "s" "v",
    let lk := get_lock "c" in
    acquire lk;;
    let l := get_side "c" "s" in
    l <- lsnoc !l "v";;
    release lk.

Definition try_recv : val :=
  λ: "c" "s",
    let lk := get_lock "c" in
    acquire lk;;
    let l := (get_side "c" (dual_side "s")) in
    let v :=
        match: !l with
          SOME "p" => l <- Snd "p";; SOME (Fst "p")
        | NONE => NONE
        end in
    release lk;;
    v.

Definition recv : val :=
  rec: "go" "c" "s" :=
    match: try_recv "c" "s" with
      SOME "p" => "p"
    | NONE => "go" "c" "s"
    end.

Section channel.
  Context `{!heapG Σ, !lockG Σ} (N : namespace).
  
  Definition is_list_ref (l : val) (xs : list val) : iProp Σ :=
    (∃ l':loc, ⌜l = #l'⌝ ∧ ∃ hd : val, l' ↦ hd ∗ ⌜is_list hd xs⌝)%I.

  Definition is_side (s : val) : Prop :=
    s = left ∨ s = right.
    
  Definition is_chan (γ : gname) (c : val) (ls rs : list val) (R : iProp Σ) : iProp Σ :=
    (∃ l r lk : val, ⌜c = ((l, r), lk)%V⌝ ∧ is_lock N γ lk R ∗ is_list_ref l ls ∗ is_list_ref r rs)%I.

  Lemma new_chan_spec (R : iProp Σ) :
    {{{ R }}}
      new_chan #()
    {{{ c γ, RET c; is_chan γ c [] [] R }}}.
  Proof. 
    iIntros (Φ) "HR HΦ". rewrite -wp_fupd /newlock /new_list /=.
    repeat wp_lam. wp_alloc lk as "Hlk".
    repeat wp_lam. wp_alloc r as "Hr".
    repeat wp_lam. wp_alloc l as "Hl".
    wp_pures.
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ lk R) with "[-Hl Hr HΦ]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro.
    iApply "HΦ".
    iExists _, _, _.
    iSplit=> //.
    iSplitR.
    - unfold is_lock. iExists _. iSplit=> //.
    - iSplitL "Hl"; iExists _; iSplit=> //; iExists (InjLV #()); iSplit => //.
  Qed.

  (* Insert a value 'v' in the buffer of a given channel 'c', based on the given side 's' *)
  Definition send_upd γ c ls rs R s v : iProp Σ :=
    match s with
    | left  => is_chan γ c (ls ++ [v]) rs R
    | right => is_chan γ c ls (rs ++ [v]) R
    | _ => ⌜False⌝%I
    end.

  Lemma send_spec (γ : gname) (c v s : val) (ls rs : list val) (R : iProp Σ) :
    {{{ is_chan γ c ls rs R ∗ ⌜is_side s⌝%I }}}
      send c s v
    {{{ RET #(); send_upd γ c ls rs R s v }}}.
  Proof.
    iIntros (Φ) "[Hc #Hs] HΦ". 
    iRevert "Hs". iIntros (Hs).
    rewrite -wp_fupd /send /=.
    iDestruct "Hc" as (l r lk Hc) "[#Hlk [Hl Hr]]".
    wp_lam.
    wp_pures.
    subst.
    wp_bind (Snd _). 
    wp_pures.
    wp_bind (acquire lk).
    iApply acquire_spec=> //.
    iNext.
    iIntros "[Hlocked HR]".
    wp_seq.
    wp_pures.
    inversion Hs; 
      [iDestruct "Hl" as (lb Hb bhd) "[Hl #Hbhd]" |
       iDestruct "Hr" as (lb Hb bhd) "[Hr #Hbhd]"];
      subst;
      wp_pures;
      wp_bind (lsnoc (Load #lb) v);
      wp_load;
      iApply lsnoc_spec=> //;
      iIntros (hd' Hhd');
      iNext;
      wp_store;
      wp_pures;
      iApply (release_spec N γ lk R with "[Hlocked HR]") => //;
      iFrame; eauto;
      iModIntro;
      iIntros (_);
      iModIntro;
      iApply "HΦ";
      iExists _, _, _;
      iSplitR;
      eauto;
      iSplitL "Hlk"=> //;
      iSplitL "Hl"=> //;
      iExists _;
      iSplitR;
      eauto.
  Qed.

  Definition try_recv_upd γ c ls rs R s v : iProp Σ :=
    match s with
    | left => match v with
              | NONEV => (is_chan γ c ls rs R ∧ ⌜rs = []⌝)%I
              | SOMEV w => (∃ rs', is_chan γ c ls rs' R ∧ ⌜rs = w::rs'⌝)%I
              | _ => ⌜False⌝%I
              end
    | right => match v with
               | NONEV => (is_chan γ c ls rs R ∧ ⌜ls = []⌝)%I
               | SOMEV w => (∃ ls', is_chan γ c ls' rs R ∧ ⌜ls = w::ls'⌝)%I
               | _ => ⌜False⌝%I
               end 
    | _ => ⌜False⌝%I
    end.

  Lemma try_recv_spec (γ : gname) (c v s : val) (ls rs : list val) (R : iProp Σ) :
    {{{ is_chan γ c ls rs R ∗ ⌜is_side s⌝%I }}}
      try_recv c s
    {{{ v, RET v;  try_recv_upd γ c ls rs R s v }}}.
  Proof.
    iIntros (Φ) "[Hc #Hs] HΦ". 
    iRevert "Hs". iIntros (Hs).
    rewrite -wp_fupd /send /=.
    iDestruct "Hc" as (l r lk Hc) "[#Hlk [Hl Hr]]".
    subst.
    wp_lam.
    wp_pures.
    wp_bind (acquire _).
    iApply acquire_spec=> //.
    iNext.
    iIntros "[Hlocked HR]".
    wp_seq.
    wp_bind (release _).
    wp_bind (Snd _).
    wp_pures.
    iApply (release_spec N γ lk R with "[Hlocked HR]") => //.
    iFrame. eauto.
    iNext. iIntros (_).
    wp_pures.
    inversion Hs; subst.
    - wp_pures.
      iDestruct "Hr" as (rl Hr rhd) "[Hr #Hrhd]".
      wp_pures.
      subst.
      wp_load.
      iRevert "Hrhd". iIntros (Hrhd).
      unfold is_list in Hrhd.
      destruct rs.
      + subst.
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iSplit=> //.
        iExists _, _, _.
        iSplit=> //.
        iFrame.
        iSplitR. eauto.
        iExists _.
        iSplit=> //.
        iExists _.
        iSplit=> //.
      + subst.
        destruct Hrhd as [hd' [Hrhd Hrhd']].
        subst.
        wp_pures.
        wp_store. wp_pures. iModIntro.
        iApply "HΦ".
        iExists _.
        iSplit=> //.
        iExists _, _, _.
        iSplit=> //.
        iSplit=> //.
        iFrame. 
        iExists _.
        iSplit=>//.
        iExists _.
        iSplit=> //.
    - wp_pures.
      iDestruct "Hl" as (ll Hl lhd) "[Hl #Hlhd]".
      wp_pures.
      subst.
      wp_load.
      iRevert "Hlhd". iIntros (Hlhd).
      unfold is_list in Hlhd.
      destruct ls.
      + subst.
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iSplit=> //.
        iExists _, _, _.
        iSplit=> //.
        iFrame.
        iSplitR. eauto.
        iExists _.
        iSplit=> //.
        iExists _.
        iSplit=> //.
      + subst.
        destruct Hlhd as [hd' [Hlhd Hlhd']].
        subst.
        wp_pures.
        wp_store. wp_pures. iModIntro.
        iApply "HΦ".
        iExists _.
        iSplit=> //.
        iExists _, _, _.
        iSplit=> //.
        iSplit=> //.
        iFrame. 
        iExists _.
        iSplit=>//.
        iExists _.
        iSplit=> //.
  Qed.  

End channel.