From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From iris.heap_lang.lib Require Import spin_lock.
From osiris.utils Require Import list compare.


Definition qenqueue : val := λ: "q" "v", #().
Definition qdequeue : val := λ: "q", #().
Definition qis_empty : val := λ: "q", #().

Definition enq := true.
Definition deq := false.

Definition cont := true.
Definition stop := false.

Definition some := true.
Definition none := false.

Definition dist_queue : val :=
  rec: "go" "q" "pc" "cc" "c" :=
    if: "cc" ≤ #0 then #() else 
    if: recv "c"                (* enq/deq *)
    then if: recv "c"           (* cont/stop *)
         then "go" (qenqueue "q" (recv "c")) "pc" "cc" "c"
         else "go" "q" ("pc"-#1) "cc" "c"
    else if: (qis_empty "q")
         then if: "pc" ≤ #0
              then send "c" #stop;; "go" "q" "pc" ("cc"-#1) "c"
              else send "c" #cont;; send "c" #none;; "go" "q" "pc" "cc" "c"
         else send "c" #cont;; send "c" #some;;
              let: "qv" := qdequeue "q" in
              send "c" (Snd "qv");; "go" (Fst "qv") "pc" "cc" "c".

Definition producer : val :=
  rec: "go" "c" "l" "produce" :=
    match: "produce" #() with
      SOME "v" =>
        acquire "l";;
        send "c" #enq;; send "c" #cont;; send "c" "v";;
        release "l";;
        "go" "c" "l" "produce"
     | NONE =>
        acquire "l";;
        send "c" #enq;; send "c" #stop
        release "l"
    end.
        
Definition consumer : val :=
  rec: "go" "c" "l" "consume" :=
    acquire "l";;
    send "c" #deq;;
    if: recv "c"             (* cont/stop *)
    then if: recv "c"        (* some/none *)
         then let: "v" := recv "c" in
              release "l";; "produce" "v";; "go" "c" "l" "consume"
         else release "l";; "go" "c" "l" "consume"
    else release "l";; #().

