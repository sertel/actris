From iris.heap_lang Require Import adequacy.
From iris.heap_lang.lib Require Import assert.
From multi_actris.channel Require Import proofmode.


Section mpc_protocols.
  Context `{!heapGS Σ, chanG Σ}.

  Notation A := 0.
  Notation B := 1.
  Notation C := 2.

(* A :  *)
(*   ![B] (a2) <a2> . ![C] (a3) <a3> .  *)
(*   ?[B] (b1) <b1> . ?[C] (c1) <c1> . *)
(*   ![B] (s1) (a1) <s1> { s1 = a1 + b1 + c1 } . ![C]  <s1> . *)
(*   ?[B] (s2) <s2> . ? [C] (s3) <s3> . *)
(*   prot_tail (s1+s2+s3) *)

  Definition A_prot (p : Z → iProto Σ) : iProto Σ :=
    (<(Send,B) @ (a2:Z)> MSG #a2 ; <(Send,C) @ (a3:Z)> MSG #a3 ;
     <(Recv,B) @ (b1:Z)> MSG #b1 ; <(Recv,C) @ (c1:Z)> MSG #c1 ;
     <(Send,B) @ (s1:Z) (a1:Z)> MSG #s1 {{ ⌜(s1 = a1 + b1 + c1)%Z⌝ }} ;
     <(Send,C)> MSG #s1 ;
     <(Recv,B) @ (s2:Z)> MSG #s2 ; <(Recv,C) @ (s3:Z)> MSG #s3;
     p (s1 + s2 + s3)%Z)%proto.

(* B : *)
(*   ?[A] (a2) <a2> . ![A] (b1) <b1> . *)
(*   ![C] (c2) <c2> . ?[C] (b3) <b3> . *)
(*   ?[A] (s1) <s1> . ![A] (s2) (a2) <s2> { s2 = a2 + b2 + c2 } . *)
(*   ![C] <s2> . ?[C] (s3) <s3> . *)
(*   prot_tail (s1+s2+s3) *)

  Definition B_prot (p : Z → iProto Σ) : iProto Σ :=
    (<(Recv,A) @ (a2:Z)> MSG #a2 ; <(Send,A) @ (b1:Z)> MSG #b1 ;
     <(Send,C) @ (c2:Z)> MSG #c2 ; <(Recv,C) @ (b3:Z)> MSG #b3 ;
     <(Recv,A) @ (s1:Z)> MSG #s1 ;
     <(Send,A) @ (s2:Z) (b2:Z)> MSG #s2 {{ ⌜(s2 = a2 + b2 + c2)%Z⌝ }} ;
     <(Send,C)> MSG #s2 ; <(Recv,C) @ (s3:Z)> MSG #s3 ;
     p (s1 + s2 + s3)%Z)%proto. 

(* C : *)
(*   ?[A] (a3) <a3> . ![A] (c1) <c1> . *)
(*   ?[B] (b3) <b3> . ![B] (c2) <c2> . *)
(*   ?[A] (s1) <s1> . ![A] (s3) (a3) <s3> { s3 = a3 + b3 + c3 }  *)
(*   ?[B] <s2> . ![B] (s3) <s3> . *)
(*   prot_tail (s1+s2+s3) *)

  Definition C_prot (p : Z → iProto Σ) : iProto Σ :=
    (<(Recv,A) @ (a3:Z)> MSG #a3 ; <(Send,A) @ (c1:Z)> MSG #c1 ;
     <(Recv,B) @ (b3:Z)> MSG #b3 ; <(Send,B) @ (c2:Z)> MSG #c2 ;
     <(Recv,A) @ (s1:Z)> MSG #s1 ; 
     <(Send,A) @ (s3:Z) (c3:Z)> MSG #s3 {{ ⌜(s3 = a3 + b3 + c3)%Z⌝ }} ;
     <(Recv,B) @ (s2:Z)> MSG #s2 ; <(Send,B)> MSG #s3; 
     p (s1 + s2 + s3)%Z)%proto.  

  Notation D := 3.

  Definition D_prot : iProto Σ :=
    (<(Recv,A) @ (sum : Z)> MSG #sum ; <(Recv,B)> MSG #sum; <(Recv,C)> MSG #sum; END)%proto.
    
  Definition tail_prot (sum : Z) : iProto Σ :=
     (<(Send,D)> MSG #sum ; END)%proto.

  Definition mpc_prot_pool : list (iProto Σ) :=
     [A_prot tail_prot; B_prot tail_prot; C_prot tail_prot; D_prot].
  
  Lemma mpc_consistent :
    ⊢ iProto_consistent mpc_prot_pool.
  Proof.
    rewrite /mpc_prot_pool.
    iProto_consistent_take_steps.
  Qed.

End mpc_protocols.
