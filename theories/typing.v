From iris.heap_lang Require Export lang.

Section typing.

  Inductive side : Set :=
  | Left
  | Right.

  Inductive stype :=
  | TEnd
  | TSend (P : val → Prop) (sτ : val → stype)
  | TRecv (P : val → Prop) (sτ : val → stype).

  Fixpoint dual_stype (sτ :stype) :=
    match sτ with
    | TEnd => TEnd
    | TSend P sτ => TRecv P (λ v, dual_stype (sτ v))
    | TRecv P sτ => TSend P (λ v, dual_stype (sτ v))
    end.

End typing.