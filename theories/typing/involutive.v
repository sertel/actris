From iris.heap_lang Require Import proofmode notation.

Class Involutive {A} (R : relation A) (f : A → A) :=
  involutive x : R (f (f x)) x.