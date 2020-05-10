## Differences

The semantic encoding of ground types use existential quantification in the
mechanisation (e.g. `λ w. ∃ (x:Z), w = int`, while the paper uses set
inclusion (e.g. `λ w. w ∈ Z`). The definitions are effectively identical.

Polymorphism in the paper is done over the type kinds (e.g. `∀ (X :k).A`),
where the mechanisation uses concrete types that are parametric on a kind
(e.g. `∀ (X : lty k Σ).A`). This is just syntactic sugar to be less explicit
in the paper.

## Examples

The parallel receive example in Section 4 can be found in
  [theories/logrel/examples/double.v](../theories/logrel/examples/double.v):
  This program performs two ``racy'' parallel receives on the same channel from two
  different threads, using locks to allow the channel to be shared. This
  program cannot be shown to be well-typed using the semantic typing rules.
  Therefore, a manual proof of the well-typedness is given.

The subprotocol assertion over two protocols that sends reference ownerships in
Section 5 can be found in
  [theories/examples/subprotocols.v](../theories/examples/subprotocols.v):
  It contains the proof of the example.

The recursive session subtyping example in Section 5 can be found in
  [theories/logrel/examples/subtyping.v](../theories/logrel/examples/subtyping.v):
