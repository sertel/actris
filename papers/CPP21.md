# Code corresponding to the paper

All code corresponding to the paper can be found in the directory
[theories/logrel](../theories/logrel). The file [README.md](../README.md)
contains an overview of the files in that directory.

# Differences between the paper and the mechanisation

- The semantic encoding of ground types use existential quantification in the
  mechanization (e.g., `λ w. ∃ (x:Z), w = int`, while the paper uses set
  inclusion (e.g., `λ w. w ∈ Z`). The definitions are effectively identical.
- Polymorphism in the paper is written over the type kinds, e.g., `∀ (X : k).A`,
  whereas that is written `∀ (X : lty k Σ). A` in Coq. This notation is used to
  for technical reasoning. The underlying definitions are the same between
  Coq and the paper.
- The polymorphic session types are defined in an nested fashion, as a sequence
  of quantifiers, followed by the actual type, for mechanisation purposes
  using telescopes. The definitions are effectively identical to the paper.
- The typing rule for branching (`ltyped_branch`) is written as a function
  instead of an n-ary rule with multiple premises.
- The disjunction of the compute client invariant is encoded using a boolean
  flag, as it makes mechanisation easier.
- The mechanisation employs a typing judgement for values (`ltyped_val`),
  for technical reasons. More details on this is found in
  [theories/logrel/term_typing_judgment.v](../theories/logrel/term_typing_judgment.v)
- Minor simplifications have been made for the displayed Coq code of Section 5,
  such as assuming that implicit variables (e.g., `{!heapG Σ}`) are available from
  a `Context`, rather than as an implicit variable of the definitions.
  The definitions between the paper and Coq code are identical,
  as this is just refactoring.

# Examples

- The compute service example in Section 3 can be found in
  [theories/logrel/examples/compute_service.v](../theories/logrel/examples/compute_service.v)
  The program recursively receive computation requests, which it computes and
  then send back. It is entirely type checked with the rules of the type system
- The parallel receive example in Section 4 can be found in
  [theories/logrel/examples/par_recv.v](../theories/logrel/examples/par_recv.v):
  This program performs two "racy" parallel receives on the same channel from
  two different threads, using locks to allow the channel to be shared.
- The parallel compute client example in Section 4 can be found in
  [theories/logrel/examples/compute_client_list.v](../theories/logrel/examples/compute_client_list.v):
  This program sends computation requests and receives their results in parallel,
  analogous to the producer-consumer pattern. It uses a lock to share the channel
  and a shared counter, that keeps track of the number of computations in transit.
  The computation service can be found in
  [theories/logrel/examples/compute_service.v](../theories/logrel/examples/compute_service.v).
  The definition of the list type and the weakest precondition for `llength`
  can be found in [theories/logrel/lib/list.v](../theories/logrel/lib/list.v)
  It is type checked using a manual typing proof.
