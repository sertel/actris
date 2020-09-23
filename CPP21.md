# Code corresponding to the paper

The material of the CPP'21 submission is contained
in the directory [theories/logrel](theories/logrel).
The logical relation is defined across the following files:

- [theories/logrel/model.v](theories/logrel/model.v): Definition of the
  notions of a semantic term type and a semantic session type in terms of
  unary Iris predicates (on values) and Actris protocols, respectively. Also
  provides the required Coq definitions for creating recursive term/session
  types.
- [theories/logrel/term_types.v](theories/logrel/term_types.v): Definitions
  of the following semantic term types: basic types (integers, booleans, unit),
  sums, products, copyable/affine functions, universally and existentially
  quantified types, unique/shared references, and session-typed channels.
- [theories/logrel/session_types.v](theories/logrel/session_types.v):
  Definitions of the following semantic session types: sending and receiving
  with session polymorphism, n-ary choice. Session type duality is also
  defined here. Recursive session types can be defined using the mechanism
  defined in [theories/logrel/model.v](theories/logrel/model.v).
- [theories/logrel/operators.v](theories/logrel/operators.v):
  Type definitions of unary and binary operators.
- [theories/logrel/contexts.v](theories/logrel/contexts.v):
  Definition of the semantic type contexts, which is used in the semantic
  typing relation. This also contains the rules for updating the context,
  which is used for distributing affine resources across the
  various parts of the proofs inside the typing rules.
- [theories/logrel/term_typing_judgment.v](theories/logrel/term_typing_judgment.v):
  Definition of the semantic typing relation, as well as the proof of type
  soundness, showing that semantically well-typed programs do not get stuck.
- [theories/logrel/subtyping.v](theories/logrel/subtyping.v):
  Definition of the semantic subtyping relation for both term and session types.
  This file also defines the notion of copyability of types in terms of subtyping.
- [theories/logrel/subtyping_rules.v](theories/logrel/subtyping_rules.v):
  Subtyping rules for term types and session types.
- [theories/logrel/term_typing_rules.v](theories/logrel/term_typing_rules.v):
  Semantic typing lemmas (typing rules) for the semantic term types.
- [theories/logrel/session_typing_rules.v](theories/logrel/session_typing_rules.v):
  Semantic typing lemmas (typing rules) for the semantic session types.
- [theories/logrel/napp.v](theories/logrel/napp.v):
  Definition of session types iteratively being appended to themselves a finite
  number of times, with support for swapping e.g. a send over an arbitrary number
  of receives.

An extension to the basic type system is given in
[theories/logrel/lib/mutex.v](theories/logrel/lib/mutex.v), which defines
mutexes as a type-safe abstraction. Mutexes are implemented using spin locks
and allow one to gain exclusive ownership of resources shared between multiple
threads. An encoding of a list type is found in
[theories/logrel/lib/mutex.v](theories/logrel/lib/mutex.v), along with axillary
lemmas, and a weakest precondition for `llength`,
that converts ownership of a list type into a list reference predicate, with
the values of the list made explicit.

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
  a `Context`, rather than as implicits variables of the definitions.
  The definitions between the paper and Coq code are identical,
  as this is just refactoring.

# Examples from the paper

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
