The state of the repository at the time of publication can be found at
[https://gitlab.mpi-sws.org/iris/actris/-/tree/POPL20](https://gitlab.mpi-sws.org/iris/actris/-/tree/POPL20)

## Examples

The examples can be found in the directory [theories/examples](../theories/examples).

The following list gives a mapping between the examples in the paper and their
mechanization in Coq:

Introduction: [theories/examples/basics.v](../theories/examples/basics.v)
Tour of Actris
  - Basics: [theories/examples/sort.v](../theories/examples/sort.v)
  - Higher-Order Functions: [theories/examples/sort.v](../theories/examples/sort.v)
  - Choice: [theories/examples/sort_br_del.v](../theories/examples/sort_br_del.v)
  - Recursion: [theories/examples/sort_br_del.v](../theories/examples/sort_br_del.v)
  - Delegation: [theories/examples/sort_br_del.v](../theories/examples/sort_br_del.v)
  - Dependent: [theories/examples/sort_fg.v](../theories/examples/sort_fg.v)
Manifest sharing via locks
  - Sample program: [theories/examples/basics.v](../theories/examples/basics.v)
  - Distributed mapper: [theories/examples/par_map.v](../theories/examples/par_map.v)
Case study: map reduce:
  - Utilities for shuffling/grouping: [theories/utils/group.v](../theories/utils/group.v)
  - Implementation and verification: [theories/examples/map_reduce.v](../theories/examples/map_reduce.v)

## Differences between the formalization and the paper

There are a number of small differences between the paper presentation
of Actris and the formalization in Coq, that are briefly discussed here.

**Weakest preconditions versus Hoare triples**

The presentation of the Actris logic in the paper makes use of Hoare triples.
In Coq, we make use of weakest preconditions because these are more convenient for
interactive theorem proving using the the [proof mode tactics][ProofMode]. To
state concise program specifications, we use the notion of *Texan Triples* from
Iris, which provides a convenient "Hoare triple"-like syntax around weakest
preconditions:

```
{{{ P }}} e {{{ x .. y, RET v; Q }}} :=
  □ ∀ Φ, P -∗ ▷ (∀ x .. y, Q -∗ Φ v) -∗ WP e {{ Φ }}
```

**Connectives for physical ownership of channels**

In the paper, physical ownership of a channel is formalized using a single
connective `(c1,c2) ↣ (vs1,vs2)`. Since then we have made the Actris
hoare triples the primitive specification for the channels, and instead
defined channel ownership directly in terms of the buffer ownership
`llist internal_eq l vs1` and `llist intenral_eq r vs2` for channels
`(l,r,lk)` and `(r,l,lk)`.

**Protocol subtyping**

The mechanization has introduced the notion of "protocol subtyping", which
allows one to strengthen/weaken the predicates of sends/receives, respectively.
This is achieved using the relation `iProto_le p p'`, and the additional rule
`c ↣ p -∗ iProto_le p p' -∗ c ↣ p'`. To support "protocol subtyping", the
definition of `c ↣ p` in the model is changed to be closed under `iProto_le`.
This idea is formally presented in the LMCS submission.
