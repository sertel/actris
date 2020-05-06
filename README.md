# ACTRIS COQ DEVELOPMENT

This directory contains the artifact for the paper "Actris: Session Type
Based Reasoning in Separation Logic".

It has been built and tested with the following dependencies

 - Coq 8.11.1
 - The version of Iris in the [opam file](opam)

In order to build, install the above dependencies and then run
`make -j [num CPU cores]` to compile Actris.

## Semantic Session Type System
The logical relation for type safety of a semantic session type system is contained
in the directory [theories/logrel](theories/logrel). The logical relation is
defined across the following files:

- [theories/logrel/model.v](theories/logrel/model.v): Definition of the
  notions of a semantic term type and a semantic session type in terms of
  unary Iris predicates (on values) and Actris protocols, respectively. Also
  provides the required Coq definitions for creating recursive term/session
  types.
- [theories/logrel/term_types.v](theories/logrel/term_types.v): Definitions
  of the following semantic term types: basic types (integers, booleans,
  unit), sums, products, copyable/affine functions, universally and
  existentially quantified types, unique/shared references, and
  session-typed channels.
- [theories/logrel/session_types.v](theories/logrel/session_types.v):
  Definitions of the following semantic session types: sending and receiving
  with session polymorphism, n-ary choice. Session type duality is also
  defined here. As mentioned, recursive session types can be defined using
  the mechanism defined in [theories/logrel/model.v](theories/logrel/model.v).
- [theories/logrel/environments.v](theories/logrel/environments.v):
  Definition of semantic type environments, which are used in the semantic
  typing relation. This also contains the rules for splitting and copying of
  environments, which is used for distributing affine resources across the
  various parts of the program inside the typing rules.
- [theories/logrel/term_typing_judgment.v](theories/logrel/term_typing_judgment.v):
  Definition of the semantic typing relation, as well as the proof of type
  soundness, showing that semantically well-typed programs do not get stuck.
- [theories/logrel/subtyping.v](theories/logrel/subtyping.v): Definition of
  the semantic subtyping relation for both term and session types. This file
  also defines the notion of copyability of types in terms of subtyping.
- [theories/logrel/term_typing_rules.v](theories/logrel/term_typing_rules.v):
  Semantic typing lemmas (typing rules) for the semantic term types.
- [theories/logrel/session_typing_rules.v](theories/logrel/session.v):
  Semantic typing lemmas (typing rules) for the semantic session types.
- [theories/logrel/subtyping_rules.v](theories/logrel/subtyping_rules.v): Subtyping rules for term types and
  session types.

An extension to the basic type system is given in
[theories/logrel/lib/mutex.v](theories/logrel/lib/mutex.v), which defines
mutexes as a type-safe abstraction. Mutexes are implemented using spin locks
and allow one to gain exclusive ownership of resource shared between multiple
threads.

The logical relation is used to show that two example programs are semantically well-typed:
- [theories/logrel/examples/pair.v](theories/logrel/examples/pair.v):
  This program performs
  two sequential receives and stores the results in a pair. It is shown to be
  semantically well-typed by applying the semantic typing rules.
- [theories/logrel/examples/double.v](theories/logrel/examples/double.v): This program
  performs two ``racy'' parallel receives on the same channel from two
  different threads, using locks to allow the channel to be shared. This
  program cannot be shown to be well-typed using the semantic typing rules.
  Therefore, a manual proof of the well-typedness is given.
- [theories/examples/subprotocols.v](theories/examples/subprotocols.v):
  Contains an example of a subprotocol assertion between two protocols that sends
  references.

## Theory of Actris

The theory of Actris (semantics of channels, the model, and the proof rules)
can be found in the directory [theories/channel](theories/channel). The files
correspond to the following parts of the paper:

- [theories/channel/channel.v](theories/channel/channel.v): The definitional
  semantics of bidirectional channels in terms of Iris's HeapLang language.
- [theories/channel/proto_model.v](theories/channel/proto_model.v): The
  construction of the model of Dependent Separation Protocols as the solution of
  a recursive domain equation.
- [theories/channel/proto_channel.v](theories/channel/proto_channel.v): The
  instantiation of protocols with the Iris logic, definition of the connective `↣`
  for channel endpoint ownership, and lemmas corresponding to the Actris proof rules.
  The relevant definitions and proof rules are as follows:
  + `iProto Σ`: The type of protocols.
  + `iProto_message`: The constructor for sends and receives.
  + `iProto_end`: The constructor for terminated protocols.
  + `mapsto_proto`: endpoint ownership `↣`.
  + `new_chan_proto_spec`: proof rule for `new_chan`.
  + `send_proto_spec` and `send_proto_spec_packed`: proof rules for `send`, the
    first version is more convenient to use in Coq, but otherwise the same as
    the latter, which is the rule in the paper.
  + `recv_proto_spec` and `recv_proto_spec_packed`: proof rules for `recv`, the
    first version is more convenient to use in Coq, but otherwise the same as
    the latter, which is the rule in the paper.
  + `select_spec`: proof rule for `select`.
  + `branch_spec`: proof rule for `branch`.

## Notation

The following table gives a mapping between the notation in the paper and the
Coq mechanization:

|        | Paper                         | Coq mechanization                     |
|--------|-------------------------------|---------------------------------------|
| Send   | `! x_1 .. x_n <v>{ P }. prot` | `<!> x_1 .. x_n, MSG v {{ P }}; prot` |
| Recv   | `? x_1 .. x_n <v>{ P }. prot` | `<?> x_1 .. x_n, MSG v {{ P }}; prot` |
| End    | `end`                         | `END`                                 |
| Select | `prot_1 {Q_1}⊕{Q_2} prot_2`   | `prot_1 <{Q_1}+{Q_2}> prot_2`         |
| Branch | `prot_1 {Q_1}&{Q_2} prot_2`   | `prot_1 <{Q_1}&{Q_2}> prot_2`         |
| Append | `prot_1 · prot_2`             | `prot_1 <++> prot_2`                  |
| Dual   | An overlined protocol         | No notation                           |

## Weakest preconditions and Coq tactics

The presentation of Actris logic in the paper makes use of Hoare triples. In
Coq, we make use of weakest preconditions because these are more convenient for
interactive theorem proving using the the [proof mode tactics][ProofMode]. To
state concise program specifications, we use the notion of *Texan Triples* from
Iris, which provides a convenient "Hoare triple"-like syntax around weakest
preconditions:

```
{{{ P }}} e {{{ x .. y, RET v; Q }}} :=
  □ ∀ Φ, P -∗ ▷ (∀ x .. y, Q -∗ Φ v) -∗ WP e {{ Φ }}
```

In order to prove programs using Actris, one can make use of a combination of
[Iris's symbolic execution tactics for HeapLang programs][HeapLang] and
[Actris's symbolic execution tactics for message passing][ActrisProofMode]. The
Actris tactics are as follows:

- `wp_send (t1 .. tn) with "selpat"`: symbolically execute `send c v` by looking
  up ownership of a send protocol `H : c ↣ <!> y1 .. yn, MSG v; {{ P }}; prot`
  in the proof mode context. The tactic instantiates the variables `y1 .. yn`
  using the terms `t1 .. tn` and uses `selpat` to prove `P`. If fewer terms
  `t` are given than variables `y`, they will be instantiated using existential
  variables (evars). The tactic will put `H : c ↣ prot` back into the context.
- `wp_recv (x1 .. xn) as "ipat"`: symbolically execute `recv c` by looking up
  `H : c ↣  <?> y1 .. yn, MSG v; {{ P }}; prot` in the proof mode context. The
  variables `y1 .. yn` are introduced as `x1 .. xn`, and the predicate `P` is
  introduced using the introduction pattern `ipat`. The tactic will put
  `H : c ↣ prot` back into the context.
- `wp_select with "selpat"`: symbolically execute `select c b` by looking up
  `H : c ↣  prot1 {Q1}<+>{Q2} prot2` in the proof mode context. The selection
  pattern `selpat` is used to resolve either `Q1` or `Q2`, based on the chosen
  branch `b`. The tactic will put `H : c ↣  prot1` or `H : c ↣ prot2` back
  into the context based on the chosen branch `b`.
- `wp_branch as ipat1 | ipat2`: symbolically execute `branch c e1 e2` by looking
  up `H : c ↣ prot1 {Q1}<&>{Q2} prot2` in the proof mode context. The result of
  the tactic involves two subgoals, in which `Q1` and `Q2` are introduced using
  the introduction patterns `ipat1` and `ipat2`, respectively. The tactic will
  put `H : c ↣ prot1` and `H : c ↣ prot2` back into the contexts of the two
  respectively goals.

The above tactics implicitly perform normalization of the protocol `prot` in
the hypothesis `H : c ↣ prot`. For example, `wp_send` also works if there is a
channel with the protocol `iProto_dual ((<?> y1 .. yn, MSG v; {{ P }}; END) <++> prot)`.
Concretely, the normalization performs the following actions:

- It re-associates appends (`<++>`), and removes left-identities (`END`) of it.
- It moves appends (`<++>`) into sends (`<!>`), receives (`<?>`), selections
  (`<+>`) and branches (`<&>`).
- It distributes duals (`iProto_dual`) over append (`<++>`).
- It unfolds `prot1` into `prot2` if there is an instance of the type class
  `ProtoUnfold prot1 prot2`. When defining a recursive protocol, it is
  useful to define a `ProtoUnfold` instance to obtain automatic unfolding
  of the recursive protocol. For example, see `sort_protocol_br_unfold` in
  [theories/examples/sort_br_del.v](theories/examples/sort_br_del.v).

[HeapLang]: https://gitlab.mpi-sws.org/iris/iris/blob/master/HeapLang.md
[ProofMode]: https://gitlab.mpi-sws.org/iris/iris/blob/master/ProofMode.md
[ActrisProofMode]: theories/channel/proofmode.v

## Examples

The examples can be found in the direction [theories/examples](theories/examples).

The following list gives a mapping between the examples in the paper and their
mechanization in Coq:

1. Introduction: [theories/examples/basics.v](theories/examples/basics.v)
2. Tour of Actris
   - 2.3 Basic: [theories/examples/sort.v](theories/examples/sort.v)
   - 2.4 Higher-Order Functions: [theories/examples/sort.v](theories/examples/sort.v)
   - 2.5 Branching: [theories/examples/sort_br_del.v](theories/examples/sort_br_del.v)
   - 2.6 Recursion: [theories/examples/sort_br_del.v](theories/examples/sort_br_del.v)
   - 2.7 Delegation: [theories/examples/sort_br_del.v](theories/examples/sort_br_del.v)
   - 2.8 Dependent: [theories/examples/sort_fg.v](theories/examples/sort_fg.v)
3. Manifest sharing via locks
   - 3.1 Sample program: [theories/examples/basics.v](theories/examples/basics.v)
   - 3.2 Distributed mapper: [theories/examples/map.v](theories/examples/map.v)
4. Case study: map reduce:
   - Utilities for shuffling/grouping: [theories/utils/group.v](theories/utils/group.v)
   - Implementation and verification: [theories/examples/map_reduce.v](theories/examples/map_reduce.v)

## Differences between the formalization and the paper

There are a number of small differences between the paper presentation
of Actris and the formalization in Coq, that are briefly discussed here.

- **Notation**

  See the section "Notation" above.

- **Weakest preconditions versus Hoare triples**

  See the section "Weakest preconditions and Coq tactics" above.

- **Connectives for physical ownership of channels**

  In the paper, physical ownership of a channel is formalized using a single
  connective `(c1,c2) ↣ (vs1,vs2)`, while the mechanization has two connectives
  for the endpoints and one for connecting them, namely:
  - `chan_own γ Left vs1` and `chan_own γ Right vs1`
  - `is_chan N γ c1 c2`

  Here, `γ` is a ghost name and `N` an invariant name. This setup is less
  intuitive but gives rise to a more practical Jacobs/Piessens-style spec of
  `recv` that does not need a closing view shift (to handle the case that the
  buffer is empty).

- **Later modalities in primitive rules for channels**

  The primitive rules for `send` and `recv` (`send_spec` and `recv_spec` in
  [theories/channel/channel.v](theories/channel/channel.v)) contain three later
  (`▷`) modalities, which are omitted for brevity's sake in the paper. These
  later modalities expose that these operations perform at least three steps in
  the operational semantics, and are needed to deal with the three levels of
  indirection in the invariant for protocols:
  1. the `▶` in the model of protocols,
  2. the higher-order ghost state used for ownership of protocols, and
  3. the opening of the protocol invariant.

- **Protocol subtyping**

  The mechanization has introduced the notion of "protocol subtyping", which
  allows one to strengthen/weaken the predicates of sends/receives, respectively.
  This achieved using the relation `iProto_le p p'`, and the additional rule
  `c ↣ p -∗ iProto_le p p' -∗ c ↣ p'`. To support "protocol subtyping", the
  definition of `c ↣ p` in the model is changed to be closed under `iProto_le`.
