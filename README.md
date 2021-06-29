# ACTRIS COQ DEVELOPMENT

This repository contains:
- The Coq mechanization of the Actris framework, first presented in the paper
[Actris: Session Type Based Reasoning in Separation Logic](https://iris-project.org/pdfs/2020-popl-actris-final.pdf)
at POPL'20
- The logical relations model for a semantic session type system, first presented in
the paper
[Machine-Checked Semantic Session Typing](https://iris-project.org/pdfs/2021-cpp-sessions-final.pdf)

It has been built and tested with the following dependencies

 - Coq 8.13.2
 - The version of Iris in the [opam file](opam)

In order to build, install the above dependencies and then run
`make -j [num CPU cores]` to compile Actris.

## Theory of Actris

The theory of Actris (semantics of channels, the model, and the proof rules)
can be found in the directory [theories/channel](theories/channel).
The individual types contain the following:

- [theories/channel/proto_model.v](theories/channel/proto_model.v): The
  construction of the model of dependent separation protocols as the solution of
  a recursive domain equation.
- [theories/channel/proto.v](theories/channel/proto.v): The instantiation of
  protocols with the Iris logic, definition of `iProto_own` for channel endpoint
  ownership, and lemmas corresponding to the Actris proof rules.
  The relevant definitions and proof rules are as follows:
  + `iProto Σ`: The type of protocols.
  + `iProto_message`: The constructor for sends and receives.
  + `iProto_end`: The constructor for terminated protocols.
  + `iProto_le`: The subprotocol relation for protocols (notation `⊑`).
- [theories/channel/channel.v](theories/channel/channel.v): The encoding of
  bidirectional channels in terms of Iris's HeapLang language, with specifications
  defined in terms of the dependent separation protocols.
  The relevant definitions and proof rules are as follows:
  + `iProto_mapsto`: endpoint ownership (notation `↣`).
  + `new_chan_spec`, `send_spec` and `recv_spec`: proof rule for `new_chan`,
	`send`, and `recv`.
  + `select_spec` and `branch_spec`: proof rule for the derived (binary)
	`select` and `branch` operations.

## Notation

The following table gives a mapping between the notation in literature
and the Coq mechanization:

Dependent Separation Protocols:

|        | POPL20 paper                  | Coq mechanization                     |
|--------|-------------------------------|---------------------------------------|
| Send   | `! x_1 .. x_n <v>{ P }. prot` | `<! x_1 .. x_n> MSG v {{ P }}; prot`  |
| Recv   | `? x_1 .. x_n <v>{ P }. prot` | `<? x_1 .. x_n> MSG v {{ P }}; prot`  |
| End    | `end`                         | `END`                                 |
| Select | `prot_1 {Q_1}⊕{Q_2} prot_2`   | `prot_1 <{Q_1}+{Q_2}> prot_2`         |
| Branch | `prot_1 {Q_1}&{Q_2} prot_2`   | `prot_1 <{Q_1}&{Q_2}> prot_2`         |
| Append | `prot_1 · prot_2`             | `prot_1 <++> prot_2`                  |
| Dual   | An overlined protocol         | No notation                           |

This notation is additionally used for the LMCS submission.

Semantic Session Types:

|          | CPP21 submission              | Coq mechanization                     |
|----------|-------------------------------|---------------------------------------|
| Send     | `!_{X_1 .. X_n} A . S`        | `<!! X_1 .. X_n> TY A ; S`            |
| Recv     | `?_{X_1 .. X_n} A . S`        | `<?? X_1 .. X_n> TY A ; S`            |
| End      | `end`                         | `END`                                 |
| Select   | `(+){ Ss }`                   | `lty_choice SEND Ss`                  |
| Branch   | `&{ Ss }`                     | `lty_choice RECV Ss`                  |
| Dual     | An overlined type             | No notation                           |
| N-append | `S^n`                         | lty_napp S n                          |

## Coq tactics

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

## Semantic Session Type System

The logical relation for type safety of a semantic session type system is contained
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

## Paper-specific remarks

For remarks about the paper-specific submissions, see

- [papers/POPL20.md](papers/POPL20.md)
- [papers/CPP21.md](papers/CPP21.md)
- [papers/LMCS.md](papers/LMCS.md)
