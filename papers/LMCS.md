## Examples

The examples of the original POPL20 paper are covered in
[papers/POPL20.md](POPL20.md).

The following list gives a mapping between the additional examples in the
paper and their mechanization in Coq:

Introduction
  - Swapping program: [theories/examples/basics.v](../theories/examples/basics.v)
Subprotocols
  - Basics: [theories/examples/subprotocols.v](../theories/examples/subprotocols.v)
  - Mapper: [theories/examples/swap_mapper.v](../theories/examples/swap_mapper.v)
  - List reversal: [theories/examples/list_rev.v](../theories/examples/list_rev.v)
  - Löb recursion: [theories/examples/subprotocols.v](../theories/examples/subprotocols.v)
Mechanization
  - Program: [theories/examples/basics.v](../theories/examples/basics.v)
  - Subprotocol: [theories/examples/list_rev.v](../theories/examples/list_rev.v)

## Differences between the formalization and the paper

There are a number of small differences between the paper presentation
of Actris 2.0 and the formalization in Coq, beyond those already covered
in [papers/POPL20.md](POPL20.md), that are briefly discussed here.

**Subprotocol rules with binders**

The paper presents a set of rules for the subprotocol relation with binders,
namely `⊑-send-mono'`, `⊑-recv-mono'`, and `⊑-swap'`. These are not available
in the mechanisation, for technical reasons related to the encoding of binders.
However, the rules are admissible from the primitive rules, as explained in the
paper. The consequence of this is observed in the proof of the Löb recursion
example, which differs from the proof presented in the paper, as it uses the
rules with binders.
