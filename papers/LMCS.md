## Examples

Differences from the original POPL20 paper along with examples thereof are covered in
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
in the mechanisation, as applying them can be cumbersome, due to the encoding of
the binders. However, the rules are admissible from the primitive rules, as
explained in the paper. Additionally, working with the tactics, as elaborated on
in the mechanisation section of the paper, is recommended. This can be observed in
the proof of the Löb recursion example, which differs from the proof presented in
the paper.
