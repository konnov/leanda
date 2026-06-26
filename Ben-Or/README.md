# Ben-Or Byzantine Consensus in Lean 4

This directory contains a Lean proof of agreement for the Ben-Or 1983 Byzantine
consensus protocol.

The Lean definitions were generated from the Wunderspec Ben-Or model. The proof
module builds an inductive invariant from auxiliary lemmas and derives agreement
for every reachable state.

The specification has the following structure:

 - [Prelude.lean](./BenOr/Prelude.lean) contains the small local prelude needed
   by the generated definitions.

 - [Defs.lean](./BenOr/Defs.lean) contains the generated protocol definitions,
   including state, initialization, steps, assumptions, and `agreement_inv`.

 - [Proofs.lean](./BenOr/Proofs.lean) contains the Ben-Or agreement proof. The
   main theorem is `ben_or.agreement_inv_invariant`.

To build:

```sh
lake build
```
