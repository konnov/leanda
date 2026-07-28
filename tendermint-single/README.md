# Single-Height Tendermint Byzantine Consensus in Lean 4

This directory contains a Lean proof of agreement for a single-height
Tendermint Byzantine consensus model.

The Lean definitions were generated from the Wunderspec model
[tendermint_single_indinv.py][]. The proof follows the TLAPS development
[tendermint_single_indinv_proofs.tla][]: it proves initialization and
transition preservation of the inductive invariant, derives the lock lemma, and
establishes agreement for every state in a protocol run.

The specification and proofs have the following structure:

 - [Prelude.lean](./TendermintSingle/Prelude.lean) contains the small local
   prelude needed by the generated definitions.

 - [Defs.lean](./TendermintSingle/Defs.lean) contains the generated protocol
   definitions, including state, initialization, transitions, the inductive
   invariant, and agreement.

 - [Basic.lean](./TendermintSingle/Proofs/Basic.lean) contains the model
   assumptions, named views of the generated invariant, and foundational
   quorum and transition lemmas.

 - [Inductive.lean](./TendermintSingle/Proofs/Inductive.lean) contains the
   `InitInd` and `NextInd` proofs. Its main theorems are
   `typed_ind_inv_init` and `typed_ind_inv_next`.

 - [Agreement.lean](./TendermintSingle/Proofs/Agreement.lean) contains the lock
   lemma and agreement proof. The final theorem is
   `tendermint_single_indinv.run_agreement`.

To build:

```sh
lake build
```

[tendermint_single_indinv.py]: https://github.com/wunderspec/wunderspec/blob/main/examples/tendermint_single_indinv.py
[tendermint_single_indinv_proofs.tla]: https://github.com/konnov/apalache-examples/blob/main/tendermint/tendermint_single_indinv_proofs.tla
