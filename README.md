# LeanDA: Distributed Algorithms in Lean 4

[![Lean actions](https://github.com/konnov/leanda/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/konnov/leanda/actions/workflows/lean_action_ci.yml)

This repository contains my experiments with Lean 4. The main purpose is to see
how Lean's features match the features of TLA<sup>+</sup>.

Available specifications:

 - [Two-phase commit](./twophase/README.md). See the [blog
   post 1](https://protocols-made-fun.com/lean/2025/04/25/lean-two-phase.html) on specification
   and [blog post 2](https://protocols-made-fun.com/lean/2025/05/10/lean-two-phase-proofs.html) in proofs with Lean4:

   - [Functional specification](./twophase/Twophase/Functional.lean)
   - [System specification](./twophase/Twophase/System.lean)
   - [Propositional specification](./twophase/Twophase/Propositional.lean)
   - [Functional-propositional refinement proofs](./twophase/Twophase/PropositionalProofs.lean)
   - [Safety proofs via inductive invariants](./twophase/Twophase/InductiveProofs.lean)
 
