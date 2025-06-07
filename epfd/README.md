# EPFD: Eventually Perfect Failure Detector

This directory contains a Lean specification of an eventually perfect failure
detector under partial synchrony, as presented in the [Introduction to Reliable
and Secure Distributed Programming][DP2011], Algorithm 2.7, p. 55.

The specification has the following structure:

 - [Basic.lean](./Epfd/Basic.lean) contains the basic type definitions.

 - [Propositional.lean](./Epfd/Propositional.lean) is the protocol spec in the
 form of propositions that look quite similar to TLA<sup>+</sup> actions.
 Additionally, it contains the definitions of fairness and the expected
 properties.
 
 - [PropositionalProofs.lean](./Epfd/PropositionalProofs.lean) contains lemmas
 and theorems that show correctness of the protocol w.r.t. the expected
 properties. Currently, we prove only strong completeness. Strong accuracy is
 work in progress.
 
 - [TemporalLemmas.lean](./Epfd/TemporalLemmas.lean) contains additional
 theorems of temporal logic that help us to construct the main proofs.
 
[DP2011]: https://www.distributedprogramming.net/