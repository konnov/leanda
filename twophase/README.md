# Two-phase commit in Lean 4

## Layered specification

This is a manual translation of Lamport's TLA<sup>+</sup> specification of
[Two-phase commit][] into Lean 4. Since Lean 4 is not specifically designed for
specifying distributed systems &mdash; in contrast to TLA<sup>+</sup> &mdash; we
have to make a few choices. In particular, we split the specification into three
layers:

 - The **functional layer**: [Functional.lean][] specifies the steps of resource
 managers and the transaction manager as **functions**. Every such function
 returns `Option ProtocolState`, that is, either a new protocol state, or
 `none`, if the function arguments are not applicable to the given state.
 
 - The **system layer**: [System.lean][] specifies a single step of the whole
 system that is composed of the transaction manager and several resource
 managers.  Since Lean 4 does not have a built-in notion of TLA<sup>+</sup>
 actions, we shift non-determinism to the inputs. That is, `next` becomes a
 function of a decision made by the scheduler (or adversary).
 
 - The **propositional layer**: [Propositional.lean][] specifies TLA<sup>+</sup>
 as propositions. These definitions look very similar to their TLA<sup>+</sup>
 counterparts.

## Randomized simulator

The module [Twophase4_run.lean][] contains a simple random simulator for four
resource managers. Given the number of samples $n$, the number of steps $k$, the
invariant name, and the seed $seed$, it runs $n$ samples of the protocol up to
$k$ steps, using a pseudo-random number generator:

```sh
$ lake exec RunTwophase4 1000000 20 noAbortOnAllPreparedEx 1745505754
❌ Counterexample found after 97860 trials
#0: Action.RMPrepare (RM.RM3)
#1: Action.RMPrepare (RM.RM4)
#2: Action.RMPrepare (RM.RM2)
#3: Action.TMRcvPrepared (RM.RM2)
#4: Action.TMRcvPrepared (RM.RM4)
#5: Action.TMRcvPrepared (RM.RM3)
#6: Action.RMPrepare (RM.RM1)
#7: Action.TMRcvPrepared (RM.RM1)
#8: Action.TMAbort
```

Since it's hard to pick up seeds, you can use the current number of seconds as a
seed:

```sh
$ lake exec RunTwophase4 1000000 20 noAbortOnAllPreparedEx `date +%s`
```

## Property-based testing

Similar to the simulator, the module [Twophase4_pbt.lean][] checks protocol
invariants with [Plausible][].

[Two-phase commit]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla
[Functional.lean]: ./Twophase/Functional.lean
[Propositional.lean]: ./Twophase/Propositional.lean
[System.lean]: ./Twophase/System.lean
[Twophase4_run.lean]: ./Twophase4_run.lean
[Twophase4_pbt.lean]: ./Twophase4_pbt.lean
[Plausible]: https://github.com/leanprover-community/plausible