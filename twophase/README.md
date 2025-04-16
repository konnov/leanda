# Two-phase commit in Lean 4

This is a manual translation of Lamport's TLA<sup>+</sup> specification of
[Two-phase commit][] into Lean 4. Since Lean 4 is not specifically designed for
specifying distributed systems &mdash; in contrast to TLA<sup>+</sup> &mdash; we
have to make a few choices. In particular, we split the specification into two
layers:

 - The functional layer: [Functional.lean][] specifies the steps of resource
 managers and the transaction manager as **functions**. Every such function
 returns `Option ProtocolState`, that is, either a new protocol state, or
 `none`, if the function arguments are not applicable to the given state.
 
 - The system layer: [System.lean][] specifies a single step of the whole system
 that is composed of the transaction manager and several resource managers.
 Since Lean 4 does not have a built-in notion of TLA<sup>+</sup> actions, we
 shift non-determinism to the inputs. That is, `next` becomes a function of a
 decision made by the scheduler (or adversary).

Finally, [Twophase3.lean][] contains a simple random simulator for three
resource managers. Given a number of steps $n$ and a seed $seed$, it runs the
protocol up to $n$ steps, using a pseudo-random number generator:

```sh
$ lake exe Twophase3 100 4449
action 0: Action.TMAbort
action 1: Action.RMPrepare (RM.RM2)
action 4: Action.RMPrepare (RM.RM3)
action 13: Action.RMRcvAbortMsg (RM.RM1)
action 17: Action.RMRcvAbortMsg (RM.RM3)
action 24: Action.RMRcvAbortMsg (RM.RM3)
action 29: Action.RMRcvAbortMsg (RM.RM3)
action 30: Action.RMRcvAbortMsg (RM.RM3)
action 46: Action.RMRcvAbortMsg (RM.RM1)
action 51: Action.RMRcvAbortMsg (RM.RM2)
action 55: Action.RMRcvAbortMsg (RM.RM1)
action 78: Action.RMRcvAbortMsg (RM.RM3)
action 87: Action.RMRcvAbortMsg (RM.RM3)
action 89: Action.RMRcvAbortMsg (RM.RM3)
action 91: Action.RMRcvAbortMsg (RM.RM1)
action 98: Action.RMRcvAbortMsg (RM.RM3)
```

Since it's hard to pick up seeds, you can use the current number of seconds as a
seed:

```sh
$ lake exe Twophase3 100 `date +%s`
```

[Two-phase commit]: https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla
[Functional.lean]: ./Twophase/Functional.lean
[System.lean]: ./Twophase/System.lean
[Twophase3.lean]: ./Twophase3.lean