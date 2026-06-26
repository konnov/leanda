/-
Shared prelude for generated `<spec>_defs.lean` files (Step B output).

For now this only pulls in the Mathlib data structures the lowering targets
(`Finset` for sets, `Finmap` for maps, integers). Helper lemmas and notation
shared across generated specs will accrue here.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finmap
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Interval

namespace Wunderspec.Prelude

end Wunderspec.Prelude

/-
Classical decidability as a **low-priority** fallback. `Finset.filter`/`Finset.card`
need a `DecidablePred`; most lowered predicates synthesize one structurally (bounded
quantifiers + `DecidableEq`), but some — e.g. a `setFilter` whose predicate nests
another `setFilter` under an existential — do not. The low priority means the
structural instance is still preferred wherever it exists; this only supplies a
decision for the remainder. Generated defs are proof-facing `Prop`s that are never
executed, and a filter's *set* is independent of which (propositionally-equal)
decidability instance it uses, so this changes no stated proposition. -/
attribute [instance 0] Classical.propDecidable

/--
Total lookup on a (constant-value) finite map: the stored value at `a`, or the
`default` if `a` is absent.

The lowering (Step B) represents Wunderspec maps `k ↦ v` as
`Finmap (fun _ : k => v)` and reads them with `lookupD`, so that map values used
in arithmetic / comparisons / set operations are honest `v`s rather than
`Option v`. The generated `Wf` predicate pins down each map's `keys`, so under
`Wf` the `default` branch is never taken and `lookupD` agrees with `lookup`.
-/
def Finmap.lookupD {α : Type u} {β : Type v} [DecidableEq α] [Inhabited β]
    (a : α) (m : Finmap (fun _ : α => β)) : β :=
  (m.lookup a).getD default

/-- Any (constant-value) finite map is inhabited by the empty map. Needed so that
nested maps (`map k (map k' v)`) can be read with `lookupD`, whose value type is
itself a `Finmap`. -/
instance {α : Type u} {β : Type v} : Inhabited (Finmap (fun _ : α => β)) := ⟨∅⟩

/--
Construct a (constant-value) finite map with domain `s`, sending each `a ∈ s` to
`f a`. The keys of `s` are distinct, so the insertion order is irrelevant.

The Wunderspec map-comprehension `Map(f x for x ∈ s)` lowers to this when it
occurs in a *term* (value) position — e.g. the value written by an `insert`, or a
map nested inside another map. An assignment RHS is instead *characterized* (keys
+ pointwise lookups), which is more proof-friendly (see Lower.lean).

`noncomputable` because `Finset.toList` is — harmless here, as the generated defs
are proof-facing `Prop`s that are never executed. -/
noncomputable def Finmap.ofFinset {α : Type u} {β : Type v} [DecidableEq α]
    (s : Finset α) (f : α → β) : Finmap (fun _ : α => β) :=
  s.toList.foldr (fun a m => Finmap.insert a (f a) m) ∅
