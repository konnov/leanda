/-
Shared prelude for the generated Tendermint definitions.

This is kept in sync with `Wunderspec.Prelude` from wunderspec-lean so the
standalone LeanDA project does not depend on a sibling checkout.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finmap
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Interval

/-- A flat, generated-source spelling of a right-associated conjunction.
`ws_and [p, q, r]` expands to `p ∧ q ∧ r`; the list notation keeps long
Wunderspec conjunctions aligned without changing their elaborated shape. -/
syntax "ws_and" " [" term,* "]" : term

macro_rules
  | `(ws_and []) => `(True)
  | `(ws_and [$p]) => `($p)
  | `(ws_and [$p, $ps,*]) => `($p ∧ ws_and [$ps,*])

namespace Wunderspec.Prelude

end Wunderspec.Prelude

attribute [instance 0] Classical.propDecidable

def Finmap.lookupD {α : Type u} {β : Type v} [DecidableEq α] [Inhabited β]
    (a : α) (m : Finmap (fun _ : α => β)) : β :=
  (m.lookup a).getD default

instance {α : Type u} {β : Type v} : Inhabited (Finmap (fun _ : α => β)) := ⟨∅⟩

noncomputable def Finmap.ofFinset {α : Type u} {β : Type v} [DecidableEq α]
    (s : Finset α) (f : α → β) : Finmap (fun _ : α => β) :=
  s.toList.foldr (fun a m => Finmap.insert a (f a) m) ∅
