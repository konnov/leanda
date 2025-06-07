/-
Necessary proofs of the standard facts in temporal logic.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic

variable {Val: Type} [DecidableEq Val]

def TraceProp := ℕ → Val → Prop

/--
  For a finite set of values `vs` and a state proposition `P`, show that we can
  swap a universal quantifier and eventually-always. In temporal logic `∀ v ∈
  vs, <>[](P v) → <>[](∀ v ∈ vs, P v)`.
  -/
theorem forall_FG_implies_FG_forall
    (P: TraceProp)
    (vs: Finset Val):
    (∀ v ∈ vs, ∃ k: ℕ, ∀ i: ℕ, P (k + i) v) →
      (∃ k: ℕ, ∀ i: ℕ, ∀ v ∈ vs, P (k + i) v) := by
  -- We prove our goal by induction over the set `X`,
  -- by growing it from ∅ up to `vs`, and showing `Q` every time.
  let Q := fun (X: Finset Val) =>
    (∀ v ∈ X, ∃ k: ℕ, ∀ i: ℕ, P (k + i) v)
      → (∃ k: ℕ, ∀ i: ℕ, ∀ v ∈ X, P (k + i) v)
  have base: Q ∅ := by
    -- when `C = ∅`, our statement is trivially true
    unfold Q; simp
  have step: ∀ v: Val, ∀ X: Finset Val, v ∉ X → Q X → Q (insert v X) := by
    intro v X h_v_not_in_X h_Q
    unfold Q; unfold Q at h_Q
    intro h_F_P_v_X
    -- prove that for all elements of `X`, eventually `P` holds true forever
    have h_X_F_P:
        ∀ x ∈ X,
          ∃ k: ℕ,
            ∀ i: ℕ,
              P (k + i) x := by
      intro x h_x_in_X
      have h_F_P_x := h_F_P_v_X x
      have : x ∈ insert v X := by
        apply Finset.mem_insert_of_mem
        exact h_x_in_X
      exact h_F_P_x this
    have h_F_P_X := h_Q h_X_F_P
    rcases h_F_P_X with ⟨k_X, h_G_P_X⟩
    -- prove that for `v`, eventually `P` holds true forever
    have h_F_P_v: ∃ k: ℕ, ∀ i: ℕ, P (k + i) v := by
      have h_F_P_v := h_F_P_v_X v
      have : v ∈ insert v X := by simp [Finset.mem_insert_of_mem]
      exact h_F_P_v this
    rcases h_F_P_v with ⟨k_v, h_G_P_v⟩
    -- now, simply choose the maximum of `k_v` and `k_X` as the witness
    let k_max := max k_v k_X
    use k_max
    -- ...and prove the goal for { v } ∪ X
    intro i y y_in_v_X
    by_cases h_y_eq_v: y = v
    case pos =>
      -- `y = v`, invoke `h_v`
      let j := k_max + i - k_v
      have h_reindex: k_v + j = k_max + i := by omega
      have h_v := h_G_P_v j
      rw [h_reindex] at h_v
      rw [h_y_eq_v]
      exact h_v

    case neg =>
      -- `y ≠ v`, hence, `y ∈ X` and we invoke `h_X`
      let j := k_max + i - k_X
      have h_reindex: k_X + j = k_max + i := by omega
      have h_y_in_X: y ∈ X := by
        simp [Finset.mem_insert_of_mem, h_y_eq_v] at y_in_v_X
        exact y_in_v_X
      have h_X := h_G_P_X j y h_y_in_X
      rw [h_reindex] at h_X
      exact h_X
  -- now apply the induction on finite sets
  exact Finset.induction base step vs
