/-
Copyright 2023 The Authors
Released under Apache 2.0 license as described in the file LICENSE
Authors: Guillaume Dubach, Marco Lenci, Sébastien Gouëzel, Marcello Seri, Oliver Butterley, Lorenzo Luccioli, Pietro Monticone
-/

import «BET».Topological

/-!
# Minimal sets

This file contains various details related to minimal sets and minimal actions.

TO DO:
- Align contents here with https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Dynamics/Minimal.lean
- Upgrade the statements and proofs swapping the metric space requirement for merely requiring a topological space.
- Upgrade all for a general action as per the stuff already in mathlib.

-/

open MeasureTheory Filter Metric Function Set
open scoped omegaLimit
set_option autoImplicit false

variable {α : Type*} [MetricSpace α]
variable [CompactSpace α] (f : α → α) (hf : Continuous f)

/-- The minimal subsets are the closed invariant subsets in which all orbits are dense. -/
structure IsMinimalSubset (f : α → α) (U : Set α) : Prop :=
  (closed : IsClosed U)
  (invariant : IsInvariant (fun n x ↦ f^[n] x) U)
  (minimal : ∀ (x y : α) (_ : x ∈ U) (_ : y ∈ U) (ε : ℝ), ε > 0 → ∃ n : ℕ, f^[n] y ∈ ball x ε)

/-- A dynamical system (α,f) is minimal if α is a minimal subset. -/
def IsMinimal (f : α → α) : Prop := IsMinimalSubset f univ

/-- In a minimal dynamics, the recurrent set is all the space. -/
theorem recurrentSet_of_minimal_is_all_space (hf : IsMinimal f) (x : α) :
    x ∈ recurrentSet f := by
  have : ∀ (ε : ℝ) (N : ℕ), ε > 0 → ∃ m : ℕ, m ≥ N ∧ f^[m] x ∈ ball x ε := by
    intro ε N hε
    obtain ⟨n, hball⟩ : ∃ n, f^[n] (f^[N] x) ∈ ball x ε :=
      hf.minimal x (f^[N] x) (mem_univ _) (mem_univ _) ε hε
    exact ⟨n + N, by linarith, (Function.iterate_add_apply _ _ _ _).symm ▸ hball⟩
  exact (recurrentSet_iff_accumulation_point f x).mpr this

/-- An example of a continuous dynamics on a compact space in which the recurrent set is all
the space, but the dynamics is not minimal -/
example : ¬IsMinimal (id : unitInterval → unitInterval) := by
  intro H
  have minimality := H.minimal 0 1 (mem_univ 0) (mem_univ 1)
    ((dist (1 : unitInterval) (0 : unitInterval)) / 2)
  revert minimality; contrapose!; intro _
  -- we need this helper twice below
  have dist_pos : 0 < dist (1 : unitInterval) 0 :=
    dist_pos.mpr (unitInterval.coe_ne_zero.mp (by norm_num))
  refine' ⟨div_pos dist_pos (by norm_num), fun n ↦ _⟩
  simp only [iterate_id, id_eq, mem_ball, not_lt, half_le_self_iff]
  exact le_of_lt dist_pos

example (x : unitInterval) : x ∈ recurrentSet (id : unitInterval → unitInterval) :=
  periodicpts_mem_recurrentSet _ _ 1 (by norm_num) (is_periodic_id 1 x)


/-- Every point in a minimal subset is recurrent. -/
theorem minimalSubset_mem_recurrentSet (U : Set α) (hU : IsMinimalSubset f U) :
    U ⊆ recurrentSet f := by
  intro x hx
  obtain ⟨_, hInv, hMin⟩ := hU
  apply (recurrentSet_iff_accumulation_point f x).mpr
  intro ε N hε
  obtain ⟨n, hball⟩ : ∃ n, f^[n] (f^[N] x) ∈ ball x ε :=
    hMin x (f^[N] x) hx (Set.mapsTo'.mp (hInv N) ⟨x, hx, rfl⟩) ε hε
  exact ⟨n + N, le_add_self, (Function.iterate_add_apply _ _ _ _).symm ▸ hball⟩

/-- Every invariant nonempty closed subset contains at least a minimal invariant subset. -/
theorem nonempty_invariant_closed_subset_has_minimalSubset
    (U : Set α) (hne : Nonempty U) (hC : IsClosed U) (hI : IsInvariant (fun n x => f^[n] x) U) :
    ∃ V : Set α, V ⊆ U → (hinv : MapsTo f U U) → IsMinimalSubset f U := by
  -- This follows from Zorn's lemma
  sorry

/-- The recurrent set of `f` is nonempty -/
theorem recurrentSet_nonempty [Nonempty α] : Set.Nonempty (recurrentSet f) := by
  sorry
