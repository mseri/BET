/-
Copyright 2023 The Authors
Released under Apache 2.0 license as described in the file LICENSE
Authors: Guillaume Dubach, Marco Lenci, Sébastien Gouëzel, Marcello Seri, Oliver Butterley, Lorenzo Luccioli, Pietro Monticone
-/

import Mathlib.Tactic
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle

/-!
# Topological dynamics

...

## Implementation notes

TO DO:
- Coordinate with the related stuff that already exists in mathlin.
- Upgrade the statements and proofs swapping the metric space requirement for merely requiring a topological space.
- Upgrade all for a general action, not only discrete systems.

## References

* ....

-/

open MeasureTheory Filter Function Set
open scoped omegaLimit
set_option autoImplicit false

section Topological_Dynamics

variable {α : Type*} [TopologicalSpace α]

/-- The non-wandering set of `f` is the set of points which return arbitrarily close after some iterate. -/
def nonWanderingSet (f : α → α) : Set α :=
  {x | ∀ U : Set α, x ∈ U -> IsOpen U -> ∃ N : ℕ, (f^[N] '' U) ∩ U |>.Nonempty }

variable [CompactSpace α] (f : α → α) (hf : Continuous f)

/-- Periodic points belong to the non-wandering set -/
theorem periodicPt_is_nonWandering (x : α) (n : ℕ) (nnz : n ≠ 0) (pp : IsPeriodicPt f n x) :
    x ∈ nonWanderingSet f := by
  intro U hUx _
  use n
  refine ⟨x, ?_⟩
  rw [mem_inter_iff]
  apply And.intro _ hUx
  unfold IsPeriodicPt at pp
  unfold IsFixedPt at pp
  use x

lemma periodicPt_arbitrary_large_time (N : ℕ) (m : ℕ) (hm : 0 < m) (x : α)
    (hx : IsPeriodicPt f m x) :
    ∀ U : Set α, x ∈ U → ∃ (n : ℕ), N ≤ n ∧ f^[n] x ∈ U := by
  intro U hUx
  use m * N
  refine ⟨Nat.le_mul_of_pos_left N hm, ?_⟩
  · rw [IsPeriodicPt.mul_const hx N]
    exact hUx

-- This one should be in mathlib if it is not already there
lemma inter_subset_empty_of_inter_empty (A : Set α) (B : Set α) (C : Set α) (D : Set α) :
(A ⊆ C) → (B ⊆ D) → (C ∩ D = ∅) → (A ∩ B = ∅) :=
  fun hAC hBD hCD ↦ subset_empty_iff.mp (hCD ▸ inter_subset_inter hAC hBD)

/-- The set of points which are not periodic of any period. -/
def IsNotPeriodicPt (f : α → α)  (x : α) := ∀ n : ℕ, 0 < n → ¬IsPeriodicPt f n x

/-- If `x` belongs to the non-wandering set, there are points `y` arbitrarily close to `x`
and arbitrarily large times for which `f^[n] y` comes back close to `x`. -/
theorem arbitrary_large_time (N : ℕ) (x : α) (hx : x ∈ nonWanderingSet f)
  (U : Set α) (hUx : x ∈ U) (hUopen : IsOpen U) :
    ∃ y : α, ∃ n : ℕ, y ∈ U ∧ f^[n] y ∈ U ∧ N + 1 < n := by
  obtain ⟨n, y, hyn, hUy⟩ := hx U hUx hUopen
  use y
  use n
  have fnyU : f^[n] y ∈ U := by
    sorry
  refine ⟨hUy, fnyU, ?_⟩
  sorry

/- Show that the non-wandering set of `f` is closed. -/
theorem nonWanderingSet_isClosed : IsClosed (nonWanderingSet f) := by
  unfold nonWanderingSet
  refine closure_subset_iff_isClosed.mp ?_
  intro x hx
  simp only [image_inter_nonempty_iff, mem_setOf_eq]
  intro U hUx hUopen
  simp at hx
  change ∃ N, (U ∩ f^[N] ⁻¹' U).Nonempty
  -- simp_rw [mem_setOf_eq] at hx
  sorry

/-- The non-wandering set of `f` is compact. -/
theorem nonWanderingSet_isCompact : IsCompact (nonWanderingSet f : Set α) :=
  sorry

/-- The omega-limit set of any point is nonempty. -/
theorem omegaLimit_nonempty (x : α) : Set.Nonempty (ω⁺ (fun n ↦ f^[n]) ({x})) :=
  nonempty_omegaLimit atTop (fun n ↦ f^[n]) {x} (Set.singleton_nonempty x)

/-- The omega-limit set of any point is contained in the non-wandering set. -/
theorem omegaLimit_is_nonWandering (x : α) : (ω⁺ (fun n ↦ f^[n]) ({x})) ⊆ (nonWanderingSet f) := by
  intro z hz
  -- rw [mem_omegaLimit_iff_frequently] at hz
  -- simp only [singleton_inter_nonempty, mem_preimage] at hz
  -- have subsequence : ∀ U ∈ nhds z, ∃ φ, StrictMono φ ∧ ∀ (n : ℕ), f^[φ n] x ∈ U :=
  --   fun U hU ↦ Filter.extraction_of_frequently_atTop (hz U hU)
  -- intro U hUz hUopen
  -- obtain ⟨φ, hφ, hφiterate⟩ := subsequence U _
  -- use φ 1
  -- apply inter_nonempty_iff_exists_right.mpr
  -- use z
  -- wrong...
  -- refine ⟨hUz, hφiterate 1⟩
  sorry

/-- The non-wandering set is non-empty -/
theorem nonWandering_nonempty [hα : Nonempty α] : Set.Nonempty (nonWanderingSet f) :=
  Set.Nonempty.mono (omegaLimit_is_nonWandering _ _) (omegaLimit_nonempty f (Nonempty.some hα))

/-- The recurrent set is the set of points that are recurrent, i.e. that belong to their omega-limit set. -/
def recurrentSet {α : Type*} [TopologicalSpace α] (f : α → α) : Set α :=
  { x | x ∈ ω⁺ (fun n ↦ f^[n]) {x} }

/-- Periodic points belong to the recurrent set. -/
theorem periodicPt_mem_recurrentSet (x : α) (n : ℕ) (nnz : n ≠ 0) (hx : IsPeriodicPt f n x) :
    x ∈ recurrentSet f := by
  change x ∈ ω⁺ (fun n ↦ f^[n]) {x}
  rw [mem_omegaLimit_iff_frequently]
  simp only [singleton_inter_nonempty, mem_preimage, frequently_atTop]
  intro U hU
  exact fun a ↦ ⟨a * n, ⟨Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero nnz),
    mem_of_mem_nhds <| (Function.IsPeriodicPt.const_mul hx a).symm ▸ hU⟩⟩

/-- The recurrent set is included in the non-wandering set -/
theorem recurrentSet_is_nonWandering : recurrentSet f ⊆ (nonWanderingSet f) :=
  fun _ ↦ fun hz ↦ omegaLimit_is_nonWandering _ _ (mem_setOf_eq ▸ hz)

/- Show that the recurrent set of `f` is nonempty (the math proof is not trivial, maybe better skip this one). -/

/-- The doubling map is the classic interval map -/
noncomputable def doubling_map (x : unitInterval) : unitInterval :=
  ⟨Int.fract (2 * x), by exact unitInterval.fract_mem (2 * x)⟩

-- theorem recurrentSet_iff_clusterPt (x : α) :
--     x ∈ recurrentSet f ↔ ClusterPt x (Filter.principal (ω⁺ (fun n ↦ f^[n]) ({x}))) := by
--   constructor
--   -- we prove =>
--   . intro recur_x
--     rw [recurrentSet, mem_setOf_eq] at recur_x
--     apply ClusterPt.of_nhds_le
--     refine le_principal_iff.mpr ?_
--     simp only [mem_omegaLimit_iff_frequently] at recur_x

--   . intro hcluster
--     rw [recurrentSet, mem_setOf_eq, mem_omegaLimit_iff_frequently]
--     unfold ClusterPt at hcluster


--     simp only [singleton_inter_nonempty, mem_preimage, frequently_atTop]
--     intro U hU N
--     apply frequently_atTop

-- theorem recurrentSet_iff_accumulation_point (x : α) :
--     x ∈ recurrentSet f ↔
--     ∀ (W : Set α) (N : ℕ), x ∈ W → ∃ U : Set α, x ∈ U ∧ U ⊆ W ∧ IsOpen U → ∃ m : ℕ, N ≤ m ∧ f^[m] x ∈ U := by
--   constructor
--   -- we prove =>
--   . intro recur_x W N hWx
--     use (interior W)
--     intro ⟨hWx, hWcontained, hWopen⟩
--     have hUnhds : (interior W) ∈ nhds x := IsOpen.mem_nhds hWopen hWx
--     rw [recurrentSet, mem_setOf_eq, mem_omegaLimit_iff_frequently] at recur_x
--     have recur_x_in_U := recur_x (interior W) hUnhds
--     simp only [singleton_inter_nonempty, frequently_atTop] at recur_x_in_U
--     exact recur_x_in_U N
--   -- we prove <=
--   . intro hf
--     rw [recurrentSet, mem_setOf_eq, mem_omegaLimit_iff_frequently]
--     intro U hUnhds
--     simp only [singleton_inter_nonempty, mem_preimage, frequently_atTop]
--     -- the goal is now `∀ (a : ℕ), ∃ b, a ≤ b ∧ f^[b] x ∈ U`
--     intro N
--     have hintUnhds : (interior U) ∈ nhds x := by
--       refine IsOpen.mem_nhds ?_ ?_
--       sorry
--     refine nonempty_def.mp ?mpr.a
--     have : ∃ U_1, x ∈ U_1 ∧ U_1 ⊆ interior U ∧ IsOpen U_1 → ∃ m, N ≤ m ∧ f^[m] x ∈ U_1 := by apply hf (interior U) N (mem_of_mem_nhds hintUnhds)
--     obtain ⟨U_1, hU1x, hU1contained, hU1open⟩ := this

--     refine ⟨mem_of_mem_nhds hUnhs, ?_⟩
--     apply isOpen_iff_mem_nhds.mpr
--     intro z hUz
--     apply mem_nhds_iff.mpr
--     sorry

end Topological_Dynamics
