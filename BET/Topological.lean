/-
Copyright 2023 The Authors
Released under Apache 2.0 license as described in the file LICENSE
Authors: Guillaume Dubach, Marco Lenci, Sébastien Gouëzel, Marcello Seri, Oliver Butterley, Lorenzo Luccioli, Pietro Monticone
-/

import Mathlib.Tactic
import Mathlib.Topology.Separation.Basic
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle

/-!
# Topological dynamics

...

## Implementation notes

TO DO:
- Coordinate with the related stuff that already exists in mathlib.

## References

* ....

-/

open MeasureTheory Filter Function Set
open scoped omegaLimit
set_option autoImplicit false

/-! ## Purely combinatorial lemmas (no topology required) -/

section PureLemmas

variable {α : Type*} (f : α → α)

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

end PureLemmas

/-! ## Topological dynamics -/

section Topological_Dynamics

variable {α : Type*} [TopologicalSpace α]

/-- The non-wandering set of `f` is the set of points which return arbitrarily close after some iterate. -/
def nonWanderingSet (f : α → α) : Set α :=
  {x | ∀ U : Set α, x ∈ U -> IsOpen U -> ∃ N : ℕ, (f^[N] '' U) ∩ U |>.Nonempty }

/-! ### Lemmas requiring only TopologicalSpace -/

section TopologicalOnly

variable (f : α → α)

/-- Periodic points belong to the non-wandering set -/
theorem periodicPt_is_nonWandering (x : α) (n : ℕ) (_nnz : n ≠ 0) (pp : IsPeriodicPt f n x) :
    x ∈ nonWanderingSet f := by
  intro U hUx _
  use n
  refine ⟨x, ?_⟩
  rw [mem_inter_iff]
  apply And.intro _ hUx
  unfold IsPeriodicPt at pp
  unfold IsFixedPt at pp
  use x

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

-- theorem mem_recurrentSet_is_accumulation_point (x : α) :
--      x ∈ recurrentSet f →
--      ∀ (U : Set α) (N : ℕ), x ∈ U ∧ IsOpen U → ∃ m : ℕ, N ≤ m ∧ f^[m] x ∈ U := by
--   intro recur_x U N ⟨hUx, hUopen⟩
--   rw [recurrentSet, mem_setOf_eq, mem_omegaLimit_iff_frequently] at recur_x
--   have hUnhds : U ∈ nhds x := IsOpen.mem_nhds hUopen hUx
--   have recur_x_in_U := recur_x U hUnhds
--   simp only [singleton_inter_nonempty, frequently_atTop] at recur_x_in_U
--   exact recur_x_in_U N

def orbit_atTop (f : α → α) (x : α) : Filter α := Filter.map (fun n ↦ f^[n] x) atTop

lemma orbit_atTop_eq_mapClusterPt (f : α → α) (x : α) :
  MapClusterPt x atTop (fun n ↦ f^[n] x) = ClusterPt x (orbit_atTop f x) := by
  rw [orbit_atTop, MapClusterPt]

theorem recurrentSet_iff_clusterPt (x : α) :
    x ∈ recurrentSet f ↔ ClusterPt x (orbit_atTop f x) := by
  constructor
  -- we prove =>
  . intro recur_x
    rw [recurrentSet, mem_setOf_eq] at recur_x
    rw [mem_omegaLimit_singleton_iff_map_cluster_point atTop (fun n ↦ f^[n]) x x] at recur_x
    rw [orbit_atTop_eq_mapClusterPt] at recur_x
    exact recur_x
  -- we prove <=
  . intro hcluster
    rw [recurrentSet]
    rw [mem_setOf_eq]
    rw [←orbit_atTop_eq_mapClusterPt] at hcluster
    rw [mem_omegaLimit_singleton_iff_map_cluster_point atTop (fun n ↦ f^[n]) x x]
    exact hcluster

/- Show that the non-wandering set of `f` is closed. -/
theorem nonWanderingSet_isClosed : IsClosed (nonWanderingSet f) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  simp only [Set.mem_compl_iff, nonWanderingSet, Set.mem_setOf_eq] at hx
  push_neg at hx
  obtain ⟨U, hUx, hUopen, hU⟩ := hx
  refine ⟨U, ?_, hUopen, hUx⟩
  intro y hyU
  simp only [Set.mem_compl_iff, nonWanderingSet, Set.mem_setOf_eq]
  intro hy
  obtain ⟨N, hN⟩ := hy U hyU hUopen
  exact absurd (hU N) hN.ne_empty

/-- The omega-limit set of any point is contained in the non-wandering set. -/
theorem omegaLimit_is_nonWandering (x : α) : (ω⁺ (fun n ↦ f^[n]) ({x})) ⊆ (nonWanderingSet f) := by
  intro y hy U hUy hUopen
  rw [mem_omegaLimit_iff_frequently] at hy
  simp only [Set.singleton_inter_nonempty, Set.mem_preimage, Filter.frequently_atTop] at hy
  have hUnhds : U ∈ nhds y := hUopen.mem_nhds hUy
  obtain ⟨n₁, _, hn₁⟩ := hy U hUnhds 0
  obtain ⟨n₂, hn₂, hn₂U⟩ := hy U hUnhds (n₁ + 1)
  refine ⟨n₂ - n₁, f^[n₂] x, ?_, hn₂U⟩
  exact ⟨f^[n₁] x, hn₁, by rw [← Function.iterate_add_apply]; congr 1; omega⟩

/-- The recurrent set is included in the non-wandering set -/
theorem recurrentSet_is_nonWandering : recurrentSet f ⊆ (nonWanderingSet f) :=
  fun _ ↦ fun hz ↦ omegaLimit_is_nonWandering _ _ (mem_setOf_eq ▸ hz)

end TopologicalOnly

/-! ### Lemmas requiring CompactSpace -/

variable [CompactSpace α] (f : α → α) (hf : Continuous f)

/-- The set of points which are not periodic of any period. -/
def IsNotPeriodicPt (f : α → α)  (x : α) := ∀ n : ℕ, 0 < n → ¬IsPeriodicPt f n x

/-- If `x` belongs to the non-wandering set, there are points `y` arbitrarily close to `x`
and arbitrarily large times for which `f^[n] y` comes back close to `x`. -/
theorem closed_arbitrary_large_time (N : ℕ) (x : α) (hx : x ∈ nonWanderingSet f)
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
  sorry

/-- The non-wandering set of `f` is compact. -/
theorem nonWanderingSet_isCompact : IsCompact (nonWanderingSet f : Set α) :=
  (nonWanderingSet_isClosed f).isCompact

/-- The omega-limit set of any point is nonempty. -/
theorem omegaLimit_nonempty (x : α) : Set.Nonempty (ω⁺ (fun n ↦ f^[n]) ({x})) :=
  nonempty_omegaLimit atTop (fun n ↦ f^[n]) {x} (Set.singleton_nonempty x)

/-- The non-wandering set is non-empty -/
theorem nonWandering_nonempty [hα : Nonempty α] : Set.Nonempty (nonWanderingSet f) :=
  Set.Nonempty.mono (omegaLimit_is_nonWandering _ _) (omegaLimit_nonempty f (Nonempty.some hα))

/- Show that the recurrent set of `f` is nonempty (the math proof is not trivial, maybe better skip this one). -/

/-- The doubling map is the classic interval map -/
noncomputable def doubling_map (x : unitInterval) : unitInterval :=
  ⟨Int.fract (2 * x), by exact unitInterval.fract_mem (2 * x)⟩

end Topological_Dynamics
