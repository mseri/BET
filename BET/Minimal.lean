/-
Copyright 2023 The Authors
Released under Apache 2.0 license as described in the file LICENSE
Authors: Guillaume Dubach, Marco Lenci, Sébastien Gouëzel, Marcello Seri, Oliver Butterley, Lorenzo Luccioli, Pietro Monticone
-/

import Mathlib.Dynamics.Minimal
import Mathlib.Dynamics.Flow
import BET.Topological

/-!
# Minimal sets

This file contains various details related to minimal sets and minimal actions.

Much of the minimal stuff probably in `Mathlib/Dynamics/Minimal.lean` but missing the definition of
a minimal set and the existence proof.

TO DO:
- Align contents here with `Mathlib/Dynamics/Minimal.lean`.
- Upgrade the statements and proofs swapping the metric space requirement for merely requiring a
  topological space.
- Only use compactSpace when really required.
- Upgrade all for a general action as per the stuff already in mathlib.
- Improve the naming of theorems and definitions.
- Match up the two different versions of `IsMinimal`.
- Extend the description of the file contents (definitions / theorems).

-/

open MeasureTheory Filter Function Set
open scoped omegaLimit
set_option autoImplicit false

variable {α : Type*}[TopologicalSpace α]
-- latter properties are required by Flow
variable {τ : Type*} [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ]

/- A subset is minimal if it is nonempty, closed, and every orbit is dense.
To do: remove invariant, add nonempty. -/
structure IsMinimalSubset (ϕ : Flow τ α) (U : Set α) : Prop :=
  (isClosed : IsClosed U)
  (isInvariant : IsInvariant ϕ.toFun U)
  (isMinimal :  ∀ x : α, DenseRange (fun τ ↦ ϕ τ x))

  -- ∀ V W, IsOpen V → (U ∩ V).Nonempty → IsOpen W → (U ∩ W).Nonempty → ∃ n : τ,
  --   ((ϕ n)⁻¹' (V ∩ U)) ∩ (W ∩ U) |>.Nonempty)

lemma fun_of_flow_fromIter (f : α → α) (hf : Continuous f) :
  (Flow.fromIter hf).toFun = fun n x ↦ f^[n] x := rfl

/-- A dynamical system (α,f) is minimal if α is a minimal subset. -/
def IsMinimal (f : α → α) (hf: Continuous f) : Prop :=
  IsMinimalSubset (Flow.fromIter hf) univ

theorem recurrentSet_of_minimal_is_all_space [CompactSpace α]
    (f : α → α) (hf : Continuous f) (hM : IsMinimal f hf) (x : α) :
    x ∈ recurrentSet f := by
    apply (recurrentSet_iff_clusterPt f x).mpr
      -- explicitly, we are now proving
      -- ∀ (ε : ℝ) (N : ℕ), ε > 0 → ∃ m : ℕ, m ≥ N ∧ f^[m] x ∈ ball x ε
      -- apply (recurrentSet_iff_accumulation_point f x).mpr
      -- intro ε N hε
      -- obtain ⟨n, hball⟩ : ∃ n, f^[n] (f^[N] x) ∈ ball x ε :=
      --   hf.minimal x (f^[N] x) (mem_univ _) (mem_univ _) ε hε
      -- exact ⟨n + N, by linarith, (Function.iterate_add_apply _ _ _ _).symm ▸ hball⟩
    sorry

/-- An example of a continuous dynamics on a compact space in which the recurrent set is all
the space, but the dynamics is not minimal -/
example : ¬IsMinimal (id : unitInterval → unitInterval) continuous_id := by
  intro H
  have minimality := H.isMinimal 0 1
  rw [fun_of_flow_fromIter] at minimality
  simp_rw [iterate_id] at minimality
  have : closure (range (fun τ : ℕ ↦ id 0)) = {0} := by
    rw [range_const, closure_singleton]
    rfl
  revert minimality; contrapose!; intro _
  rw [range_const, closure_singleton]
  simp

example (x : unitInterval) : x ∈ recurrentSet (id : unitInterval → unitInterval) :=
  periodicPt_mem_recurrentSet _ _ 1 (by norm_num) (is_periodic_id 1 x)

/-- Every point in a minimal subset is recurrent. -/
theorem minimalSubset_mem_recurrentSet (f : α → α) (hf : Continuous f)
  (U : Set α) (hU : IsMinimalSubset (Flow.fromIter hf) U) :
    U ⊆ recurrentSet f := by
  intro x hx
  rcases hU with ⟨_, hInv, hMin⟩
  apply (recurrentSet_iff_clusterPt f x).mpr
  sorry
  -- rw [clusterPt_iff]
  -- intro ε N hε
  -- obtain ⟨n, hball⟩ : ∃ n, f^[n] (f^[N] x) ∈ ball x ε :=
  --   hMin x (f^[N] x) hx (Set.mapsTo'.mp (hInv N) ⟨x, hx, rfl⟩) ε hε
  -- exact ⟨n + N, le_add_self, (Function.iterate_add_apply _ _ _ _).symm ▸ hball⟩

/-- Is a closed, invariant and nonempty set. -/
structure IsCIN (f : α → α) (U : Set α) : Prop :=
  (nonempty : U.Nonempty)
  (closed : IsClosed U)
  (invariant : IsInvariant (fun n x ↦ f^[n] x) U)

/-- A set is minimal if it is closed, invariant and nonempty and no proper subset satisfies these same properties. -/
structure IsMinimalAlt (f : α → α) (U : Set α) : Prop :=
  (cin : IsCIN f U)
  (minimal : ∀ (V : Set α), V ⊆ U ∧ IsCIN f V → V = U)

/- The intersection of nested nonempty closed invariant sets is nonempty, closed and invariant. -/
theorem inter_nested_closed_inv_is_closed_inv_nonempty [CompactSpace α] (f : α → α) (C : Set (Set α))
    (hc1 : C.Nonempty) (hc2 :  IsChain (· ⊆ ·) C) (hn : ∀ V ∈ C, IsCIN f V) :
    IsCIN f (⋂₀ C) := by
  have hScl := (fun V x ↦ (hn V x).closed)
  have hne := (fun V x ↦ (hn V x).nonempty)
  have htd : DirectedOn (· ⊇ ·) C := IsChain.directedOn hc2.symm
  have hSc : ∀ U ∈ C, IsCompact U := fun U a ↦ IsClosed.isCompact (hScl U a)
  have : Nonempty C := nonempty_coe_sort.mpr hc1
  -- the use of fun in the constructor in the following refine
  -- allows one to introduce directly all the relevant terms
  -- for the proof
  refine' ⟨_, isClosed_sInter hScl, fun n x hx U h2c ↦ _⟩
  -- Nonempty intersection follows from Cantor's intersection theorem
  · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed htd hne hSc hScl
  -- Invariance from basic argument
  · exact (hn U h2c).invariant n (hx U h2c)

/-- Every invariant nonempty closed subset contains at least a minimal invariant subset. -/
theorem exists_minimal_set [CompactSpace α]  (f : α → α) (U : Set α) (h : IsCIN f U) :
    ∃ V : Set α, V ⊆ U ∧ (IsMinimalAlt f V) := by
  /- Consider `S` the set of invariant nonempty closed subsets. -/
  let S : Set (Set α) := {V | V ⊆ U ∧ IsCIN f V}
  /- Every totally ordered subset of `S` has a lower bound. -/
  have h0 : ∀ C ⊆ S, IsChain (· ⊆ ·) C → Set.Nonempty C → ∃ lb ∈ S, ∀ U' ∈ C, lb ⊆ U' := by
    intro C h1 h2 h3
    /- The intersection is the candidate for the lower bound. -/
    let lb := ⋂₀ C
    use lb
    /- We show that `lb` has is closed, invariant and nonempty. -/
    have h4 : ∀ V ∈ C, IsCIN f V := fun V h5 ↦ (h1 h5).right
    have h5 := inter_nested_closed_inv_is_closed_inv_nonempty f C h3 h2 h4
    /- We show that `lb` is in `S`. -/
    choose V' h8 using h3 -- Let's fix some `V ∈ C`.
    -- same as have h14 : V' ∈ S := by exact h1 h8
    have h14 : V' ∈ S := h1 h8
    have h6 : lb ⊆ U := Subset.trans (sInter_subset_of_mem h8) (h14.left)
    /- We show that `lb` is a lowerbound. -/
    have h12 : ∀ U' ∈ C, lb ⊆ U' := fun U' hu => sInter_subset_of_mem hu
    exact ⟨mem_sep h6 h5, h12⟩
  /- Apply Zorn's lemma. -/
  obtain ⟨V, h1, h2⟩ := zorn_superset_nonempty S h0 U ⟨Eq.subset rfl,h⟩
  use V
  /- Rephrase the conclusion. -/
  have h3 : ∀ (V' : Set α), V' ⊆ V ∧ IsCIN f V' → V' = V :=
    fun V' h4 ↦ h2.right V' ⟨(subset_trans h4.left h1.left), h4.right⟩ h4.left
  exact ⟨h1.left, h1.right, h3⟩

/-- The orbit of a point `x` is set of all iterates under `f`. -/
def orbit (f: α → α) x := { y | ∃ n : ℕ, y = f^[n] x }

/-- The orbit of a point is invariant. -/
theorem orbit_inv (f: α → α) (x : α) : IsInvariant (fun n x ↦ f^[n] x) (orbit f x) := by
  intro n y h0
  choose m h1 using h0
  -- here we show that f^[n] y = f^[n + m] x
  use n + m
  rw [h1]
  exact (iterate_add_apply f n m x).symm

/-- The closure of an orbit is invariant under the dynamics. -/
theorem closure_orbit_inv (f: α → α) (hf : Continuous f) (x : α) :
  IsInvariant (fun n x ↦ f^[n] x) (closure (orbit f x)) := by
  let s := orbit f x
  intro n y h0
  have h1 : ContinuousOn f^[n] (closure s) := Continuous.continuousOn (Continuous.iterate hf n)
  have h2 : f^[n] y ∈ f^[n] '' closure s := Exists.intro y { left := h0, right := rfl }
  exact closure_mono (mapsTo'.mp ((orbit_inv f x) n)) (ContinuousOn.image_closure h1 h2)

-- open Metric in
-- def everyOrbitDense [MetricSpace α] (f: α → α) (U : Set α) := ∀ (x y : α) (_: x ∈ U) (_: y ∈ U) (ε : ℝ),
--     ε > 0 → ∃ n : ℕ, f^[n] y ∈ ball x ε

open Metric in
def everyOrbitDense (f: α → α) (U : Set α) := ∀ x ∈ U, Dense (orbit f x)

/-- If the orbit of any point in a set `U` is dense then `U` is invariant. -/
theorem invariant_if_everyOrbitDense (f: α → α) (U : Set α) (hd : everyOrbitDense f U) (hcl : IsClosed U) :
    IsInvariant (fun n x ↦ f^[n] x) U := by
  sorry

theorem minimalAlt_if_minimal (f: α → α)  (U : Set α) (hd : everyOrbitDense f U) (hcl : IsClosed U)
    (hn : U.Nonempty) : IsMinimalAlt f U := by
  -- `U` is a minimal subset and so `U` is nonempty and closed by definition.
  refine { cin.closed := hcl, cin.invariant := ?_, cin.nonempty := hn, minimal := ?_ }
  -- Invariance follows from prior result.
  · exact invariant_if_everyOrbitDense f U hd hcl
  -- Suppose that `V` is a nonempty closed invariant subset of `U` and show that `V = U`.
  intro V h8
  -- Since `V` is nonempty, there exists `x ∈ V`.
  let x := h8.right.nonempty.some
  have h3 : x ∈ V := Nonempty.some_mem h8.right.nonempty
  -- The orbit of each point in `U` is dense in `U` and `V` is a closed invariant subset.
  -- Consequently `U = closure orbit x ⊆ V`.
  have h4 : U = closure (orbit f x) := by
    unfold everyOrbitDense at hd
    refine Set.eq_of_subset_of_subset (fun y h18 ↦ ?_) (fun y h19 ↦ ?_)
    · sorry
    · sorry
  have h5 : U ⊆ V := by
    rw [h4]
    refine' closure_minimal (fun y h13 ↦ _) h8.right.closed
    choose n h14 using h13
    exact h14 ▸ h8.right.invariant n h3
  -- Thus, `U = V`.
  exact (Set.eq_of_subset_of_subset h5 h8.left).symm

/-
# MinimalAlt → Minimal

Let `U` be a nonempty closed invariant subset of X such that `U` has no proper nonempty closed invariant subsets.
If `x ∈ U`, then the invariance of `U` guarantees that the orbit of `x` is contained within `U`.
`closure_orbit_inv` implies that the closure of the orbit is invariant.
Thus, this set is a nonempty closed invariant subset of `U`.
Since `U` has no proper nonempty closed invariant subsets, `U` is equal to the closure of the orbit.
Hence, the oribit of any point is dense in `U`.
-/

/-- The two definitions are equivalent. -/
theorem minimal_equiv (f: α → α) (hf: Continuous f)
    (U : Set α) : (IsMinimalAlt f U) ↔ (IsMinimalSubset (Flow.fromIter hf) U) := sorry

/-- Every invariant nonempty closed subset contains at least a minimal invariant subset. -/
theorem nonempty_invariant_closed_subset_has_minimalSubset
    (f: α → α) (hf: Continuous f)
    (U : Set α) (hne : Nonempty U) (hC : IsClosed U) (hI : IsInvariant (fun n x => f^[n] x) U) :
    ∃ V : Set α, V ⊆ U → (hinv : MapsTo f U U) → IsMinimalSubset (Flow.fromIter hf) U := by
  -- This follows from `exists_minimal_set` and `minimal_equiv`
  sorry

/-- The recurrent set of `f` is nonempty -/
theorem recurrentSet_nonempty [Nonempty α] [CompactSpace α] (f : α → α) (hf: Continuous f) :
  Set.Nonempty (recurrentSet f) := by
  -- There exists a minimal set, this is a nonempty set.
  have h1 : IsCIN f univ :=
    { nonempty := univ_nonempty, closed := isClosed_univ, invariant := fun _ _ a ↦ a }
  choose V _ h4 using (exists_minimal_set f univ h1)
  have h5 := h4.cin.nonempty
  -- The minimal set is contained within the recurrent set.
  rw [minimal_equiv] at h4
  have h6 : V ⊆ recurrentSet f := minimalSubset_mem_recurrentSet f hf V h4
  exact Nonempty.mono h6 h5
