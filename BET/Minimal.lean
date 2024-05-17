/-
Copyright 2023 The Authors
Released under Apache 2.0 license as described in the file LICENSE
Authors: Guillaume Dubach, Marco Lenci, Sébastien Gouëzel, Marcello Seri, Oliver Butterley, Lorenzo Luccioli, Pietro Monticone
-/

import «BET».Topological

/-!
# Minimal sets

This file contains various details related to minimal sets and minimal actions.

Much of the minimal stuff probably in `Mathlib/Dynamics/Minimal.lean` but missing the definition of a minimal set and the existence proof.

TO DO:
- Align contents here with `Mathlib/Dynamics/Minimal.lean`.
- Upgrade the statements and proofs swapping the metric space requirement for merely requiring a topological space.
- Only use compactSpace when really required.
- Upgrade all for a general action as per the stuff already in mathlib.
- Improve the naming of theorems and definitions.
- Match up the two different versions of `IsMinimal`.
- Extend the description of the file contents (definitions / theorems).

-/

open MeasureTheory Filter Metric Function Set
open scoped omegaLimit
set_option autoImplicit false

variable {α : Type*} [MetricSpace α]
variable [CompactSpace α] (f : α → α) (hf : Continuous f)

/- A subset is minimal if it is nonempty, closed, and every orbit is dense.
To do: remove invariant, add nonempty. -/
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
theorem inter_nested_closed_inv_is_closed_inv_nonempty
    (f : α → α) (C : Set (Set α))
    (hc1 : C.Nonempty) (hc2 :  IsChain (· ⊆ ·) C) (hn : ∀ V ∈ C, IsCIN f V) :
    IsCIN f (⋂₀ C) := by
  have hScl := (fun V x ↦ (hn V x).closed)
  have hne := (fun V x ↦ (hn V x).nonempty)
  -- Nonempty intersection follows from Cantor's intersection theorem
  have h0 : (⋂₀ C).Nonempty := by
    -- Flip the chain to fit with the result in mathlib
    replace hc2 : IsChain (· ⊇ ·) C := hc2.symm
    have htd : DirectedOn (· ⊇ ·) C := IsChain.directedOn hc2
    have hSc : ∀ U ∈ C, IsCompact U := fun U a ↦ IsClosed.isCompact (hScl U a)
    have : Nonempty C := nonempty_coe_sort.mpr hc1
    exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed htd hne hSc hScl
  -- Closed by assumption
  have h1 : IsClosed (⋂₀ C) := isClosed_sInter hScl
  -- Invariance from basic argument
  have h2 : IsInvariant (fun n x ↦ f^[n] x) (⋂₀ C) := by
    intros n x hx
    have h2b : ∀ U ∈ C, (fun n x ↦ f^[n] x) n x ∈ U := by
      intros U h2c
      exact (hn U h2c).invariant n (hx U h2c)
    exact h2b
  exact ⟨h0, h1, h2⟩

/-- Every invariant nonempty closed subset contains at least a minimal invariant subset. -/
theorem exists_minimal_set
    (U : Set α) (h : IsCIN f U) :
    ∃ V : Set α, V ⊆ U ∧ (IsMinimalAlt f V) := by
  /- Consider `S` the set of invariant nonempty closed subsets. -/
  let S : Set (Set α) := {V | V ⊆ U ∧ IsCIN f V}
  /- Every totally ordered subset of `S` has a lower bound. -/
  have h0 : ∀ C ⊆ S, IsChain (· ⊆ ·) C → Set.Nonempty C → ∃ lb ∈ S, ∀ U' ∈ C, lb ⊆ U' := by
    intros C h1 h2 h3
    /- The intersection is the candidate for the lower bound. -/
    let lb := ⋂₀ C
    use lb
    /- We show that `lb` has is closed, invariant and nonempty. -/
    have h4 : ∀ V ∈ C, IsCIN f V := by
      intro V h5
      exact (h1 h5).right
    have h5 := inter_nested_closed_inv_is_closed_inv_nonempty f C h3 h2 h4
    /- We show that `lb` is in `S`. -/
    choose V' h8 using h3 -- Let's fix some `V ∈ C`.
    have h14 : V' ∈ S := by exact h1 h8
    have h6 : lb ⊆ U := by exact Subset.trans (sInter_subset_of_mem h8) (h14.left)
    /- We show that `lb` is a lowerbound. -/
    have h12 : ∀ U' ∈ C, lb ⊆ U' := fun U' hu => sInter_subset_of_mem hu
    exact ⟨mem_sep h6 h5, h12⟩
  /- Apply Zorn's lemma. -/
  obtain ⟨V, h1, h2⟩ := zorn_superset_nonempty S h0 U ⟨Eq.subset rfl,h⟩
  use V
  /- Rephrase the conclusion. -/
  have h3 : ∀ (V' : Set α), V' ⊆ V ∧ IsCIN f V' → V' = V := by
    intros V' h4
    exact h2.right V' ⟨(subset_trans h4.left h1.left), h4.right⟩ h4.left
  exact ⟨h1.left, h1.right, h3⟩

/-- The orbit of a point `x` is set of all iterates under `f`. -/
def orbit x := { y | ∃ n : ℕ, y = f^[n] x }

/-- The orbit of a point is invariant. -/
theorem orbit_inv (x : α) : IsInvariant (fun n x ↦ f^[n] x) (orbit f x) := by
  intros n y h0
  choose m h1 using h0
  have h5 : f^[n] y = f^[n + m] x := by
    rw [h1]
    exact (iterate_add_apply f n m x).symm
  use n + m

/-- The closure of an orbit is invariant under the dynamics. -/
theorem closure_orbit_inv (x : α) : IsInvariant (fun n x ↦ f^[n] x) (closure (orbit f x)) := by
  let s := orbit f x
  intros n y h0
  have h1 : ContinuousOn f^[n] (closure s) := Continuous.continuousOn (Continuous.iterate hf n)
  have h2 : f^[n] y ∈ f^[n] '' closure s := Exists.intro y { left := h0, right := rfl }
  have h3 := closure_mono (mapsTo'.mp ((orbit_inv f x) n))
  exact h3 (ContinuousOn.image_closure h1 h2)

def everyOrbitDense (U : Set α) := ∀ (x y : α) (_: x ∈ U) (_: y ∈ U) (ε : ℝ),
    ε > 0 → ∃ n : ℕ, f^[n] y ∈ ball x ε

/-- If the orbit of any point in a set `U` is dense then `U` is invariant. -/
theorem invariant_if_everyOrbitDense
    (U : Set α) (hd : everyOrbitDense f U) (hcl : IsClosed U) :
    IsInvariant (fun n x ↦ f^[n] x) U := by

  sorry

theorem minimalAlt_if_minimal
    (U : Set α) (hd : everyOrbitDense f U) (hcl : IsClosed U)
    (hn : U.Nonempty) : IsMinimalAlt f U := by
  -- `U` is a minimal subset and so `U` is nonempty and closed by definition.
  refine { cin.closed := hcl, cin.invariant := ?_, cin.nonempty := hn, minimal := ?_ }
  -- Invariance follows from prior result.
  exact invariant_if_everyOrbitDense f U hd hcl
  -- Suppose that `V` is a nonempty closed invariant subset of `U` and show that `V = U`.
  intro V h8
  -- Since `V` is nonempty, there exists `x ∈ V`.
  let x := h8.right.nonempty.some
  have h3 : x ∈ V := Nonempty.some_mem h8.right.nonempty
  -- The orbit of each point in `U` is dense in `U` and `V` is a closed invariant subset.
  -- Consequently `U = closure orbit x ⊆ V`.
  have h4 : U = closure (orbit f x) := by
    have h15 := hd
    unfold everyOrbitDense at h15
    have h16 : U ⊆ closure (orbit f x) := by
      intros y h18

      sorry
    have h17 : closure (orbit f x) ⊆ U := by
      intros y h19

      sorry
    exact Set.eq_of_subset_of_subset h16 h17
  have h5 : closure (orbit f x) ⊆ V := by
    have h9 := h8.right.closed
    have h12 := h8.right.invariant
    have h10 : (orbit f x) ⊆ V := by
      intros y h13
      choose n h14 using h13
      have h11 : f^[n] x ∈ V := h12 n h3
      rw [← h14] at h11
      exact h11
    exact closure_minimal h10 h9
  rw [← h4] at h5
  -- Thus, `U = V`.
  have h6 := Set.eq_of_subset_of_subset h5 h8.left
  exact h6.symm

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
theorem minimal_equiv
    (U : Set α) : (IsMinimalAlt f U) ↔ (IsMinimalSubset f U) := sorry

/-- Every invariant nonempty closed subset contains at least a minimal invariant subset. -/
theorem nonempty_invariant_closed_subset_has_minimalSubset
    (U : Set α) (hne : Nonempty U) (hC : IsClosed U) (hI : IsInvariant (fun n x => f^[n] x) U) :
    ∃ V : Set α, V ⊆ U → (hinv : MapsTo f U U) → IsMinimalSubset f U := by
  -- This follows from `exists_minimal_set` and `minimal_equiv`
  sorry

/-- The recurrent set of `f` is nonempty -/
theorem recurrentSet_nonempty [Nonempty α]: Set.Nonempty (recurrentSet f) := by
  -- There exists a minimal set, this is a nonempty set.
  have h0 := exists_minimal_set f univ
  have h1 : IsCIN f univ := by
    refine { nonempty := ?nonempty, closed := ?closed, invariant := fun _ ⦃x⦄ a ↦ a }
    exact univ_nonempty
    exact isClosed_univ
  have h2 := h0 h1
  choose V _ h4 using h2
  have h5 := h4.cin.nonempty
  -- The minimal set is contained within the recurrent set.
  rw [minimal_equiv] at h4
  have h6 : V ⊆ recurrentSet f := minimalSubset_mem_recurrentSet f V h4
  exact Nonempty.mono h6 h5
