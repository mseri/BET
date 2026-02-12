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

section Orbit

variable {α : Type*}

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

/-- The orbit equals the range of iterates. -/
lemma orbit_eq_range (f : α → α) (x : α) :
    orbit f x = Set.range (fun n : ℕ ↦ f^[n] x) := by
  ext y; simp [orbit, Set.mem_range, eq_comm]

/-- If `U` is invariant, then the orbit of any point in `U` is contained in `U`. -/
theorem orbit_subset_of_invariant (f: α → α) (U : Set α)
    (hinv : IsInvariant (fun n x ↦ f^[n] x) U) (x : α) (hx : x ∈ U) :
    orbit f x ⊆ U := by
  intro y hy
  obtain ⟨n, hn⟩ := hy
  exact hn ▸ hinv n hx

end Orbit

variable {α : Type*}[TopologicalSpace α]
-- latter properties are required by Flow
variable {τ : Type*} [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ]

/- A subset is minimal if it is nonempty, closed, invariant, and every orbit is dense in U. -/
structure IsMinimalSubset (ϕ : Flow τ α) (U : Set α) : Prop where
  (isNonempty : U.Nonempty)
  (isClosed : IsClosed U)
  (isInvariant : IsInvariant ϕ.toFun U)
  (isMinimal : ∀ x ∈ U, U ⊆ closure (Set.range (fun τ ↦ ϕ τ x)))

lemma fun_of_flow_fromIter (f : α → α) (hf : Continuous f) :
  (Flow.fromIter hf).toFun = fun n x ↦ f^[n] x := rfl

/-- A dynamical system (α,f) is minimal if α is a minimal subset. -/
def IsMinimal (f : α → α) (hf: Continuous f) : Prop :=
  IsMinimalSubset (Flow.fromIter hf) univ

theorem recurrentSet_of_minimal_is_all_space [CompactSpace α] [Nonempty α]
    (f : α → α) (hf : Continuous f) (hM : IsMinimal f hf) (x : α) :
    x ∈ recurrentSet f := by
  rw [recurrentSet, Set.mem_setOf_eq, mem_omegaLimit_iff_frequently]
  simp only [Set.singleton_inter_nonempty, Set.mem_preimage, Filter.frequently_atTop]
  intro U hU N
  -- By minimality, every orbit is dense in α
  have hDense : Dense (Set.range (fun n ↦ f^[n] (f^[N] x))) := by
    have h1 := hM.isMinimal (f^[N] x) (Set.mem_univ _)
    rw [fun_of_flow_fromIter] at h1
    exact fun y => h1 (Set.mem_univ y)
  -- So it intersects every neighborhood of x
  obtain ⟨z, hzR, hzU⟩ := hDense.inter_nhds_nonempty hU
  obtain ⟨m, hm⟩ := hzR
  have hm' : f^[m] (f^[N] x) = z := hm
  exact ⟨m + N, Nat.le_add_left N m, by rw [Function.iterate_add_apply, hm']; exact hzU⟩

/-- An example of a continuous dynamics on a compact space in which the recurrent set is all
the space, but the dynamics is not minimal -/
example : ¬IsMinimal (id : unitInterval → unitInterval) continuous_id := by
  intro H
  have minimality := H.isMinimal 0 (Set.mem_univ _) (Set.mem_univ (1 : unitInterval))
  rw [fun_of_flow_fromIter] at minimality
  simp_rw [iterate_id] at minimality
  simp [Set.range_const] at minimality

example (x : unitInterval) : x ∈ recurrentSet (id : unitInterval → unitInterval) :=
  periodicPt_mem_recurrentSet _ _ 1 (by norm_num) (is_periodic_id 1 x)

/-- Every point in a minimal subset is recurrent. -/
theorem minimalSubset_mem_recurrentSet [CompactSpace α] (f : α → α) (hf : Continuous f)
  (U : Set α) (hU : IsMinimalSubset (Flow.fromIter hf) U) :
    U ⊆ recurrentSet f := by
  intro x hxU
  rw [recurrentSet, Set.mem_setOf_eq, mem_omegaLimit_iff_frequently]
  simp only [Set.singleton_inter_nonempty, Set.mem_preimage, Filter.frequently_atTop]
  intro V hV N
  have hfNx : f^[N] x ∈ U := by
    have hinv := hU.isInvariant N
    rw [fun_of_flow_fromIter] at hinv
    exact hinv hxU
  -- By minimality, orbit of f^[N] x is dense in U, and x ∈ U
  have hxcl : x ∈ closure (Set.range (fun n ↦ f^[n] (f^[N] x))) := by
    have h1 := hU.isMinimal (f^[N] x) hfNx
    rw [fun_of_flow_fromIter] at h1
    exact h1 hxU
  rw [mem_closure_iff_nhds] at hxcl
  obtain ⟨z, hzV, hzR⟩ := Set.inter_nonempty.mp (hxcl V hV)
  obtain ⟨m, hm⟩ := hzR
  have hm' : f^[m] (f^[N] x) = z := hm
  exact ⟨m + N, Nat.le_add_left N m, by rw [Function.iterate_add_apply, hm']; exact hzV⟩

/-- Is a closed, invariant and nonempty set. -/
structure IsCIN (f : α → α) (U : Set α) : Prop where
  (nonempty : U.Nonempty)
  (closed : IsClosed U)
  (invariant : IsInvariant (fun n x ↦ f^[n] x) U)

/-- A set is minimal if it is closed, invariant and nonempty and no proper subset satisfies these same properties. -/
structure IsMinimalAlt (f : α → α) (U : Set α) : Prop where
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
  have h3 : ∀ (V' : Set α), V' ⊆ V ∧ IsCIN f V' → V' = V := by
    intro V' h4
    have hV'S : V' ∈ S := ⟨h4.1.trans h1, h4.2⟩
    exact Subset.antisymm h4.1 (h2.2 hV'S h4.1)
  exact ⟨h1, h2.1.2, h3⟩

/-- The closure of an orbit is invariant under the dynamics. -/
theorem closure_orbit_inv (f: α → α) (hf : Continuous f) (x : α) :
  IsInvariant (fun n x ↦ f^[n] x) (closure (orbit f x)) := by
  let s := orbit f x
  intro n y h0
  have h1 : ContinuousOn f^[n] (closure s) := Continuous.continuousOn (Continuous.iterate hf n)
  have h2 : f^[n] y ∈ f^[n] '' closure s := Exists.intro y { left := h0, right := rfl }
  exact closure_mono (mapsTo_iff_image_subset.mp ((orbit_inv f x) n)) (ContinuousOn.image_closure h1 h2)

-- open Metric in
-- def everyOrbitDense [MetricSpace α] (f: α → α) (U : Set α) := ∀ (x y : α) (_: x ∈ U) (_: y ∈ U) (ε : ℝ),
--     ε > 0 → ∃ n : ℕ, f^[n] y ∈ ball x ε

open Metric in
/-- Every orbit starting in `U` is dense in `U`. -/
def everyOrbitDense (f: α → α) (U : Set α) := ∀ x ∈ U, U ⊆ closure (orbit f x)

/-- If `U` is closed, nonempty, invariant, and every orbit in `U` is dense in `U`,
    then `U` is a minimal-alt set. -/
theorem minimalAlt_if_minimal (f: α → α) (U : Set α) (hd : everyOrbitDense f U) (hcl : IsClosed U)
    (hn : U.Nonempty) (hinv : IsInvariant (fun n x ↦ f^[n] x) U) : IsMinimalAlt f U := by
  -- `U` is a minimal subset and so `U` is nonempty and closed by definition.
  refine { cin.closed := hcl, cin.invariant := hinv, cin.nonempty := hn, minimal := ?_ }
  -- Suppose that `V` is a nonempty closed invariant subset of `U` and show that `V = U`.
  intro V h8
  -- Since `V` is nonempty, there exists `x ∈ V`.
  let x := h8.right.nonempty.some
  have h3 : x ∈ V := Nonempty.some_mem h8.right.nonempty
  have hxU : x ∈ U := h8.1 h3
  -- The orbit of `x` is dense in `U` and `V` is a closed invariant subset containing `x`.
  -- So `U ⊆ closure(orbit f x) ⊆ V`.
  have h5 : U ⊆ V := by
    -- The first inclusion follows by density
    have hUcl : U ⊆ closure (orbit f x) := hd x hxU
    -- The second by invariance of V
    have horbV : orbit f x ⊆ V := orbit_subset_of_invariant f V h8.right.invariant x h3
    -- and then closedness
    have hclV : closure (orbit f x) ⊆ V := closure_minimal horbV h8.right.closed
    exact fun y hy => hclV (hUcl hy)
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

/-- The two definitions of minimality are equivalent. -/
theorem minimal_equiv (f: α → α) (hf: Continuous f)
    (U : Set α) : (IsMinimalAlt f U) ↔ (IsMinimalSubset (Flow.fromIter hf) U) := by
  constructor
  · -- (⇒) IsMinimalAlt → IsMinimalSubset
    intro halt
    refine ⟨halt.cin.nonempty, halt.cin.closed, ?_, ?_⟩
    · -- Invariance
      rw [fun_of_flow_fromIter]
      exact halt.cin.invariant
    · -- Every orbit in U is dense in U
      intro x hxU
      rw [fun_of_flow_fromIter, ← orbit_eq_range]
      -- closure(orbit f x) is a closed, invariant, nonempty (CIN as defined above) subset of U
      have horbU : orbit f x ⊆ U :=
        orbit_subset_of_invariant f U halt.cin.invariant x hxU
      have hclU : closure (orbit f x) ⊆ U := closure_minimal horbU halt.cin.closed
      have hCIN : IsCIN f (closure (orbit f x)) :=
        { nonempty := ⟨x, subset_closure ⟨0, rfl⟩⟩
          closed := isClosed_closure
          invariant := closure_orbit_inv f hf x }
      have heq := halt.minimal (closure (orbit f x)) ⟨hclU, hCIN⟩
      -- heq gives closure (orbit f x) = U, but we needed to show
      -- the weaker U ⊆ closure (orbit f x) which is now immediate
      exact le_of_eq heq.symm
  · -- (⇐) IsMinimalSubset → IsMinimalAlt
    intro hsub
    refine ⟨⟨hsub.isNonempty, hsub.isClosed, ?_⟩, ?_⟩
    · -- Invariance
      have h := hsub.isInvariant
      rwa [fun_of_flow_fromIter] at h
    · -- Minimality: show any CIN V ⊆ U equals U
      intro V ⟨hVU, hVCIN⟩
      obtain ⟨x, hxV⟩ := hVCIN.nonempty
      have hxU : x ∈ U := hVU hxV
      have horbV : orbit f x ⊆ V := orbit_subset_of_invariant f V hVCIN.invariant x hxV
      have hclV : closure (orbit f x) ⊆ V := closure_minimal horbV hVCIN.closed
      have hUcl : U ⊆ closure (orbit f x) := by
        have h := hsub.isMinimal x hxU
        rwa [fun_of_flow_fromIter, ← orbit_eq_range] at h
      exact Subset.antisymm hVU (hUcl.trans hclV)

/-- Every invariant nonempty closed subset contains at least a minimal invariant subset. -/
theorem nonempty_invariant_closed_subset_has_minimalSubset [CompactSpace α]
    (f: α → α) (hf: Continuous f)
    (U : Set α) (hne : U.Nonempty) (hC : IsClosed U) (hI : IsInvariant (fun n x => f^[n] x) U) :
    ∃ V : Set α, V ⊆ U ∧ IsMinimalSubset (Flow.fromIter hf) V := by
  have hCIN : IsCIN f U := { nonempty := hne, closed := hC, invariant := hI }
  obtain ⟨V, hVU, hVmin⟩ := exists_minimal_set f U hCIN
  exact ⟨V, hVU, (minimal_equiv f hf V).mp hVmin⟩

/-- The recurrent set of `f` is nonempty -/
theorem recurrentSet_nonempty [Nonempty α] [CompactSpace α] (f : α → α) (hf: Continuous f) :
  Set.Nonempty (recurrentSet f) := by
  -- There exists a minimal set, this is a nonempty set.
  have h1 : IsCIN f univ :=
    { nonempty := univ_nonempty, closed := isClosed_univ, invariant := fun _ _ a ↦ a }
  obtain ⟨V, _, h4⟩ := exists_minimal_set f univ h1
  have h5 := h4.cin.nonempty
  -- The minimal set is contained within the recurrent set.
  have h4' := (minimal_equiv f hf V).mp h4
  have h6 : V ⊆ recurrentSet f := minimalSubset_mem_recurrentSet f hf V h4'
  exact Nonempty.mono h6 h5
