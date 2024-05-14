import Mathlib.Tactic
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle

/-!
# Topological dynamics

This file defines Birkhoff sums, other related notions and proves Birkhoff's ergodic theorem.

## Implementation notes

We could do everything in a topological space, using filters and neighborhoods, but it will
be more comfortable with a metric space.

TODO: at some point translate to topological spaces

## References

* ....

-/

open MeasureTheory Filter Metric Function Set
open scoped omegaLimit
set_option autoImplicit false

section Topological_Dynamics

variable {α : Type*} [MetricSpace α]

/-- The non-wandering set of `f` is the set of points which return arbitrarily close after some iterate. -/
def nonWanderingSet (f : α → α) : Set α :=
  {x | ∀ ε, 0 < ε → ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ n ≠ 0}

variable [CompactSpace α] (f : α → α) (hf : Continuous f)

/-- Periodic points belong to the non-wandering set. -/
theorem periodicpts_is_mem (x : α) (n : ℕ) (nnz : n ≠ 0) (pp : IsPeriodicPt f n x) :
    x ∈ nonWanderingSet f := by
  intro ε hε
  use x, n
  refine' ⟨mem_ball_self hε, _, nnz⟩
  . rw [pp]
    exact mem_ball_self hε

lemma periodic_arbitrary_large_time (N : ℕ) (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) (x : α)
    (hx : IsPeriodicPt f m x) :
    ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ N ≤ n := by
  use x, m * N
  refine' ⟨mem_ball_self hε, _, Nat.le_mul_of_pos_left N hm⟩
  · rw [IsPeriodicPt.mul_const hx N]
    exact mem_ball_self hε

lemma inter_subset_empty_of_inter_empty (A : Set α) (B : Set α) (C : Set α) (D : Set α) :
(A ⊆ C) → (B ⊆ D) → (C ∩ D = ∅) → (A ∩ B = ∅) :=
  fun hAC hBD hCD ↦ subset_empty_iff.mp (hCD ▸ inter_subset_inter hAC hBD)

lemma separated_balls (x : α) (h : x ≠ f x) : ∃ ε, 0 < ε ∧ (ball x ε) ∩ (f '' (ball x ε)) = ∅ := by
  have hfC : ContinuousAt f x := Continuous.continuousAt hf
  rw [Metric.continuousAt_iff] at hfC
  have h00 : 0 < ((dist x (f x)) / 4) := div_pos (dist_pos.mpr h) four_pos
  have ⟨a, b, c⟩ := hfC ((dist x (f x)) / 4) h00
  use min a ((dist x (f x)) / 4)
  refine' ⟨lt_min b h00, _⟩
  rw [Set.ext_iff]
  refine' fun y ↦ ⟨fun ⟨hy1, hy2⟩ ↦ _ , fun l ↦ l.elim⟩
  rw [ball, mem_setOf_eq] at hy1
  have hha : min a (dist x (f x) / 4) ≤ a := min_le_left a (dist x (f x) / 4)
  rw [ball, mem_image] at hy2
  rcases hy2 with ⟨z, hz1, hz2⟩
  have hy3 := hz2 ▸ c <| (mem_setOf_eq ▸ hz1).trans_le hha
  have hy4 := dist_comm y x ▸ hy1.trans_le <| min_le_right a (dist x (f x) / 4)
  exfalso
  have gg := dist_triangle x y (f x)
  linarith

/-- The set of points which are not periodic of any period. -/
def IsNotPeriodicPt (f : α → α)  (x : α) := ∀ n : ℕ, 0 < n → ¬IsPeriodicPt f n x

lemma separated_ball_image_ball (n : ℕ) (hn : 0 < n) (x : α) (hfx : IsNotPeriodicPt f x) :
    ∃ (ε : ℝ), 0 < ε ∧ (ball x ε) ∩ (f^[n] '' (ball x ε)) = ∅ :=
  separated_balls (f^[n]) (hf.iterate n) x (Ne.symm <| hfx n hn)

lemma separated_balls_along_non_periodic_orbit (N : ℕ) (x : α) (hfx : IsNotPeriodicPt f x) :
    ∃ δ, (δ > 0) ∧ ∀ (n : ℕ), (0 < n) ∧ (n ≤ N + 1) → (ball x δ) ∩ (f^[n] '' ball x δ) = ∅ := by
  have hkill : ∀ n, 0 < n → ∃ ε, 0 < ε ∧ (ball x ε) ∩ (f^[n] '' (ball x ε)) = ∅ :=
    fun n hnpos ↦ separated_ball_image_ball f hf n hnpos x hfx
  choose! ε2 hε2 h'ε2 using hkill
  have A : Finset.Nonempty ((Finset.Icc 1 (N + 1)).image ε2) := by simp
  let δ := ((Finset.Icc 1 (N + 1)).image ε2).min' A
  have δmem : δ ∈ (Finset.Icc 1 (N + 1)).image ε2 := Finset.min'_mem _ _
  simp only [Finset.mem_image, Finset.mem_Icc] at δmem
  rcases δmem with ⟨n, ⟨npos, _⟩, h'n⟩
  use δ
  refine' ⟨Eq.trans_gt h'n (hε2 n npos), fun n2 hnrange ↦ _⟩
  have hA : δ ≤ ε2 n2 := by
    apply Finset.min'_le
    simp only [Finset.mem_image, Finset.mem_Icc]
    use n2
    exact ⟨hnrange, rfl⟩
  exact inter_subset_empty_of_inter_empty (ball x δ) (f^[n2] '' ball x δ) (ball x (ε2 n2))
    (f^[n2] '' ball x (ε2 n2)) (ball_subset_ball (x := x) hA)
    (image_subset (f^[n2]) (ball_subset_ball (x := x) hA)) (h'ε2 n2 hnrange.left)

theorem ball_non_periodic_arbitrary_large_time (ε : ℝ) (hε : 0 < ε) (x : α)
  (hx : x ∈ nonWanderingSet f)  (hfx : IsNotPeriodicPt f x) :
    ∀ (N : ℕ), ∃ (n : ℕ), N+1 < n ∧ (f^[n] '' ball x ε) ∩ ball x ε ≠ ∅ := by
  -- Suppose, for sake of contradiction, `∃ N, ∀ (n : ℕ), N + 1 < n → f^[n] '' ball x ε ∩ ball x ε = ∅`
  by_contra! h₁
  -- Since x is not periodic, ∃ ε₂ > 0 such that, ∀ (n : ℕ), 0 < n ∧ n ≤ N + 1 → ball x ε₂ ∩ f^[n] '' ball x ε₂ = ∅.
  obtain ⟨N, h₂⟩ := h₁
  choose ε₂ h₃ using separated_balls_along_non_periodic_orbit f hf N x hfx
  obtain ⟨h₈,h₉⟩ := h₃
  -- Choose ε₃ less than ε and ε₂.
  let ε₃ := min ε ε₂
  -- We have therefore shown that, for all n, f^n(B(x,ε₃)) ∩ B(x,ε₃) = ∅
  have h₇ : ∀ (n : ℕ), (0 < n) → f^[n] '' ball x ε₃ ∩ ball x ε₃ = ∅ := by
    intro n hnn
    by_cases hcases : n ≤ N + 1 <;>
      apply inter_subset_empty_of_inter_empty (f^[n] '' ball x ε₃) (ball x ε₃) (f^[n] '' ball x _)
        (ball x _)
    · exact image_subset _ <| ball_subset_ball <| min_le_right ε ε₂
    · exact ball_subset_ball <| min_le_right ε ε₂
    · exact inter_comm _ _ ▸ h₉ n ⟨hnn, hcases⟩
    · exact image_subset _ <| ball_subset_ball <| min_le_left ε ε₂
    · exact ball_subset_ball <| min_le_left ε ε₂
    · exact h₂ n (not_le.mp hcases)
  -- And this contradicts the non wandering assumption.
  rw [nonWanderingSet, mem_setOf_eq] at hx
  choose y n hy hyn hnpos using hx ε₃ (lt_min_iff.mpr ⟨hε, h₈⟩)
  have hw := mem_inter (mem_image_of_mem f^[n] hy) hyn
  rwa [h₇ n (Nat.pos_of_ne_zero hnpos)] at hw

lemma non_periodic_arbitrary_large_time (N : ℕ) (ε0 : ℝ) (hε0 : 0 < ε0) (x : α)
    (hfx : IsNotPeriodicPt f x) (hxf : x ∈ nonWanderingSet f) :
    ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε0 ∧ f^[n] y ∈ ball x ε0 ∧ N + 1 < n := by
  choose n h2 h3 using (ball_non_periodic_arbitrary_large_time f hf ε0 hε0 x hxf hfx N)
  choose z h5 using (inter_nonempty_iff_exists_left.mp (nmem_singleton_empty.mp h3))
  choose y h7 h8 using ((mem_image f^[n] (ball x ε0) z).mp (mem_of_mem_inter_left h5))
  use y, n
  exact ⟨h7, h8 ▸ h5.2, h2⟩

theorem arbitrary_large_time (N : ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) (hx : x ∈ nonWanderingSet f) :
    ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ N + 1 < n := by
  by_cases hfx : IsNotPeriodicPt f x
  -- hard case: if x is non-periodic, we use continuity of f
  · exact non_periodic_arbitrary_large_time f hf N ε hε x hfx hx
  -- easy case: if x is periodic, then y = x is a good candidate
  · unfold IsNotPeriodicPt at hfx
    push_neg at hfx
    rcases hfx with ⟨n, hn, hn2⟩
    -- rcases hfx with ⟨n, hn⟩ also works
    use x, n * (N + 2)
    refine' ⟨mem_ball_self hε, _, _⟩
    · rw [IsPeriodicPt.mul_const hn2 (N + 2)]
      exact mem_ball_self hε
    · have h5 := Nat.le_mul_of_pos_left (N + 1) hn
      linarith

/- Show that the non-wandering set of `f` is closed. -/
theorem is_closed : IsClosed (nonWanderingSet f) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u x hu ulim ε hepos
  rw [tendsto_atTop_nhds] at ulim
  have e2pos : 0 < ε / 2 := by linarith
  obtain ⟨z, h3, h4⟩ : ∃ (z : α), z ∈ ball x (ε / 2) ∧ z ∈ nonWanderingSet f := by
    obtain ⟨N, k3⟩ := ulim (ball x (ε / 2)) (mem_ball_self e2pos) isOpen_ball
    exact ⟨u N, k3 N (Nat.le_refl N), hu N⟩
  simp only [nonWanderingSet, mem_ball, ne_eq, exists_and_left, mem_setOf_eq] at h4
  -- let l1 := h4 (ε / 2) e2pos
  -- rcases l1 with ⟨y, l1, ⟨n, l2, l3⟩⟩
  -- obtain below is equivalent to the above two lines
  obtain ⟨y, l1, ⟨n, l2, l3⟩⟩ := h4 (ε / 2) e2pos
  obtain ⟨h6, h7, h8⟩ : y ∈ ball z (ε / 2) ∧ f^[n] y ∈ ball z (ε / 2) ∧ n ≠ 0 := ⟨l1, l2, l3⟩
  have m1 : dist y z + dist z x < ε := by
    rw [mem_ball] at h3 h6
    linarith
  have h9 : y ∈ ball x ε := lt_of_le_of_lt (dist_triangle _ _ _) m1
  -- Question: Why can I omit argument, but I can't in the line below?
  -- Answer: In this case the argument can easily be inferred from the goal since you want
  -- to prove that `dist y x ≤ dist y z + dist z x` and you are giving it a lemma that says
  -- exactly that, so the only thing left to determine is what are the `x`, `y` and `z` in the
  -- lemma. On the other hand in the line below the arguments are not obvious from the goal,
  -- since you need to prove an inequality using some kind of transitivity, so it is easy to
  -- infer the first and last objects from the goal, but not the middle one.
  -- exact lt_of_le_of_lt this m1
  have p1 : dist (f^[n] y) z + dist z x < ε := by
    rw [mem_ball] at h7 h3
    linarith
  have h10 : f^[n] y ∈ ball x ε := lt_of_le_of_lt (dist_triangle _ _ _) p1
    -- simp -- was doing `mem_ball.mp: y ∈ ball x ε → dist y x < ε `
    -- have : dist (f^[n] y) x ≤ dist (f^[n] y) z + dist z x := dist_triangle _ _ _
  exact ⟨y, n, h9, h10, h8⟩

/-- The non-wandering set of `f` is compact. -/
theorem is_cpt : IsCompact (nonWanderingSet f : Set α) :=
  isCompact_of_isClosed_isBounded (is_closed f) isBounded_of_compactSpace

/-- The omega-limit set of any point is nonempty. -/
theorem omegaLimit_nonempty (x : α) : Set.Nonempty (ω⁺ (fun n ↦ f^[n]) ({x})) :=
  nonempty_omegaLimit atTop (fun n ↦ f^[n]) {x} (Set.singleton_nonempty x)

/-- The omega-limit set of any point is contained in the non-wandering set. -/
theorem omegaLimit_nonwandering (x : α) : (ω⁺ (fun n ↦ f^[n]) ({x})) ⊆ (nonWanderingSet f) := by
  intro z hz
  rw [mem_omegaLimit_iff_frequently] at hz
  simp only [singleton_inter_nonempty, mem_preimage] at hz
  have subsequence : ∀ U ∈ nhds z, ∃ φ, StrictMono φ ∧ ∀ (n : ℕ), f^[φ n] x ∈ U :=
    fun U hU ↦ Filter.extraction_of_frequently_atTop (hz U hU)
  intro ε hε
  obtain ⟨φ, hφ, hf⟩ : ∃ φ, StrictMono φ ∧ ∀ (n : ℕ), f^[φ n] x ∈ ball z ε :=
    subsequence (ball z ε) (ball_mem_nhds z hε)
  use f^[φ 1] x, φ 2 - φ 1
  have : f^[φ 2 - φ 1] (f^[φ 1] x) = f^[φ 2] x := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel]
    exact le_of_lt (hφ (by linarith))
  exact ⟨hf 1, this ▸ (hf 2), Nat.sub_ne_zero_of_lt (hφ Nat.le.refl)⟩

/-- The non-wandering set is non-empty -/
theorem nonWandering_nonempty [hα : Nonempty α] : Set.Nonempty (nonWanderingSet f) :=
  Set.Nonempty.mono (omegaLimit_nonwandering _ _) (omegaLimit_nonempty f (Nonempty.some hα))

/-- The recurrent set is the set of points that are recurrent, i.e. that belong to their omega-limit set. -/
def recurrentSet {α : Type*} [TopologicalSpace α] (f : α → α) : Set α :=
  { x | x ∈ ω⁺ (fun n ↦ f^[n]) {x} }

theorem recurrentSet_iff_accumulation_point (x : α) :
    x ∈ recurrentSet f ↔ ∀ (ε : ℝ) (N : ℕ), 0 < ε → ∃ m : ℕ, N ≤ m ∧ f^[m] x ∈ ball x ε := by
  constructor
  . intro recur_x ε N hε
    rw [recurrentSet, mem_setOf_eq, mem_omegaLimit_iff_frequently] at recur_x
    have recur_x_in_ball := recur_x (ball x ε) (ball_mem_nhds x hε)
    simp only [singleton_inter_nonempty, frequently_atTop] at recur_x_in_ball
    exact recur_x_in_ball N
  . intro hf
    -- simp only [mem_setOf_eq] -- `x ∈ { y | p y } = p x`
    rw [recurrentSet, mem_setOf_eq, mem_omegaLimit_iff_frequently]
    intro U hU
    simp only [singleton_inter_nonempty, mem_preimage, frequently_atTop] -- reduces the goal to `∀ (a : ℕ), ∃ b, a ≤ b ∧ f^[b] x ∈ U`
    -- same as `rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, rest⟩` but nicer
    obtain ⟨ε, hε, ball_in_U⟩ : ∃ ε, ε > 0 ∧ ball x ε ⊆ U := Metric.mem_nhds_iff.mp hU
    intro a
    rcases hf ε a hε with ⟨m, hm, fm_in_ball⟩
    exact ⟨m, hm, mem_of_subset_of_mem ball_in_U fm_in_ball⟩

/-- Periodic points belong to the recurrent set. -/
theorem periodicpts_mem_recurrentSet (x : α) (n : ℕ) (nnz : n ≠ 0) (hx : IsPeriodicPt f n x) :
    x ∈ recurrentSet f := by
  change x ∈ ω⁺ (fun n ↦ f^[n]) {x}
  rw [mem_omegaLimit_iff_frequently]
  simp only [singleton_inter_nonempty, mem_preimage, frequently_atTop]
  intro U hU
  exact fun a ↦ ⟨a * n, ⟨Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero nnz),
    mem_of_mem_nhds <| (Function.IsPeriodicPt.const_mul hx a).symm ▸ hU⟩⟩

/-- The recurrent set is included in the non-wandering set -/
theorem recurrentSet_nonwandering : recurrentSet f ⊆ (nonWanderingSet f) :=
  fun _ ↦ fun hz ↦ omegaLimit_nonwandering _ _ (mem_setOf_eq ▸ hz)

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

/-- The doubling map is the classic interval map -/
noncomputable def doubling_map (x : unitInterval) : unitInterval :=
  ⟨Int.fract (2 * x), by exact unitInterval.fract_mem (2 * x)⟩

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

end Topological_Dynamics
