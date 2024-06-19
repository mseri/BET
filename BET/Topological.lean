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

/-- Periodic points belong to the non-wandering set. -/
theorem periodicpts_is_mem (x : α) (n : ℕ) (nnz : n ≠ 0) (pp : IsPeriodicPt f n x) :
    x ∈ nonWanderingSet f := by
  intro U hUx _
  use n
  refine ⟨x, ?_⟩
  rw [mem_inter_iff]
  apply And.intro _ hUx
  unfold IsPeriodicPt at pp
  unfold IsFixedPt at pp
  use x

lemma periodic_arbitrary_large_time (N : ℕ) (m : ℕ) (hm : 0 < m) (x : α)
    (hx : IsPeriodicPt f m x) :
    ∀ U : Set α, x ∈ U → ∃ (n : ℕ), N ≤ n ∧ f^[n] x ∈ U := by
  intro U hUx
  use m * N
  refine ⟨Nat.le_mul_of_pos_left N hm, ?_⟩
  · rw [IsPeriodicPt.mul_const hx N]
    exact hUx

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
  have p1 : dist (f^[n] y) z + dist z x < ε := by
    rw [mem_ball] at h7 h3
    linarith
  have h10 : f^[n] y ∈ ball x ε := lt_of_le_of_lt (dist_triangle _ _ _) p1
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

/-- The doubling map is the classic interval map -/
noncomputable def doubling_map (x : unitInterval) : unitInterval :=
  ⟨Int.fract (2 * x), by exact unitInterval.fract_mem (2 * x)⟩

end Topological_Dynamics
