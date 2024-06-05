/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Damien Thomine
-/
import Mathlib.Topology.Instances.EReal
import BET.TopologicalEntropy.Miscellaneous.ERealDiv

/-!
# Continuity of the multiplication on EReal
Outside of indeterminacies `0 × ±∞` and `±∞ × 0`, the multiplication on extended reals `EReal`
is continuous. There are many different cases to consider, so we first prove some special cases
and leverage as much as possible the symmetries of the multiplication.
-/

namespace ERealMulCont

lemma continuousAt_mul_swap {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (b, a) := by
  have : (fun p : EReal × EReal ↦ p.1 * p.2) = (fun p : EReal × EReal ↦ p.1 * p.2)
      ∘ Prod.swap := by
    ext p
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
    exact mul_comm p.1 p.2
  rw [this]; clear this
  apply ContinuousAt.comp _ (Continuous.continuousAt continuous_swap)
  simp [h]

lemma continuousAt_mul_symm1 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (-a, b) := by
  have : (fun p : EReal × EReal ↦ p.1 * p.2) = (fun x : EReal ↦ -x)
      ∘ (fun p : EReal × EReal ↦ p.1 * p.2) ∘ (fun p : EReal × EReal ↦ (-p.1, p.2)) := by
    ext p
    simp only [Function.comp_apply, neg_mul, neg_neg]
  rw [this]; clear this
  apply ContinuousAt.comp (Continuous.continuousAt continuous_neg)
    <| ContinuousAt.comp _ (ContinuousAt.prod_map (Continuous.continuousAt continuous_neg)
      (Continuous.continuousAt continuous_id))
  simp only [neg_neg, id_eq, h]

lemma continuousAt_mul_symm2 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, -b) :=
  continuousAt_mul_swap (continuousAt_mul_symm1 (continuousAt_mul_swap h))

lemma continuousAt_mul_symm3 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (-a, -b) :=
  continuousAt_mul_symm1 (continuousAt_mul_symm2 h)

lemma continuousAt_mul_coe_coe (a b : ℝ) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b) := by
  simp only [ContinuousAt, EReal.nhds_coe_coe, ← EReal.coe_mul, Filter.tendsto_map'_iff,
    (· ∘ ·), EReal.tendsto_coe, tendsto_mul]

lemma continuousAt_mul_top_top :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, ⊤) := by
  simp only [ContinuousAt, EReal.top_mul_top, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [eventually_nhds_iff]
  use (Set.Ioi ((max x 0) : EReal)) ×ˢ (Set.Ioi 1)
  split_ands
  . intros p p_in_prod
    simp only [Set.mem_prod, Set.mem_Ioi, max_lt_iff] at p_in_prod
    rcases p_in_prod with ⟨⟨p1_gt_x, p1_pos⟩, p2_gt_1⟩
    have := mul_le_mul_of_nonneg_left (le_of_lt p2_gt_1) (le_of_lt p1_pos)
    rw [mul_one p.1] at this
    exact lt_of_lt_of_le p1_gt_x this
  . exact IsOpen.prod isOpen_Ioi isOpen_Ioi
  . simp only [Set.mem_Ioi, max_lt_iff, EReal.coe_lt_top, EReal.zero_lt_top, and_self]
  . rw [Set.mem_Ioi, ← EReal.coe_one]
    exact EReal.coe_lt_top 1

lemma continuousAt_mul_top_pos {a : ℝ} (h : 0 < a) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, a) := by
  simp only [ContinuousAt, EReal.top_mul_coe_of_pos h, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [eventually_nhds_iff]
  use (Set.Ioi ((2*(max (x+1) 0)/a : ℝ) : EReal)) ×ˢ (Set.Ioi ((a/2 : ℝ) : EReal))
  split_ands
  . intros p p_in_prod
    simp only [Set.mem_prod, Set.mem_Ioi] at p_in_prod
    rcases p_in_prod with ⟨p1_gt, p2_gt⟩
    have p1_pos : 0 < p.1 := by
      apply lt_of_le_of_lt _ p1_gt
      rw [EReal.coe_nonneg]
      apply mul_nonneg _ (le_of_lt (inv_pos_of_pos h))
      simp only [gt_iff_lt, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, le_max_iff, le_refl, or_true]
    have a2_pos : 0 < ((a/2 : ℝ) : EReal) := by
      rw [EReal.coe_pos]
      linarith
    have lock := mul_le_mul_of_nonneg_right (le_of_lt p1_gt) (le_of_lt a2_pos)
    have key := mul_le_mul_of_nonneg_left (le_of_lt p2_gt) (le_of_lt p1_pos)
    replace lock := le_trans lock key; clear key
    apply lt_of_lt_of_le _ lock; clear lock
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, div_mul_div_comm, mul_comm,
      ← div_mul_div_comm, mul_div_right_comm]
    simp only [ne_eq, Ne.symm (ne_of_lt h), not_false_eq_true, div_self, OfNat.ofNat_ne_zero,
      one_mul, lt_max_iff, lt_add_iff_pos_right, zero_lt_one, true_or]
  . exact IsOpen.prod isOpen_Ioi isOpen_Ioi
  . simp only [Set.mem_Ioi, EReal.coe_lt_top]
  . simp only [Set.mem_Ioi, EReal.coe_lt_coe_iff, half_lt_self_iff, h]

lemma continuousAt_mul_top_ne_zero {a : ℝ} (h : a ≠ 0) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, a) := by
  rcases (lt_or_gt_of_ne h) with a_neg | a_pos
  . rw [← neg_neg (a : EReal)]
    exact continuousAt_mul_symm2 (continuousAt_mul_top_pos (neg_pos.2 a_neg))
  . exact continuousAt_mul_top_pos a_pos

/-- The multiplication on `EReal` is continuous except at indeterminacies
  (i.e. whenever one value is zero and the other infinite). -/
theorem continuousAt_mul {p : EReal × EReal} (h₁ : p.1 ≠ 0 ∨ p.2 ≠ ⊥)
    (h₂ : p.1 ≠ 0 ∨ p.2 ≠ ⊤) (h₃ : p.1 ≠ ⊥ ∨ p.2 ≠ 0) (h₄ : p.1 ≠ ⊤ ∨ p.2 ≠ 0) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) p := by
  rcases p with ⟨x, y⟩
  induction x using EReal.rec <;> induction y using EReal.rec
  . rw [← EReal.neg_top]
    exact continuousAt_mul_symm3 continuousAt_mul_top_top
  . simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₃; clear h₁ h₂ h₄
    rw [← EReal.neg_top]
    exact continuousAt_mul_symm1 (continuousAt_mul_top_ne_zero h₃)
  . rw [← EReal.neg_top]
    exact continuousAt_mul_symm1 continuousAt_mul_top_top
  . simp only [ne_eq, EReal.coe_eq_zero, not_true_eq_false, or_false] at h₁; clear h₂ h₃ h₄
    rw [← EReal.neg_top]
    exact continuousAt_mul_symm2 (continuousAt_mul_swap (continuousAt_mul_top_ne_zero h₁))
  . exact continuousAt_mul_coe_coe _ _
  . simp only [ne_eq, EReal.coe_eq_zero, not_true_eq_false, or_false] at h₂; clear h₁ h₃ h₄
    exact continuousAt_mul_swap (continuousAt_mul_top_ne_zero h₂)
  . rw [← EReal.neg_top]
    exact continuousAt_mul_symm2 continuousAt_mul_top_top
  . simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₄; clear h₁ h₂ h₃
    exact continuousAt_mul_top_ne_zero h₄
  . exact continuousAt_mul_top_top

end ERealMulCont

#lint
