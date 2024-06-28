/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Damien Thomine, Pietro Monticone
-/
import BET.TopologicalEntropy.Miscellaneous.Misc
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Division of extended reals
We define a division of an extended real `EReal`.

This file may be completed as wished, it is still quite incomplete.

MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14224
-/

/- Instance of LinearOrderedSemifield?-/

namespace EReal

open EReal ENNReal Misc SignType

/-! ### Inverse of an extended real-/

noncomputable instance : DivInvMonoid EReal where
  inv := fun (a : EReal) ↦ match a with
  | none => 0
  | some b => match b with
    | none => 0
    | some c => (c⁻¹ : ℝ)

@[simp]
theorem inv_bot : (⊥ : EReal)⁻¹ = 0 := rfl

@[simp]
theorem inv_top : (⊤ : EReal)⁻¹ = 0 := rfl

theorem coe_inv (x : ℝ) : (x⁻¹ : ℝ) = (x : EReal)⁻¹ := rfl

@[simp]
theorem inv_zero : (0 : EReal)⁻¹ = 0 := by
  change (0 : ℝ)⁻¹ = (0 : EReal)
  rw [GroupWithZero.inv_zero, coe_zero]

noncomputable instance : DivInvOneMonoid EReal where
  inv_one := by nth_rw 1 [← coe_one, ← coe_inv 1, _root_.inv_one, coe_one]

theorem inv_neg (a : EReal) : (-a)⁻¹ = -a⁻¹ := by
  induction a using EReal.rec
  · rw [neg_bot, inv_top, inv_bot, neg_zero]
  · rw [← coe_inv _, ← coe_neg _⁻¹, ← coe_neg _, ← coe_inv (-_)]
    exact EReal.coe_eq_coe_iff.2 _root_.inv_neg
  · rw [neg_top, inv_bot, inv_top, neg_zero]

theorem inv_inv {a : EReal} (h : a ≠ ⊥) (h' : a ≠ ⊤) : (a⁻¹)⁻¹ = a := by
  rw [← coe_toReal h' h, ← coe_inv a.toReal, ← coe_inv a.toReal⁻¹, _root_.inv_inv a.toReal]

theorem mul_inv (a b : EReal) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  induction a, b using EReal.induction₂_symm with
  | top_top | top_zero | top_bot | zero_bot | bot_bot => simp
  | @symm a b h => rw [mul_comm b a, mul_comm b⁻¹ a⁻¹]; exact h
  | top_pos x x_pos => rw [top_mul_of_pos (EReal.coe_pos.2 x_pos), inv_top, zero_mul]
  | top_neg x x_neg => rw [top_mul_of_neg (EReal.coe_neg'.2 x_neg), inv_bot, inv_top, zero_mul]
  | pos_bot x x_pos => rw [mul_bot_of_pos (EReal.coe_pos.2 x_pos), inv_bot, mul_zero]
  | coe_coe x y => rw [← coe_mul, ← coe_inv, _root_.mul_inv, coe_mul, coe_inv, coe_inv]
  | neg_bot x x_neg => rw [mul_bot_of_neg (EReal.coe_neg'.2 x_neg), inv_top, inv_bot, mul_zero]

/-! ## Inversion and absolute value -/

theorem sign_mul_inv_abs (a : EReal) : (sign a) * (a.abs : EReal)⁻¹ = a⁻¹ := by
  induction' a using EReal.rec with a
  · simp
  · rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, ← inv_neg, abs_def a,
        coe_ennreal_ofReal, max_eq_left (abs_nonneg a), ← coe_neg |a|, abs_of_neg a_neg, neg_neg]
    · rw [coe_zero, sign_zero, SignType.coe_zero, abs_zero, coe_ennreal_zero, inv_zero, mul_zero]
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul]
      simp only [abs_def a, coe_ennreal_ofReal, ge_iff_le, abs_nonneg, max_eq_left]
      congr
      exact abs_of_pos a_pos
  · simp

theorem sign_mul_inv_abs' (a : EReal) : (sign a) * ((a.abs⁻¹ : ℝ≥0∞) : EReal) = a⁻¹ := by
  induction' a using EReal.rec with a
  · simp
  · rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_neg a_neg), coe_ennreal_ofReal,
        max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_neg |a|⁻¹, ← coe_inv a, abs_of_neg a_neg,
        ← _root_.inv_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_pos a_pos), coe_ennreal_ofReal,
          max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_inv a]
      congr
      exact abs_of_pos a_pos
  · simp

/-! ## Inversion and positivity -/

theorem inv_nonneg_of_nonneg {a : EReal} (h : 0 ≤ a) : 0 ≤ a⁻¹ := by
  induction' a using EReal.rec with a
  · simp
  · rw [← coe_inv a, EReal.coe_nonneg, inv_nonneg]
    exact EReal.coe_nonneg.1 h
  · simp

theorem inv_nonpos_of_nonpos {a : EReal} (h : a ≤ 0) : a⁻¹ ≤ 0 := by
  induction' a using EReal.rec with a
  · simp
  · rw [← coe_inv a, EReal.coe_nonpos, inv_nonpos]
    exact EReal.coe_nonpos.1 h
  · simp

theorem inv_pos_of_ntop_pos {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : 0 < a⁻¹ := by
  induction' a using EReal.rec with a
  · exact (not_lt_bot h).rec
  · rw [← coe_inv a]
    norm_cast at *
    exact inv_pos_of_pos h
  · exact (h' (Eq.refl ⊤)).rec

theorem inv_neg_of_nbot_neg {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : a⁻¹ < 0 := by
  induction' a using EReal.rec with a
  · exact (h' (Eq.refl ⊥)).rec
  · rw [← coe_inv a]
    norm_cast at *
    exact inv_lt_zero.2 h
  · exact (not_top_lt h).rec

/-! ### Division -/

theorem div_eq_inv_mul (a b : EReal) : a / b = b⁻¹ * a := EReal.mul_comm a b⁻¹

theorem coe_div (a b : ℝ) : (a / b : ℝ) = (a : EReal) / (b : EReal) := rfl

@[simp]
theorem div_bot {a : EReal} : a / ⊥ = 0 := inv_bot ▸ mul_zero a

@[simp]
theorem div_top {a : EReal} : a / ⊤ = 0 := inv_top ▸ mul_zero a

@[simp]
theorem div_zero {a : EReal} : a / 0 = 0 := by
  change a * 0⁻¹ = 0
  rw [inv_zero, mul_zero a]

@[simp]
theorem zero_div {a : EReal} : 0 / a = 0 := zero_mul a⁻¹

theorem top_div_nontop_pos {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : ⊤ / a = ⊤ :=
  top_mul_of_pos (inv_pos_of_ntop_pos h h')

theorem top_div_nonbot_neg {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : ⊤ / a = ⊥ :=
  top_mul_of_neg (inv_neg_of_nbot_neg h h')

theorem bot_div_nontop_pos {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : ⊥ / a = ⊥ :=
  bot_mul_of_pos (inv_pos_of_ntop_pos h h')

theorem bot_div_nonbot_neg {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : ⊥ / a = ⊤ :=
  bot_mul_of_neg (inv_neg_of_nbot_neg h h')

/-! ## Division and multiplication -/

theorem div_self {a : EReal} (h₁ : a ≠ ⊥) (h₂ : a ≠ ⊤) (h₃ : a ≠ 0) : a / a = 1 := by
  rw [← coe_toReal h₂ h₁] at h₃ ⊢
  rw [← coe_div, _root_.div_self (coe_ne_zero.1 h₃), coe_one]

theorem mul_div (a b c : EReal) : a * (b / c) = (a * b) / c := by
  change a * (b * c⁻¹) = (a * b) * c⁻¹
  rw [mul_assoc]

theorem mul_div_right (a b c : EReal) : (a / b) * c = (a * c) / b := by
  rw [mul_comm, EReal.mul_div, mul_comm]

theorem div_div (a b c : EReal) : a / b / c = a / (b * c) := by
  change (a * b⁻¹) * c⁻¹ = a * (b * c)⁻¹
  rw [mul_assoc a b⁻¹, mul_inv]

theorem div_mul_cancel {a b : EReal} (h₁ : b ≠ ⊥) (h₂ : b ≠ ⊤) (h₃ : b ≠ 0) : (a / b) * b = a := by
  change (a * b⁻¹) * b = a
  rw [mul_assoc, mul_comm b⁻¹ b]
  change a * (b / b) = a
  rw [div_self h₁ h₂ h₃, mul_one]

theorem mul_div_cancel {a b : EReal} (h₁ : b ≠ ⊥) (h₂ : b ≠ ⊤) (h₃ : b ≠ 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel h₁ h₂ h₃]

theorem mul_div_mul_cancel {a b c : EReal} (h₁ : c ≠ ⊥) (h₂ : c ≠ ⊤) (h₃ : c ≠ 0) :
    (a * c) / (b * c) = a / b := by
  change (a * c) * (b * c)⁻¹ = a * b⁻¹
  rw [mul_assoc, mul_inv b c]
  congr
  exact mul_div_cancel h₁ h₂ h₃

/-! ## Distributivity -/

theorem div_right_distrib_of_nneg {a b c : EReal} (h : 0 ≤ a) (h' : 0 ≤ b) :
    (a + b) / c = (a / c) + (b / c) :=
  EReal.right_distrib_of_nneg h h'

/-! ## Division and order s-/

theorem monotone_div_right_of_nonneg {b : EReal} (h : 0 ≤ b) : Monotone fun a ↦ a / b :=
  fun _ _ h' ↦ mul_le_mul_of_nonneg_right h' (inv_nonneg_of_nonneg h)

theorem monotone_div_right_of_nonneg_apply {a a' b : EReal} (h : 0 ≤ b) (h' : a ≤ a') :
    a / b ≤ a' / b :=
  monotone_div_right_of_nonneg h h'

theorem strictMono_div_right_of_pos {b : EReal} (h : 0 < b) (h' : b ≠ ⊤) :
    StrictMono fun a ↦ a / b := by
  intro a a' a_lt_a'
  apply lt_of_le_of_ne <| monotone_div_right_of_nonneg_apply (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b (ne_bot_of_gt h) h' (ne_of_gt h), hyp,
    @EReal.mul_div_cancel a' b (ne_bot_of_gt h) h' (ne_of_gt h)]

theorem strictMono_div_right_of_pos_apply {a a' b : EReal} (h₁ : 0 < b) (h₂ : b ≠ ⊤)
    (h₃ : a < a') : a / b < a' / b :=
  strictMono_div_right_of_pos h₁ h₂ h₃

theorem antitone_div_right_of_nonpos {b : EReal} (h : b ≤ 0) : Antitone fun a ↦ a / b := by
  intro a a' h'
  change a' * b⁻¹ ≤ a * b⁻¹
  rw [← neg_neg (a * b⁻¹), ← neg_neg (a' * b⁻¹), neg_le_neg_iff, mul_comm a b⁻¹, mul_comm a' b⁻¹,
    ← neg_mul b⁻¹ a, ← neg_mul b⁻¹ a', mul_comm (-b⁻¹) a, mul_comm (-b⁻¹) a', ← inv_neg b]
  have : 0 ≤ -b := by apply le_neg_of_le_neg; simp [h]
  exact monotone_div_right_of_nonneg_apply this h'

theorem antitone_div_right_of_nonpos_apply {a a' b : EReal} (h : b ≤ 0) (h' : a ≤ a') :
    a' / b ≤ a / b :=
  antitone_div_right_of_nonpos h h'

theorem strictAnti_div_right_of_neg {b : EReal} (h : b < 0) (h' : b ≠ ⊥) :
    StrictAnti fun a ↦ a / b := by
  intro a a' a_lt_a'
  simp only
  apply lt_of_le_of_ne <| antitone_div_right_of_nonpos_apply (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b h' (ne_top_of_lt h) (ne_of_lt h), ← hyp,
    @EReal.mul_div_cancel a' b h' (ne_top_of_lt h) (ne_of_lt h)]

theorem strictAnti_div_right_of_neg_apply {a a' b : EReal} (h₁ : b < 0) (h₂ : b ≠ ⊥)
    (h₃ : a < a') : a' / b < a / b :=
  strictAnti_div_right_of_neg h₁ h₂ h₃

theorem le_div_iff_mul_le {a b c : EReal} (h : b > 0) (h' : b ≠ ⊤) :
    a ≤ c / b ↔ a * b ≤ c := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [mul_div b a b, mul_comm a b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

theorem div_le_iff_le_mul {a b c : EReal} (h : b > 0) (h' : b ≠ ⊤) :
    a / b ≤ c ↔ a ≤ b * c := by
  nth_rw 1 [← @mul_div_cancel c b (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [mul_div b c b, mul_comm b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

theorem div_nonneg {a b : EReal} (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a / b :=
  mul_nonneg h (inv_nonneg_of_nonneg h')

theorem div_nonpos_of_nonpos_of_nonneg {a b : EReal} (h : a ≤ 0) (h' : 0 ≤ b) : a / b ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg h (inv_nonneg_of_nonneg h')

theorem div_nonpos_of_nonneg_of_nonpos {a b : EReal} (h : 0 ≤ a) (h' : b ≤ 0) : a / b ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos h (inv_nonpos_of_nonpos h')

theorem div_nonneg_of_nonpos_of_nonpos {a b : EReal} (h : a ≤ 0) (h' : b ≤ 0) : 0 ≤ a / b :=
  le_of_eq_of_le (Eq.symm zero_div) (antitone_div_right_of_nonpos_apply h' h)

end EReal

#lint
#minimize_imports
