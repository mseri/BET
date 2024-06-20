/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Damien Thomine
-/
import Mathlib.Tactic
import Mathlib.Data.Real.EReal
import BET.TopologicalEntropy.Miscellaneous.Misc

/-!
# Division of extended reals by extended nonnegative reals
We define a division of an extended real `EReal` by an extended nonnegative real `ENNReal`
as the multiplication by the coercion of its inverse. It is an instance of division.

This file may be completed as wished, it is still quite incomplete.
-/

namespace ERealDiv

open Misc

/--
Division of an extended real (EReal) by an extended nonnegative real (ENNReal). Defined by inversion in
[0, ∞], coercion to [-∞,+∞], and multiplication in [-∞,+∞].--/
noncomputable def EReal.divENNReal : EReal → ENNReal → EReal :=
  fun (a : EReal) (b : ENNReal) ↦ a * b⁻¹

noncomputable instance EReal.ENNReal.instHDiv : HDiv EReal ENNReal EReal where
  hDiv := EReal.divENNReal

theorem EReal.div_eq_inv_mul {a : EReal} {b : ENNReal} : a / b = b⁻¹ * a := EReal.mul_comm _ _

theorem EReal.mul_div {a b : EReal} {c : ENNReal} : a * (b / c) = (a * b) / c := by
  change a * (b * c⁻¹) = (a * b) * c⁻¹
  rw [mul_assoc]

theorem EReal.mul_div_right {a c : EReal} {b : ENNReal} : (a / b) * c = (a * c) / b := by
  rw [mul_comm, EReal.mul_div, mul_comm]

theorem EReal.mul_inv_cancel {a : EReal} {b : ENNReal} (h : b ≠ 0) (h' : b ≠ ⊤) :
    (a / b) * b = a := by
  change (a * b⁻¹) * b = a
  simp [mul_assoc, ← EReal.coe_ennreal_mul, mul_comm b⁻¹ b, ENNReal.mul_inv_cancel h h']

@[simp]
theorem EReal.div_one {a : EReal} : a / (1 : ENNReal) = a := by
  change a * (1 : ENNReal)⁻¹ = a
  simp [inv_one, EReal.coe_ennreal_one, mul_one a]

@[simp]
theorem EReal.div_top {a : EReal} : a / (⊤ : ENNReal) = 0 := by
  change a * (⊤ : ENNReal)⁻¹ = 0
  simp

theorem EReal.pos_div_zero {a : EReal} (h : 0 < a) : a / (0 : ENNReal) = ⊤ := by
  change a * (0 : ENNReal)⁻¹ = ⊤
  rw [ENNReal.inv_zero, EReal.coe_ennreal_top, EReal.mul_top_of_pos h]

theorem EReal.neg_div_zero {a : EReal} (h : a < 0) : a / (0 : ENNReal) = ⊥ := by
  change a * (0 : ENNReal)⁻¹ = ⊥
  rw [ENNReal.inv_zero, EReal.coe_ennreal_top, EReal.mul_top_of_neg h]

@[simp]
theorem EReal.zero_div {b : ENNReal} : (0 : EReal) / b = 0 :=
  MulZeroClass.zero_mul (ENNReal.toEReal b⁻¹)

theorem EReal.top_div_ntop {b : ENNReal} (h : b ≠ ⊤) : (⊤ : EReal) / b = ⊤ := by
  apply EReal.top_mul_of_pos
  simp [h]

theorem EReal.bot_div_ntop {b : ENNReal} (h : b ≠ ⊤) : (⊥ : EReal) / b = ⊥ := by
  apply EReal.bot_mul_of_pos
  simp [h]

theorem EReal.mul_div_mul {a : EReal} {b c : ENNReal} (h : c ≠ 0) (h' : c ≠ ⊤) :
    (a * c) / (b * c) = a / b := by
  change (a * c) * (b * c)⁻¹ = a * b⁻¹
  suffices h : c * (b * c)⁻¹ = b⁻¹
  · rw [← h, mul_assoc]; norm_cast
  · calc
      c * (b * c)⁻¹ = c * (b⁻¹ * c⁻¹) := by rw [ENNReal.mul_inv (Or.inr h') (Or.inr h)]
                  _ = b⁻¹ * c⁻¹ * c   := mul_comm c (b⁻¹ * c⁻¹)
                  _ = b⁻¹ * (c⁻¹ * c) := mul_assoc b⁻¹ c⁻¹ c
                  _ = b⁻¹ * 1         := by rw [ENNReal.inv_mul_cancel h h']
                  _ = b⁻¹             := mul_one b⁻¹

theorem EReal.div_mul {a : EReal} {b c : ENNReal} (h : b ≠ 0 ∨ c ≠ ⊤) (h' : b ≠ ⊤ ∨ c ≠ 0) :
    (a / b) / c = a / (b * c) := by
  change (a * b⁻¹) * c⁻¹ = a * (b * c)⁻¹
  suffices this :
    b⁻¹ * c⁻¹ = (b * c)⁻¹
  · rw [← this, mul_assoc]; norm_cast
  · exact Eq.symm (ENNReal.mul_inv h h')

theorem EReal.div_left_mono (b : ENNReal) : Monotone fun a : EReal ↦ a / b := by
  intro a a' h
  apply mul_le_mul_of_nonneg_right h
  norm_cast
  exact bot_le

theorem EReal.div_left_mono' {a a' : EReal} (b : ENNReal) (h : a ≤ a') : a / b ≤ a' / b :=
  EReal.div_left_mono b h

theorem EReal.div_left_strictMono {b : ENNReal} (h : b ≠ 0) (h' : b ≠ ⊤) :
    StrictMono fun a : EReal ↦ a / b := by
  intro a c a_lt_c
  simp only
  apply lt_of_le_of_ne
  · exact EReal.div_left_mono' b (le_of_lt a_lt_c)
  · intro ab_eq_cb
    apply ne_of_lt a_lt_c
    rw [← @EReal.mul_inv_cancel a b h h', ab_eq_cb,
      @EReal.mul_inv_cancel c b h h']

theorem EReal.div_left_strictMono' {a a' : EReal} {b : ENNReal} (h₁ : b ≠ 0) (h₂ : b ≠ ⊤)
    (h₃ : a < a') :
    a / b < a' / b :=
  EReal.div_left_strictMono h₁ h₂ h₃

theorem EReal.le_div_iff_mul_le {a c : EReal} {b : ENNReal} (h : b ≠ 0) (h' : b ≠ ⊤) :
    a ≤ c / b ↔ a * b ≤ c := by
  nth_rw 1 [← @EReal.mul_inv_cancel a b h h']
  exact EReal.mul_div_right ▸ StrictMono.le_iff_le (EReal.div_left_strictMono h h')

theorem EReal.div_le_iff_le_mul {a c : EReal} {b : ENNReal} (h : b ≠ 0) (h' : b ≠ ⊤) :
    a / b ≤ c ↔ a ≤ b * c := by
  nth_rw 1 [← @EReal.mul_inv_cancel c b h h']
  rw [EReal.mul_div_right, mul_comm c b]
  exact StrictMono.le_iff_le (EReal.div_left_strictMono h h')

theorem EReal.nneg_div {a : EReal} {b : ENNReal} (h : 0 ≤ a) : 0 ≤ a / b :=
  le_of_eq_of_le (Eq.symm EReal.zero_div) (EReal.div_left_mono b h)

theorem EReal.npos_div {a : EReal} {b : ENNReal} (h : a ≤ 0) : a / b ≤ 0 :=
  le_of_le_of_eq (EReal.div_left_mono b h) EReal.zero_div

theorem EReal.div_right_distrib_of_nneg {a b : EReal} {c : ENNReal} (h : 0 ≤ a) (h' : 0 ≤ b) :
    (a + b) / c = (a / c) + (b / c) := EReal.right_distrib_of_nneg h h'

end ERealDiv

#lint
