/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Data.EReal.Inv
public import Mathlib.Basic.ENNReal.Inv

/-!
# Division of extended reals by extended nonnegative reals
We define a division of an extended real `EReal` by an extended nonnegative real `ENNReal`
as multiplication by the coercion of its inverse. An optional scoped instance of division
is provided.

`ERealDiv.EReal.divENNReal a b` inverts `b` in `ENNReal` before coercing it to
`EReal`. Unlike ordinary EReal division, positive numerators divided by zero
therefore give `⊤`. The optional mixed-division instance is scoped to `ERealDiv`;
statements use the named operation to avoid ambiguity with ordinary division.

The entropy development uses mathlib's `ExpGrowth` API and no longer needs this
operation, we could probably drop it.
-/

@[expose] public section

namespace ERealDiv

/--
Division of an extended real (`EReal`) by an extended nonnegative real (`ENNReal`). Defined by
inversion in [0, ∞], coercion to [-∞,+∞], and multiplication in [-∞,+∞]. -/
noncomputable def EReal.divENNReal (a : EReal) (b : ENNReal) : EReal := a * (b⁻¹ : ENNReal)

noncomputable scoped instance instHDivERealENNReal : HDiv EReal ENNReal EReal where
  hDiv := EReal.divENNReal

/-- Away from a zero denominator, mixed division agrees with ordinary division. -/
lemma EReal.divENNReal_eq_div (a : EReal) {b : ENNReal} (hb : b ≠ 0) :
    EReal.divENNReal a b = a / (b : EReal) := by
  by_cases htop : b = ⊤
  · simp [htop, EReal.divENNReal]
  lift b to NNReal using htop
  have hb' : b ≠ 0 := by simpa using hb
  simp only [EReal.divENNReal, div_eq_mul_inv, ← ENNReal.coe_inv hb',
    EReal.coe_nnreal_eq_coe_real, ← EReal.coe_inv, NNReal.coe_inv]

lemma EReal.div_eq_inv_mul {a : EReal} {b : ENNReal} :
    EReal.divENNReal a b = (b⁻¹ : ENNReal) * a := mul_comm _ _

lemma EReal.mul_div {a b : EReal} {c : ENNReal} :
    a * EReal.divENNReal b c = EReal.divENNReal (a * b) c := (mul_assoc _ _ _).symm

lemma EReal.mul_div_right {a c : EReal} {b : ENNReal} :
    EReal.divENNReal a b * c = EReal.divENNReal (a * c) b := by
  simp only [EReal.divENNReal, mul_right_comm]

lemma EReal.mul_inv_cancel {a : EReal} {b : ENNReal} (h : b ≠ 0) (h' : b ≠ ⊤) :
    EReal.divENNReal a b * b = a := by
  rw [EReal.divENNReal, mul_assoc, ← EReal.coe_ennreal_mul,
    ENNReal.inv_mul_cancel h h', EReal.coe_ennreal_one, mul_one]

@[simp] lemma EReal.div_one {a : EReal} : EReal.divENNReal a 1 = a := by
  simp [EReal.divENNReal]

@[simp] lemma EReal.div_top {a : EReal} : EReal.divENNReal a ⊤ = 0 := by
  simp [EReal.divENNReal]

lemma EReal.pos_div_zero {a : EReal} (h : 0 < a) : EReal.divENNReal a 0 = ⊤ := by
  simpa only [EReal.divENNReal, ENNReal.inv_zero, EReal.coe_ennreal_top] using
    EReal.mul_top_of_pos h

lemma EReal.neg_div_zero {a : EReal} (h : a < 0) : EReal.divENNReal a 0 = ⊥ := by
  simpa only [EReal.divENNReal, ENNReal.inv_zero, EReal.coe_ennreal_top] using
    EReal.mul_top_of_neg h

@[simp] lemma EReal.zero_div {b : ENNReal} : EReal.divENNReal 0 b = 0 := zero_mul _

lemma EReal.top_div_ntop {b : ENNReal} (h : b ≠ ⊤) : EReal.divENNReal ⊤ b = ⊤ :=
  EReal.top_mul_of_pos (EReal.coe_ennreal_pos.mpr (ENNReal.inv_pos.mpr h))

lemma EReal.bot_div_ntop {b : ENNReal} (h : b ≠ ⊤) : EReal.divENNReal ⊥ b = ⊥ :=
  EReal.bot_mul_of_pos (EReal.coe_ennreal_pos.mpr (ENNReal.inv_pos.mpr h))

lemma EReal.mul_div_mul {a : EReal} {b c : ENNReal} (h : c ≠ 0) (h' : c ≠ ⊤) :
    EReal.divENNReal (a * c) (b * c) = EReal.divENNReal a b := by
  have key : c * (b * c)⁻¹ = b⁻¹ := by
    rw [ENNReal.mul_inv (Or.inr h') (Or.inr h), mul_left_comm,
      ENNReal.mul_inv_cancel h h', mul_one]
  change (a * (c : EReal)) * ((b * c)⁻¹ : ENNReal) = a * (b⁻¹ : ENNReal)
  rw [mul_assoc, ← EReal.coe_ennreal_mul, key]

lemma EReal.div_mul {a : EReal} {b c : ENNReal} (h : b ≠ 0 ∨ c ≠ ⊤)
    (h' : b ≠ ⊤ ∨ c ≠ 0) :
    EReal.divENNReal (EReal.divENNReal a b) c = EReal.divENNReal a (b * c) := by
  simp only [EReal.divENNReal, ENNReal.mul_inv h h', EReal.coe_ennreal_mul, mul_assoc]

lemma EReal.div_left_mono (b : ENNReal) : Monotone fun a : EReal => EReal.divENNReal a b :=
  fun _ _ h => mul_le_mul_of_nonneg_right h (EReal.coe_ennreal_nonneg _)

lemma EReal.div_left_mono' {a a' : EReal} (b : ENNReal) (h : a ≤ a') :
    EReal.divENNReal a b ≤ EReal.divENNReal a' b := EReal.div_left_mono b h

lemma EReal.div_left_strictMono {b : ENNReal} (h : b ≠ 0) (h' : b ≠ ⊤) :
    StrictMono fun a : EReal => EReal.divENNReal a b := by
  intro a c hac
  apply lt_of_le_of_ne (EReal.div_left_mono b hac.le)
  intro heq
  change EReal.divENNReal a b = EReal.divENNReal c b at heq
  apply hac.ne
  rw [← @EReal.mul_inv_cancel a b h h', heq, EReal.mul_inv_cancel h h']

lemma EReal.div_left_strictMono' {a a' : EReal} {b : ENNReal} (h : b ≠ 0) (h' : b ≠ ⊤)
    (haa' : a < a') : EReal.divENNReal a b < EReal.divENNReal a' b :=
  EReal.div_left_strictMono h h' haa'

lemma EReal.le_div_iff_mul_le {a c : EReal} {b : ENNReal} (h : b ≠ 0) (h' : b ≠ ⊤) :
    a ≤ EReal.divENNReal c b ↔ a * b ≤ c := by
  rw [EReal.divENNReal_eq_div _ h]
  exact _root_.EReal.le_div_iff_mul_le (EReal.coe_ennreal_pos.mpr (pos_iff_ne_zero.mpr h))
    (EReal.coe_ennreal_eq_top_iff.not.mpr h')

lemma EReal.div_le_iff_le_mul {a c : EReal} {b : ENNReal} (h : b ≠ 0) (h' : b ≠ ⊤) :
    EReal.divENNReal a b ≤ c ↔ a ≤ b * c := by
  rw [EReal.divENNReal_eq_div _ h]
  exact _root_.EReal.div_le_iff_le_mul (EReal.coe_ennreal_pos.mpr (pos_iff_ne_zero.mpr h))
    (EReal.coe_ennreal_eq_top_iff.not.mpr h')

lemma EReal.nneg_div {a : EReal} {b : ENNReal} (h : 0 ≤ a) : 0 ≤ EReal.divENNReal a b :=
  mul_nonneg h (EReal.coe_ennreal_nonneg _)

lemma EReal.npos_div {a : EReal} {b : ENNReal} (h : a ≤ 0) : EReal.divENNReal a b ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg h (EReal.coe_ennreal_nonneg _)

lemma EReal.div_right_distrib_of_nneg {a b : EReal} {c : ENNReal} (h : 0 ≤ a) (h' : 0 ≤ b) :
    EReal.divENNReal (a + b) c = EReal.divENNReal a c + EReal.divENNReal b c :=
  EReal.right_distrib_of_nonneg h h'

end ERealDiv
