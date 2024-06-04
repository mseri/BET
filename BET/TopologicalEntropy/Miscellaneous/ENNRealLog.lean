/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Damien Thomine
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Instances.EReal

/-!
# Extended nonnegative real logarithm
We define `log` as an extension of the logarithm of a positive real
to the extended nonnegative reals `ENNReal`. The function takes values
in the extended reals `EReal`, with `log 0 = ⊥` and `log ⊤ = ⊤`.

## Main definitions
- `log`: The extension of the real logarithm to `ENNReal`.
- `log_OrderIso`, `log_equiv`: `log` seen respectively
as an order isomorphism and an homeomorphism.

## Main Results
- `log_strictMono`: `log` is increasing;
- `log_injective`, `log_surjective`, `log_bijective`: `log` is
  injective, surjective, and bijective;
- `log_mul_add`, `log_pow`, `log_pow`: `log` satisfy
the identities `log (x * y) = log x + log y` and `log (x * y) = y * log x`
(with either `y ∈ ℕ` or `y ∈ ℝ`).

## Tags
ENNReal, EReal, logarithm
-/

namespace ENNReal


/-! ### Definition -/

section Definition

/--
The logarithm function defined on the extended nonnegative reals `ENNReal`
to the extended reals `EReal`. Coincides with the usual logarithm function
and with `Real.log` on positive reals, and takes values `log 0 = ⊥` and `log ⊤ = ⊤`.
Conventions about multiplication in `ENNReal` and addition in `EReal` make the identity
`log (x * y) = log x + log y` unconditionnal. --/
noncomputable def log (x : ENNReal) : EReal :=
  if x = 0 then ⊥
    else if x = ⊤ then ⊤
    else Real.log (ENNReal.toReal x)

@[simp]
theorem log_zero : log 0 = ⊥ := by
  simp only [log, ↓reduceIte]

@[simp]
theorem log_one : log 1 = 0 := by
  simp only [log, one_ne_zero, ↓reduceIte, one_ne_top, one_toReal, Real.log_one, EReal.coe_zero]

@[simp]
theorem log_top : log ⊤ = ⊤ := by
  simp only [log, top_ne_zero, ↓reduceIte]

theorem log_pos_real {x : ENNReal} (h : x ≠ 0) (h' : x ≠ ⊤) :
    log x = Real.log (ENNReal.toReal x) := by
  simp only [log, h, ↓reduceIte, h']

theorem log_pos_real' {x : ENNReal} (h : 0 < x.toReal) :
    log x = Real.log (ENNReal.toReal x) := by
  simp only [log, Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 h).1), ↓reduceIte,
  ne_of_lt (ENNReal.toReal_pos_iff.1 h).2]

theorem log_of_nNReal {x : NNReal} (h : x ≠ 0) :
    log (ENNReal.ofReal x) = Real.log x := by
  simp only [log, ofReal_coe_nnreal, coe_eq_zero, h, ↓reduceIte, coe_ne_top, coe_toReal]

end Definition


/-! ### Monotonicity -/

section Monotonicity

theorem log_strictMono : StrictMono log := by
  intro x y h
  unfold log
  rcases ENNReal.trichotomy x with (x_zero | x_top | x_real)
  . rcases ENNReal.trichotomy y with (y_zero | y_top | y_real)
    . exfalso
      rw [x_zero, y_zero] at h
      exact lt_irrefl 0 h
    . simp only [x_zero, ↓reduceIte, y_top, top_ne_zero, bot_lt_top]
    . simp only [x_zero, ↓reduceIte, Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1),
      ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2, EReal.bot_lt_coe]
  . exfalso
    exact (ne_top_of_lt h) x_top
  . simp only [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).1), ↓reduceIte,
    ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).2]
    rcases ENNReal.trichotomy y with (y_zero | y_top | y_real)
    . exfalso
      rw [y_zero, ← ENNReal.bot_eq_zero] at h
      exact not_lt_bot h
    . simp only [y_top, top_ne_zero, ↓reduceIte, EReal.coe_lt_top]
    . simp only [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1), ↓reduceIte,
      ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2, EReal.coe_lt_coe_iff]
      apply Real.log_lt_log x_real
      apply (ENNReal.toReal_lt_toReal (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).2)
        (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2)).2 h

theorem log_monotone : Monotone log :=
  StrictMono.monotone log_strictMono

theorem log_injective : Function.Injective log :=
  StrictMono.injective log_strictMono

theorem log_surjective : Function.Surjective log := by
  intro y
  cases' eq_bot_or_bot_lt y with y_bot y_nbot
  · rw [y_bot]
    use ⊥
    exact log_zero
  cases' eq_top_or_lt_top y with y_top y_ntop
  · rw [y_top]
    use ⊤
    exact log_top
  use ENNReal.ofReal (Real.exp y.toReal)
  have exp_y_pos := not_le_of_lt (Real.exp_pos y.toReal)
  simp only [log, ofReal_eq_zero, exp_y_pos, ↓reduceIte, ofReal_ne_top]
  rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos y.toReal)), Real.log_exp y.toReal]
  exact EReal.coe_toReal (ne_of_lt y_ntop) (Ne.symm (ne_of_lt y_nbot))

theorem log_bijective : Function.Bijective log :=
  ⟨log_injective, log_surjective⟩

/-- `log` as an order isomorphism. --/
@[simps!]
noncomputable def log_OrderIso : ENNReal ≃o EReal :=
  StrictMono.orderIsoOfSurjective log log_strictMono log_surjective

theorem log_eq_iff {x y : ENNReal} : x = y ↔ log x = log y := by
  apply Iff.intro
  · intro h
    rw [h]
  · exact @log_injective x y

theorem log_eq_bot_iff {x : ENNReal} : x = 0 ↔ log x = ⊥ := by
  rw [← log_zero]
  exact @log_eq_iff x 0

theorem log_eq_one_iff {x : ENNReal} : x = 1 ↔ log x = 0 := by
  rw [← log_one]
  exact @log_eq_iff x 1

theorem log_eq_top_iff {x : ENNReal} : x = ⊤ ↔ log x = ⊤ := by
  rw [← log_top]
  exact @log_eq_iff x ⊤

theorem log_lt_iff_lt {x y : ENNReal} : x < y ↔ log x < log y :=
  Iff.symm (OrderIso.lt_iff_lt log_OrderIso)

theorem log_bot_lt_iff {x : ENNReal} : 0 < x ↔ ⊥ < log x := by
  rw [← log_zero]
  exact @log_lt_iff_lt 0 x

theorem log_lt_top_iff {x : ENNReal} : x < ⊤ ↔ log x < ⊤ := by
  rw [← log_top]
  exact @log_lt_iff_lt x ⊤

theorem log_lt_one_iff {x : ENNReal} : x < 1 ↔ log x < 0 := by
  rw [← log_one]
  exact @log_lt_iff_lt x 1

theorem log_one_lt_iff {x : ENNReal} : 1 < x ↔ 0 < log x := by
  rw [← log_one]
  exact @log_lt_iff_lt 1 x

theorem log_le_iff_le {x y : ENNReal} : x ≤ y ↔ log x ≤ log y :=
  Iff.symm (OrderIso.le_iff_le log_OrderIso)

theorem log_le_one_iff (x : ENNReal) : x ≤ 1 ↔ log x ≤ 0 := by
  rw [← log_one]
  exact @log_le_iff_le x 1

theorem log_one_le_iff {x : ENNReal} : 1 ≤ x ↔ 0 ≤ log x := by
  rw [← log_one]
  exact @log_le_iff_le 1 x

end Monotonicity


/-! ### Algebraic properties -/

section Morphism

theorem log_mul_add {x y : ENNReal} : log (x * y) = log x + log y := by
  rcases ENNReal.trichotomy x with (x_zero | x_top | x_real)
  · simp only [x_zero, zero_mul, log_zero, EReal.bot_add]
  · rw [x_top, log_top]
    rcases ENNReal.trichotomy y with (y_zero | y_top | y_real)
    · rw [y_zero, mul_zero, log_zero, EReal.add_bot]
    · simp only [y_top, ne_eq, top_ne_zero, not_false_eq_true, mul_top, log_top, EReal.top_add_top]
    · rw [log_pos_real' y_real, ENNReal.top_mul', EReal.top_add_coe, ← log_eq_top_iff]
      simp only [ite_eq_right_iff, zero_ne_top, imp_false]
      exact Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1)
  · rw [log_pos_real' x_real]
    rcases ENNReal.trichotomy y with (y_zero | y_top | y_real)
    · rw [y_zero, mul_zero, log_zero, EReal.add_bot]
    · rw [y_top, mul_top', log_top, EReal.coe_add_top, ← log_eq_top_iff]
      simp only [ite_eq_right_iff, zero_ne_top, imp_false]
      exact Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).1)
    · have xy_real := Real.mul_pos x_real y_real
      rw [← ENNReal.toReal_mul] at xy_real
      rw [log_pos_real' xy_real, log_pos_real' y_real, ENNReal.toReal_mul]
      norm_cast
      exact Real.log_mul (Ne.symm (ne_of_lt x_real)) (Ne.symm (ne_of_lt y_real))

theorem log_pow {x : ENNReal} {n : ℕ} : log (x ^ n) = (n : ENNReal) * log x := by
  by_cases h_n_pos : n = 0
  · rw [h_n_pos, pow_zero x]
    simp only [log_one, CharP.cast_eq_zero, EReal.coe_ennreal_zero, zero_mul]
  replace h_n_pos := Nat.pos_of_ne_zero h_n_pos
  rcases ENNReal.trichotomy x with (x_zero | x_top | x_real)
  · rw [x_zero, zero_pow (Ne.symm (ne_of_lt h_n_pos)), log_zero, EReal.mul_bot_of_pos]
    norm_cast
  · rw [x_top, ENNReal.top_pow h_n_pos, log_top, EReal.mul_top_of_pos]
    norm_cast
  · replace x_real := ENNReal.toReal_pos_iff.1 x_real
    have x_ne_zero := Ne.symm (LT.lt.ne x_real.1)
    have x_ne_top := LT.lt.ne x_real.2
    simp only [log, pow_eq_zero_iff', x_ne_zero, ne_eq, false_and, ↓reduceIte, pow_eq_top_iff,
      x_ne_top, toReal_pow, Real.log_pow, EReal.coe_mul]
    rfl

theorem log_rpow {x : ENNReal} {y : ℝ} : log (x ^ y) = y * log x := by
  rcases lt_trichotomy y 0 with (y_neg | y_zero | y_pos)
  · rcases ENNReal.trichotomy x with (x_zero | x_top | x_real)
    · rw [x_zero, ENNReal.zero_rpow_def y]
      simp only [not_lt_of_lt y_neg, ↓reduceIte, ne_of_lt y_neg, log_top, log_zero]
      exact Eq.symm (EReal.coe_mul_bot_of_neg y_neg)
    · rw [x_top, ENNReal.top_rpow_of_neg y_neg, log_zero, log_top]
      exact Eq.symm (EReal.coe_mul_top_of_neg y_neg)
    · have x_ne_zero := Ne.symm (LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).1)
      have x_ne_top := LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).2
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      rw [← ENNReal.toReal_rpow x y]
      apply Real.log_rpow x_real y
  · rw [y_zero, @ENNReal.rpow_zero x, log_one, EReal.coe_zero, zero_mul]
  · rcases ENNReal.trichotomy x with (x_zero | x_top | x_real)
    · rw [x_zero, ENNReal.zero_rpow_of_pos y_pos, log_zero, EReal.mul_bot_of_pos]
      norm_cast
    · rw [x_top, ENNReal.top_rpow_of_pos y_pos, log_top, EReal.mul_top_of_pos]
      norm_cast
    · have x_ne_zero := Ne.symm (LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).1)
      have x_ne_top := LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).2
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      rw [← ENNReal.toReal_rpow x y]
      apply Real.log_rpow x_real y

end Morphism


/-! ### Topological properties -/

section Continuity

/-- `log` as an homeomorphism. --/
@[simps!]
noncomputable def log_Homeomorph : ENNReal ≃ₜ EReal :=
  OrderIso.toHomeomorph log_OrderIso

@[continuity]
theorem log_Continuous : Continuous log :=
  Homeomorph.continuous log_Homeomorph

end Continuity

#lint

end ENNReal
