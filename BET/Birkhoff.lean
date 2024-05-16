/-
Copyright 2023 The Authors
Released under Apache 2.0 license as described in the file LICENSE
Authors: Guillaume Dubach, Marco Lenci, Sébastien Gouëzel, Marcello Seri, Oliver Butterley
-/

import Mathlib.Tactic
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# Birkhoff's ergodic theorem

This file defines Birkhoff sums, other related notions and proves Birkhoff's ergodic theorem.

## Implementation notes

...

## References

* ....

-/

section Ergodic_Theory

open BigOperators MeasureTheory


/-
- `T` is a measure preserving map of a probability space `(α, μ)`,
- `f g : α → ℝ` are integrable.
-/
variable {α : Type*} [MeasurableSpace α]
variable {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
variable {T : α → α} (hT : MeasurePreserving T μ)
variable {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
variable (x : α)
variable (n : ℕ)

/- define `A := { x | sup_n ∑_{i=0}^{n} f(T^i x) = ∞}`.
def A := { x : α | ∃ n, ∀ C : ℝ, ∑ i in Finset.range n, f (T^[i] x) > C }

define `A := { x | lim_n ∑_{i=0}^{n} f(T^i x) = ∞}`.
-/
def A := { x : α | Filter.Tendsto (fun n ↦ ∑ i in Finset.range n, f (T^[i] x)) Filter.atTop Filter.atTop }

/- `A` is in `I = inv_sigma_algebra`. -/
-- idea: is it better to define a new type measurable sets in alpha and then restrict to that type?
-- def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ T⁻¹' S = S }
def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ IsInvariant (fun n x ↦ T^[n] x) S }

/- define `Φ_n : max { ∑_{i=0}^{n} φ ∘ T^i }_{k ≤ n}` -/

/- ∀ `x ∈ A`, `Φ_{n+1}(x) - Φ_{n}(T(x)) = φ(x) - min(0,Φ_{n}(T(x))) ≥ φ(x)` decreases to `φ(x)`. -/

/- Using dominated convergence, `0 ≤ ∫_A (Φ_{n+1} - Φ_{n}) dμ = ∫_A (Φ_{n+1} - Φ_{n} ∘ T) dμ → ∫_A φ dμ`. -/

/- `(1/n) ∑_{k=0}^{n-1} φ ∘ T^k ≤ Φ_n / n`. -/

/- If `x ∉ A`, `limsup_n (1/n) ∑_{k=0}^{n-1} φ ∘ T^i ≤ 0`. -/

/- If conditional expectation of `φ` is negative, i.e., `∫_C φ dμ = ∫_C φ|_inv_sigmal_algebra dμ < 0` for all `C` in `inv_sigma_algebra` with `μ(C) > 0`,
then `μ(A) = 0`. -/

/- Then (assumptions as prior step) `limsup_n (1/n) ∑_{k=0}^{n-1} φ ∘ T^i ≤ 0` a.e. -/

/- Let `φ = f - f|_I - ε`. -/

/- `f_I ∘ T = f|_I` and so `(1/n) ∑_{k=0}^{n-1} f ∘ T^k = (1/n) ∑_{k=0}^{n-1} f ∘ T^k - f_I - ε`. -/

/- `limsup_n (1/n) ∑_{k=0}^{n-1} f ∘ T^i ≤ f|_I + ε` a.e. -/

/- Replacing `f` with `-f`  we get the lower bound. -/

/- Birkhoff's theorem: Almost surely, `birkhoffAverage ℝ f g n x` converges to the conditional expectation of `f`. -/

#check birkhoffAverage ℝ T f n x

/- If `T` is ergodic, show that the invariant sigma-algebra is a.e. trivial. -/

/- Show that the conditional expectation with respect to an a.e. trivial subalgebra is a.e.
the integral. -/

/- Birkhoff theorem for ergodic maps. -/

end Ergodic_Theory
