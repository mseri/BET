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
variable (T : α → α) (hT : MeasurePreserving T μ)
variable (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)


open Finset in
/-- The max of the first `n + 1` Birkhoff sums.
I.e., `maxOfSums T f x n` corresponds to `max {birkhoffSum T f 1 x,..., birkhoffSum T f (n + 1) x}`.
Indexing choice avoids max of empty set issue. -/
def maxOfSums (x : α) (n : ℕ) :=
    sup' (range (n + 1)) (nonempty_range_succ) (fun k ↦ birkhoffSum T f (k + 1) x)

theorem maxOfSums_zero : maxOfSums T f x 0 = f x := by
  unfold maxOfSums
  simp only [zero_add, Finset.range_one, Finset.sup'_singleton, birkhoffSum_one']

/-- `maxOfSums` is monotone (one step version). -/
theorem maxOfSums_succ_le (x : α) (n : ℕ) : (maxOfSums T f x n) ≤ (maxOfSums T f x (n + 1)) := by
  exact Finset.sup'_mono (fun k ↦ birkhoffSum T f (k + 1) x)
    (Finset.range_subset.mpr (Nat.le.step Nat.le.refl)) Finset.nonempty_range_succ

/-- `maxOfSums` is monotone (explict version). -/
theorem maxOfSums_le_le (x : α) (m n : ℕ) (hmn : m ≤ n) :
    (maxOfSums T f x m) ≤ (maxOfSums T f x n) := by
  induction' n with n hi
  rw [Nat.le_zero.mp hmn]
  rcases Nat.of_le_succ hmn with hc | hc
  exact le_trans (hi hc) (maxOfSums_succ_le T f x n)
  rw [hc]

/-- `maxOfSums` is monotone.
(Uncertain which is the best phrasing to keep of these options.) -/
theorem maxOfSums_le_le' (x : α) : Monotone (fun n ↦ maxOfSums T f x n) := by
  unfold Monotone
  intros n m hmn
  exact maxOfSums_le_le T f x n m hmn

open Filter in
/-- The set of divergent points `{ x | sup_n ∑_{i=0}^{n} f(T^i x) = ∞}`. -/
def divSet := { x : α | Tendsto (fun n ↦ maxOfSums T f x n) atTop atTop }












/- define `A := { x | sup_n ∑_{i=0}^{n} f(T^i x) = ∞}`.
def A := { x : α | ∃ n, ∀ C : ℝ, ∑ i in Finset.range n, f (T^[i] x) > C }

define `A := { x | lim_n ∑_{i=0}^{n} f(T^i x) = ∞}`.
-/
def A := { x : α | Filter.Tendsto (fun n ↦ ∑ i in Finset.range n, f (T^[i] x)) Filter.atTop Filter.atTop }

/- `A` is in `I = inv_sigma_algebra`. -/
-- idea: is it better to define a new type measureable sets in alpha and then restrict to that type?
-- def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ T⁻¹' S = S }
def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ IsInvariant (fun n x ↦ T^[n] x) S }

/- define `Φ_n : max { ∑_{i=0}^{n} φ ∘ T^i }_{k ≤ n}` -/

/- ∀ `x ∈ A`, `Φ_{n+1}(x) - Φ_{n}(T(x)) = φ(x) - min(0,Φ_{n}(T(x))) ≥ φ(x)` decreases to `φ(x)`. -/

/- Using dominated convergence, `0 ≤ ∫_A (Φ_{n+1} - Φ_{n}) dμ = ∫_A (Φ_{n+1} - Φ_{n} ∘ T) dμ → ∫_A φ dμ`. -/

/- `(1/n) ∑_{k=0}^{n-1} φ ∘ T^k ≤ Φ_n / n`. -/

/- If `x ∉ A`, `limsup_n (1/n) ∑_{k=0}^{n-1} φ ∘ T^i ≤ 0`. -/

/- If conditional expection of `φ` is negative, i.e., `∫_C φ dμ = ∫_C φ|_inv_sigmal_algebra dμ < 0` for all `C` in `inv_sigma_algebra` with `μ(C) > 0`,
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
