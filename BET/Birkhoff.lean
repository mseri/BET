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
- `φ g : α → ℝ` are integrable.
-/
variable {α : Type*} [MeasurableSpace α]
variable {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
variable (T : α → α) (hT : MeasurePreserving T μ)
variable (φ g φ : α → ℝ) (hf : Integrable φ μ) (hg : Integrable g μ)


open Finset in
/-- The max of the first `n + 1` Birkhoff sums.
I.e., `maxOfSums T φ x n` corresponds to `max {birkhoffSum T φ 1 x,..., birkhoffSum T φ (n + 1) x}`.
Indexing choice avoids max of empty set issue. -/
/- define `Φ_n : max { ∑_{i=0}^{n} φ ∘ T^i }_{k ≤ n}` -/
def maxOfSums (x : α) (n : ℕ) :=
    sup' (range (n + 1)) (nonempty_range_succ) (fun k ↦ birkhoffSum T φ (k + 1) x)

/- Note that maxOfSums T φ x n corresponds to Φ_{n+1} -/

theorem maxOfSums_zero : maxOfSums T φ x 0 = φ x := by
  unfold maxOfSums
  simp only [zero_add, Finset.range_one, Finset.sup'_singleton, birkhoffSum_one']

/-- `maxOfSums` is monotone (one step version). -/
theorem maxOfSums_succ_le (x : α) (n : ℕ) : (maxOfSums T φ x n) ≤ (maxOfSums T φ x (n + 1)) := by
  exact Finset.sup'_mono (fun k ↦ birkhoffSum T φ (k + 1) x)
    (Finset.range_subset.mpr (Nat.le.step Nat.le.refl)) Finset.nonempty_range_succ

/-- `maxOfSums` is monotone (explict version). -/
theorem maxOfSums_le_le (x : α) (m n : ℕ) (hmn : m ≤ n) :
    (maxOfSums T φ x m) ≤ (maxOfSums T φ x n) := by
  induction' n with n hi
  rw [Nat.le_zero.mp hmn]
  rcases Nat.of_le_succ hmn with hc | hc
  exact le_trans (hi hc) (maxOfSums_succ_le T φ x n)
  rw [hc]

/-- `maxOfSums` is monotone.
(Uncertain which is the best phrasing to keep of these options.) -/
theorem maxOfSums_le_le' (x : α) : Monotone (fun n ↦ maxOfSums T φ x n) := by
  unfold Monotone
  intros n m hmn
  exact maxOfSums_le_le T φ x n m hmn


open Filter in
/-- The set of divergent points `{ x | lim_n Φ_n x = ∞}`. -/
def divSet := { x : α | Tendsto (fun n ↦ maxOfSums T φ x n) atTop atTop }


/- ∀ `x ∈ A`, `Φ_{n+1}(x) - Φ_{n}(T(x)) = φ(x) - min(0,Φ_{n}(T(x))) ≥ φ(x)` decreases to `φ(x)`. -/

/-- Convenient combination of `birkhoffSum` terms. -/
theorem birkhoffSum_succ_image (n : ℕ) (x : α) :
      birkhoffSum T φ n (T x) = birkhoffSum T φ (n + 1) x - φ x := by
    rw [birkhoffSum_add T φ n 1 x]
    rw [eq_add_of_sub_eq' (birkhoffSum_apply_sub_birkhoffSum T φ n x)]
    simp
    exact add_sub (birkhoffSum T φ n x) (φ (T^[n] x)) (φ x)

-- TODO: clean the following, enquire if there is an easier way to extract it from mathlib.
/-- Would expect this to be in `Mathlib/Data/Finset/Lattice`. -/
theorem sup'_eq_iff_le {s : Finset β} [SemilatticeSup α] (H : s.Nonempty) (φ : β → α) (hs : a ∈ s) :
    s.sup' H φ = φ a ↔ ∀ b ∈ s, φ b ≤ φ a := by
  constructor
  intros h0 b h2
  rw [← h0]
  exact Finset.le_sup' φ h2
  intro h1
  have hle : s.sup' H φ ≤ φ a := by
    simp only [Finset.sup'_le_iff]
    exact h1
  exact (LE.le.ge_iff_eq hle).mp (Finset.le_sup' φ hs)


open Finset in
/-- Divide a range into two parts. Maybe this exists in mathlib? Simpler way to write the proof?-/
theorem range_union (n m : ℕ) : range (n + m) = (range n) ∪ (filter (n ≤ ·) (range (n + m))) := by
  ext k
  constructor
  by_cases hc : k < n
  intro hkr
  exact mem_union.mpr (Or.inl (mem_range.mpr hc))
  push_neg at hc
  intro hkr
  exact mem_union_right (range n) (mem_filter.mpr { left := hkr, right := hc })
  intros hku
  simp
  simp at hku
  rcases hku with h1 | h2
  exact Nat.lt_add_right m h1
  exact h2.left

open Finset in
/-- Claim 1 (Marco) -/
theorem maxOfSums_succ_image (n : ℕ) (x : α) :
    maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n = φ x - min 0 (maxOfSums T φ (T x) n) := by
  -- Consider `maxOfSums T φ x (n + 1) = max {birkhoffSum T φ 1 x,..., birkhoffSum T φ (n + 2) x}`
  by_cases hc : ∀ k ≤ n + 1, birkhoffSum T φ (k + 1) x ≤ birkhoffSum T φ 1 x
  -- Case when the max is achieved by first element.
  have h0 : maxOfSums T φ x (n + 1) = birkhoffSum T φ 1 x := by
    unfold maxOfSums
    rw [birkhoffSum_one']
    rw [birkhoffSum_one'] at hc
    have h12 : (range (n + 1 + 1)).Nonempty := nonempty_range_succ
    have h13 : 0 ∈ (range (n + 1 + 1)) := by
      refine mem_range.mpr (Nat.add_pos_right (n + 1) Nat.le.refl)
    have h11 := sup'_eq_iff_le h12 (fun k ↦ birkhoffSum T φ (k + 1) x) h13
    simp only [zero_add, birkhoffSum_one', mem_range] at h11
    have h15 : ∀ b < n + 1 + 1, birkhoffSum T φ (b + 1) x ≤ φ x := by
      intros k h16
      have h17 : k ≤ n + 1 := Nat.lt_succ.mp h16
      exact hc k h17
    exact h11.mpr h15
  have h1 : birkhoffSum T φ 1 x = φ x := birkhoffSum_one T φ x
  have h2 : ∀ k, birkhoffSum T φ k (T x) = birkhoffSum T φ (k + 1) x - φ x := by
    intro k
    exact birkhoffSum_succ_image T φ k x
  have h3 : ∀ k ≤ n + 1, birkhoffSum T φ k (T x) ≤ 0 := by
    intros k hk
    rw [h2]
    rw [h1] at hc
    simp only [tsub_le_iff_right, zero_add]
    exact hc k hk
  have h4 : maxOfSums T φ (T x) n ≤ 0 := by
    unfold maxOfSums
    simp only [sup'_le_iff, mem_range]
    intros k hk
    rw [Nat.lt_succ] at hk
    refine h3 (k + 1) (Nat.add_le_add hk Nat.le.refl)
  have h5 : min 0 (maxOfSums T φ (T x) n) = maxOfSums T φ (T x) n := min_eq_right h4
  linarith
  -- Case when max is not achieved by the first element
  push_neg at hc
  let bS := fun k ↦ birkhoffSum T φ (k + 1) x
  let s1 := range 1
  let s2 := filter (1 ≤ ·) (range (n + 2))
  have h19 : range (n + 2) = s1 ∪ s2 := by
    have h20 := range_union 1 (n + 1)
    rw [Nat.one_add (n + 1)] at h20
    exact h20
  have h21 : s2.Nonempty := by
    use 1

    sorry
  have h17 : sup' (range (n + 2)) nonempty_range_succ bS = bS 0 ⊔ sup' s2 h21 bS := by
    -- Now use `sup'_union`, `range_union` to divide `maxOfSums T φ x (n + 1)` into 2 pieces.

    sorry

  have h6 : maxOfSums T φ x (n + 1) =
      sup' (range (n + 1)) (nonempty_range_succ) (fun k ↦ birkhoffSum T φ (k + 2) x) := by
    unfold maxOfSums
    -- Since `hc`, the max is not achieved by the first element reduce to max over other terms.

    sorry
  have h7 : maxOfSums T φ (T x) n =
      sup' (range (n + 1)) (nonempty_range_succ) (fun k ↦ birkhoffSum T φ (k + 1) (T x)) := by
    exact rfl
  have h10 : maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n = φ x := by
    rw [h6, h7]
    have h18 (k : ℕ) := birkhoffSum_succ_image T φ (k + 1) x
    have h19 :
        (fun k ↦ birkhoffSum T φ (k + 2) x) = (fun k ↦ birkhoffSum T φ (k + 1) (T x) + φ x) := by

      sorry
    rw [h19]

    -- Use `sup'_comm` to allow sup to commute with the function.
    sorry
  have h8 : 0 ≤ maxOfSums T φ (T x) n := by
    unfold maxOfSums

    sorry
  have h9 : min 0 (maxOfSums T φ (T x) n) = 0 := by
    exact min_eq_left h8
  rw [h9, h6, h7]

  sorry



open Filter in
/-- The set of divergent points is invariant. -/
theorem divSet_inv : T⁻¹' (divSet T φ) = (divSet T φ) := by
  sorry




/- `A` is in `I = inv_sigma_algebra`. -/
-- idea: is it better to define a new type measureable sets in alpha and then restrict to that type?
-- def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ T⁻¹' S = S }
def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ IsInvariant (fun n x ↦ T^[n] x) S }


/- Using dominated convergence, `0 ≤ ∫_A (Φ_{n+1} - Φ_{n}) dμ = ∫_A (Φ_{n+1} - Φ_{n} ∘ T) dμ → ∫_A φ dμ`. -/

/- `(1/n) ∑_{k=0}^{n-1} φ ∘ T^k ≤ Φ_n / n`. -/

/- If `x ∉ A`, `limsup_n (1/n) ∑_{k=0}^{n-1} φ ∘ T^i ≤ 0`. -/

/- If conditional expection of `φ` is negative, i.e., `∫_C φ dμ = ∫_C φ|_inv_sigmal_algebra dμ < 0` for all `C` in `inv_sigma_algebra` with `μ(C) > 0`,
then `μ(A) = 0`. -/

/- Then (assumptions as prior step) `limsup_n (1/n) ∑_{k=0}^{n-1} φ ∘ T^i ≤ 0` a.e. -/

/- Let `φ = φ - φ|_I - ε`. -/

/- `f_I ∘ T = φ|_I` and so `(1/n) ∑_{k=0}^{n-1} φ ∘ T^k = (1/n) ∑_{k=0}^{n-1} φ ∘ T^k - f_I - ε`. -/

/- `limsup_n (1/n) ∑_{k=0}^{n-1} φ ∘ T^i ≤ φ|_I + ε` a.e. -/

/- Replacing `φ` with `-φ`  we get the lower bound. -/

/- Birkhoff's theorem: Almost surely, `birkhoffAverage ℝ φ g n x` converges to the conditional expectation of `φ`. -/


/- If `T` is ergodic, show that the invariant sigma-algebra is a.e. trivial. -/

/- Show that the conditional expectation with respect to an a.e. trivial subalgebra is a.e.
the integral. -/

/- Birkhoff theorem for ergodic maps. -/

end Ergodic_Theory
