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
variable (φ : α → ℝ)
-- variable (f g φ : α → ℝ) (hf : Integrable φ μ) (hg : Integrable g μ)


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

/-- Would expect this to be in `Mathlib/Data/Finset/Lattice`.
Or perhaps there is already an easier way to extract it from mathlib? -/
theorem sup'_eq_iff_le {s : Finset β} [SemilatticeSup α] (H : s.Nonempty) (φ : β → α) (hs : a ∈ s) :
    s.sup' H φ = φ a ↔ ∀ b ∈ s, φ b ≤ φ a := by
  constructor
  · intros h0 b h2
    rw [← h0]
    exact Finset.le_sup' φ h2
  · intro h1
    have hle : s.sup' H φ ≤ φ a := by
      simp only [Finset.sup'_le_iff]
      exact h1
    exact (LE.le.ge_iff_eq hle).mp (Finset.le_sup' φ hs)

/-- convenient because used several times in proving claim 1 -/
theorem map_range_Nonempty (n : ℕ) : (Finset.map (addLeftEmbedding 1)
    (Finset.range (n + 1))).Nonempty := by
  use 1
  refine Finset.mem_map.mpr ?h.a
  use 0
  constructor
  · simp only [Finset.mem_range, add_pos_iff, zero_lt_one, or_true]
  · exact rfl

open Finset in
/-- modified from mathlib to make f explicit - isn't the version in mathlib inconvenient? -/
theorem comp_sup'_eq_sup'_comp_alt [SemilatticeSup α] [SemilatticeSup γ] {s : Finset β}
    (H : s.Nonempty) (f : β → α)
    (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) : g (s.sup' H f) = s.sup' H (g ∘ f) := by
  refine' H.cons_induction _ _ <;> intros <;> simp [*]

open Finset in
/-- Claim 1 -/
theorem maxOfSums_succ_image (n : ℕ) (x : α) :
    maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n = φ x - min 0 (maxOfSums T φ (T x) n) := by
  -- Consider `maxOfSums T φ x (n + 1) = max {birkhoffSum T φ 1 x,..., birkhoffSum T φ (n + 2) x}`
  -- hc tells that the max is equal to the first term or the max of all the other terms
  have hc : maxOfSums T φ x (n + 1) = birkhoffSum T φ 1 x ∨
      maxOfSums T φ x (n + 1) = sup' (map (addLeftEmbedding 1) (range (n + 1)))
      (map_range_Nonempty n) fun k ↦ birkhoffSum T φ (k + 1) x := by
    have h0 : range (n + 2) = {0} ∪ map (addLeftEmbedding 1) (range (n + 1)) := by
      rw [← range_one, ← Nat.add_comm 1 (n + 1)]
      exact range_add_eq_union 1 (n + 1)
    have h1 := sup'_union (singleton_nonempty 0) (map_range_Nonempty n)
        (fun k ↦ birkhoffSum T φ (k + 1) x)
    simp_rw [← h0] at h1
      -- the max is the max of first term and the max of all the other terms
    have h2 : maxOfSums T φ x (n + 1) = max (birkhoffSum T φ 1 x)
        (sup' (map (addLeftEmbedding 1) (range (n + 1))) (map_range_Nonempty n)
        fun k ↦ birkhoffSum T φ (k + 1) x) := by
      unfold maxOfSums
      rw [h1]
      simp
      exact rfl
    have h3 := max_choice (birkhoffSum T φ 1 x)
      (sup' (map (addLeftEmbedding 1) (range (n + 1))) (map_range_Nonempty n)
      fun k ↦ birkhoffSum T φ (k + 1) x)
    rw [← h2] at h3
    exact h3
  -- divide into cases
  rcases hc with hcl | hcr
  -- case when max is the first term
  have h35 : ∀ k ∈ range (n + 1 + 1), birkhoffSum T φ (k + 1) x ≤ birkhoffSum T φ 1 x := by
    have h41 : 0 ∈ (range (n + 1 + 1)) := mem_range.mpr (Nat.add_pos_right (n + 1) Nat.le.refl)
    have h11 := sup'_eq_iff_le nonempty_range_succ (fun k ↦ birkhoffSum T φ (k + 1) x) h41
    simp at h11
    simp
    refine' h11.mp _
    unfold maxOfSums at hcl
    simp at hcl
    exact hcl
  have h1 : birkhoffSum T φ 1 x = φ x := birkhoffSum_one T φ x
  have h2 : ∀ k, birkhoffSum T φ k (T x) = birkhoffSum T φ (k + 1) x - φ x := by
    intro k
    exact birkhoffSum_succ_image T φ k x
  have h3 : ∀ k ≤ n + 1, birkhoffSum T φ k (T x) ≤ 0 := by
    intros k hk
    rw [h2]
    rw [h1] at hcl
    simp only [tsub_le_iff_right, zero_add]
    rw [birkhoffSum_one'] at h35
    exact h35 k (mem_range_succ_iff.mpr hk)
  have h4 : maxOfSums T φ (T x) n ≤ 0 := by
    unfold maxOfSums
    simp only [sup'_le_iff, mem_range]
    intros k hk
    rw [Nat.lt_succ] at hk
    refine h3 (k + 1) (Nat.add_le_add hk Nat.le.refl)
  have h5 : min 0 (maxOfSums T φ (T x) n) = maxOfSums T φ (T x) n := min_eq_right h4
  linarith
  -- case when max is not achieved by the first element
  rw [sup'_map (fun k ↦ birkhoffSum T φ (k + 1) x) (map_range_Nonempty n)] at hcr
  simp at hcr
  have h1 : maxOfSums T φ x (n + 1) = φ x + maxOfSums T φ (T x) n := by
    rw [hcr]
    unfold maxOfSums
    have h4 (k : ℕ) (_ : k ∈ range (n + 1)) := birkhoffSum_succ' T φ (k + 1) x
    have h5 := sup'_congr nonempty_range_succ rfl h4
    have h7 := comp_sup'_eq_sup'_comp_alt (nonempty_range_succ : (range (n + 1)).Nonempty)
      (fun k ↦ birkhoffSum T φ (k + 1) (T x)) (fun a ↦ (φ x) + a ) (fun a b ↦ add_sup a b (φ x))
    simp at h7
    simp at h5
    simp_rw [← h7] at h5
    simp_rw [← h5, add_comm]
  -- in this case the min is zero
  have h8 : 0 ≤ maxOfSums T φ (T x) n := by
    have h9 : φ x ≤ maxOfSums T φ x (n + 1) := by
      unfold maxOfSums
      have h41 : 0 ∈ (range (n + 1 + 1)) := mem_range.mpr (Nat.add_pos_right (n + 1) Nat.le.refl)
      have h10 := le_sup' (fun k ↦ birkhoffSum T φ (k + 1) x) h41
      simp at h10
      norm_num
      exact h10
    linarith
  rw [min_eq_left h8, h1]
  simp

open Filter in
/-- The set of divergent points is invariant. -/
theorem divSet_inv : T⁻¹' (divSet T φ) = (divSet T φ) := by
  sorry

/- `A` is in `I = inv_sigma_algebra`. -/
-- idea: is it better to define a new type measureable sets in alpha and then restrict to that type?
-- def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ T⁻¹' S = S }
def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ IsInvariant (fun n x ↦ T^[n] x) S }

end Ergodic_Theory
