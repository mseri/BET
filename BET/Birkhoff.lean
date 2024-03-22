import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# Birkhoff's ergodic theorem

This file contains the proof of Birkhoff's ergodic theorem.

## Implementation notes

...

## References

* ....

-/

section Ergodic_Theory

open BigOperators MeasureTheory


/-
- `T` is a measure preserving map of a probability space `(α, μ)`,
- `φ : α → ℝ` is integrable.
-/
variable {α : Type*} [MeasurableSpace α]
variable {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
variable (T : α → α) (hT : MeasurePreserving T μ)
variable (φ : α → ℝ) (hphi : Integrable φ μ)


open Finset in
/-- The max of the first `n + 1` Birkhoff sums, i.e.,
`maxOfSums T φ x n` corresponds to `max {birkhoffSum T φ 1 x,..., birkhoffSum T φ (n + 1) x}`. -/
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
theorem maxOfSums_Monotone (x : α) : Monotone (fun n ↦ maxOfSums T φ x n) := by
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
theorem sup'_eq_iff_le {s : Finset β} [SemilatticeSup α] (H : s.Nonempty) (f : β → α) (hs : a ∈ s) :
    s.sup' H f = f a ↔ ∀ b ∈ s, f b ≤ f a := by
  constructor
  · intros h0 b h2
    rw [← h0]
    exact Finset.le_sup' f h2
  · intro h1
    have hle : s.sup' H f ≤ f a := by
      simp only [Finset.sup'_le_iff]
      exact h1
    exact (LE.le.ge_iff_eq hle).mp (Finset.le_sup' f hs)

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
/-- Claim 1: a convenient equality for `maxOfSums`. -/
theorem claim1 (n : ℕ) (x : α) :
    maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n = φ x - min 0 (maxOfSums T φ (T x) n) := by
  -- Consider `maxOfSums T φ x (n + 1) = max {birkhoffSum T φ 1 x,..., birkhoffSum T φ (n + 2) x}`
  -- tthe max is equal to the first term or the max of all the other terms
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
/-- eventual equality -/
theorem claim4 (x : α) (hx : (T x) ∈ divSet T φ ):
    ∀ᶠ n in atTop, maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n = φ x := by
  unfold divSet at hx
  simp at hx
  -- since `maxOfSums T φ (T x) n` → ∞, eventually `min 0 (maxOfSums T φ (T x) n) = 0`
  have h1 : ∀ᶠ n in atTop, min 0 (maxOfSums T φ (T x) n) = 0 := by
    have h0 : ∀ᶠ n in atTop, 0 ≤ maxOfSums T φ (T x) n := by
      exact Tendsto.eventually_ge_atTop hx 0
    simp at h0
    simp
    obtain ⟨k,hk⟩ := h0
    use k
  simp only [eventually_atTop, ge_iff_le] at h1
  obtain ⟨k,hk⟩ := h1
  simp
  use k
  intros m hm
  -- take advantage of claim 1
  have h3 := claim1 T φ m x
  rw [hk m hm, sub_zero] at h3
  exact h3

open Filter in
/-- eventual equality -/
theorem claim5 (x : α) (hx : x ∈ divSet T φ):
    ∀ᶠ n in atTop, maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n = φ x := by
  unfold divSet at hx
  simp at hx
  have hx' : Tendsto (fun n ↦ maxOfSums T φ x (n + 1)) atTop atTop := by
    exact (tendsto_add_atTop_iff_nat 1).mpr hx
  -- since `maxOfSums T φ x (n + 1)` → ∞, eventually `min 0 (maxOfSums T φ (T x) n) = 0`
  have h1 : ∀ᶠ n in atTop, min 0 (maxOfSums T φ (T x) n) = 0 := by
    have h2 : ∀ᶠ n in atTop, φ x + 1 ≤ maxOfSums T φ x (n + 1) := by
      exact Tendsto.eventually_ge_atTop hx' (φ x + 1)
    simp at h2
    obtain ⟨k, hk⟩ := h2
    simp
    use k
    intros n hn
    have h3 := hk n hn
    have h5 := eq_add_of_sub_eq' (claim1 T φ n x)
    rw [h5] at h3
    by_contra hf
    push_neg at hf
    have h4 : min 0 (maxOfSums T φ (T x) n) = maxOfSums T φ (T x) n := by
      simp
      apply le_of_lt
      exact hf
    rw [h4] at h5
    simp at h5
    linarith
  simp only [eventually_atTop, ge_iff_le] at h1
  obtain ⟨k,hk⟩ := h1
  simp
  use k
  intros m hm
  -- take advantage of claim 1
  have h3 := claim1 T φ m x
  rw [hk m hm, sub_zero] at h3
  exact h3

open Filter in
/-- Claim 2: the set of divergent points is invariant. -/
theorem divSet_inv : T⁻¹' (divSet T φ) = (divSet T φ) := by
  ext x
  constructor
  · intro hx
    have h2' : ∀ᶠ n in atTop, maxOfSums T φ (T x) n = maxOfSums T φ x (n + 1) - φ x := by
      -- there should be a slicker way of rearranging the equality in Tendsto ------------------
      simp
      have h2 := claim4 T φ x hx
      simp at h2
      obtain ⟨k, hk⟩ := h2
      use k
      intros n hn
      suffices hs : maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n = φ x by linarith
      exact hk n hn
      ------------------------------------------------------------------------------------------
    -- use the eventual equality
    have h5 : Tendsto (fun n ↦ maxOfSums T φ x (n + 1) - φ x) atTop atTop := by
      exact Tendsto.congr' h2' hx
    -- rearrange using properties of `Tendsto`
    have h6 : Tendsto (fun n ↦ maxOfSums T φ x (n + 1)) atTop atTop := by
      have h7 := tendsto_atTop_add_const_right atTop (φ x) h5
      simp at h7
      exact h7
    refine' (tendsto_add_atTop_iff_nat 1).mp _
    exact h6
  · intro hx
    have hx' : Tendsto (fun n ↦ maxOfSums T φ x (n + 1)) atTop atTop := by
      exact (tendsto_add_atTop_iff_nat 1).mpr hx
    -- eventually we have a precise equality between the two maxOfSums
    have h2' : ∀ᶠ n in atTop, maxOfSums T φ x (n + 1) - φ x = maxOfSums T φ (T x) n := by
      -- there should be a slicker way of rearranging the equality in Tendsto ------------------
      simp
      have h2 := claim5 T φ x hx
      simp at h2
      obtain ⟨k, hk⟩ := h2
      use k
      intros n hn
      suffices hs : maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n = φ x by linarith
      exact hk n hn
      ------------------------------------------------------------------------------------------
    exact Tendsto.congr' h2' (tendsto_atTop_add_const_right atTop (- φ x) hx')

/-- framed formula -/
theorem claim3 (x : α) : Monotone (fun n ↦ -(maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n)) := by
  unfold Monotone
  intros n m hnm
  simp_rw [claim1]
  simp
  by_cases hc : 0 ≤ maxOfSums T φ (T x) m
  · left
    exact hc
  · right
    exact maxOfSums_Monotone T φ (T x) hnm

-- theorem star_claim (x : α) (hx : x ∉ divSet  ) : ... ≤ 0 := by sorry

/-- The set of divergent points is measurable -/
theorem divSet_MeasurableSet : MeasurableSet (divSet T φ) := by
  sorry

open Filter Topology in
theorem claim6 : 0 ≤ ∫ x in (divSet T φ), φ x ∂μ := by
  have h0 (n : ℕ) : 0 ≤ ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1) - maxOfSums T φ x n) ∂μ := by
    have hn : n ≤ (n + 1) := by simp
    have h01 : ∀ x ∈ divSet T φ, 0 ≤ (maxOfSums T φ x (n + 1) - maxOfSums T φ x n) := by
      intros x hx
      have h00 := maxOfSums_Monotone T φ x hn
      linarith

    -- have h02 := set_integral_nonneg (divSet_MeasurableSet T φ) h01
    sorry
  have h1 (n : ℕ) : ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1) - maxOfSums T φ x n) ∂μ =
      ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n) ∂μ := by

    -- change of variables using that divSet is invariant
    sorry
  have h2 :
      Tendsto (fun n ↦ ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1)
      - maxOfSums T φ (T x) n) ∂μ) atTop (𝓝 (∫ x in (divSet T φ), φ x ∂μ)) := by

    -- use monotone convergence theorem
    sorry
  have h3 (n : ℕ) : 0 ≤ ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1)
      - maxOfSums T φ (T x) n) ∂μ := by
    calc 0 ≤ ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1) - maxOfSums T φ x n) ∂μ := h0 n
    _ = ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n) ∂μ := h1 n
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds h2 h3


/-
Monotone convergence theorem:
- lintegral_iSup
- lintegral_tendsto_of_tendsto_of_monotone
- lintegral_iSup'
-/

/- `A` is in `I = inv_sigma_algebra`. -/
-- idea: is it better to define a new type measureable sets in alpha and then restrict to that type?
-- def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ T⁻¹' S = S }
-- def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ IsInvariant (fun n x ↦ T^[n] x) S }

end Ergodic_Theory
