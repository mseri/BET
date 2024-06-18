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

/- TODO:
  - define Birkhoff Average on actions, to be done much later, after mathlibization
  - update the proof to this more general setting
  - refactor using partialSups and ℕ →o ℝ
-/

section Ergodic_Theory

open BigOperators MeasureTheory

/-
- `T` is a measure preserving map of a probability space `(α, μ)`,
- `φ : α → ℝ` is integrable.
-/
variable {α : Type*} [m0: MeasurableSpace α]
/-
The original sigma-algebra is now named m0 because we need to distiguish
b/w that and the invariant sigma-algebra.
-/
variable {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
variable (T : α → α) (hT : MeasurePreserving T μ)
variable (φ : α → ℝ) (hphi : Integrable φ μ) (hphim : Measurable φ)
/- For the moment it's convenient to also assume that φ is measurable
because for Lean Integrable means almost everywhere (strongly) measurable
and it's not convenient to carry around "a.e." in the main prooof.
We can probably fix this later by taking an almost everywhere
(strongly) measurable fn, turn it into a truly measurable function which is
a.e. equal to the given function, apply the thoerem to this one and then
derive conclusions for the original function -/
variable (R : Type*) [DivisionSemiring R] [Module R ℝ] -- used for birkhoffAverage

/- when calling the definition below, T will be an explicit argument.
This is for two reasons:
- we made T an explicit variable (and we couldn't do otherwise, Floris explained), and
- we used T in the construction of the definition -/
def invSigmaAlg : MeasurableSpace α where
  -- same as `MeasurableSet' s := MeasurableSet s ∧ T ⁻¹' s = s`
  MeasurableSet' := fun s ↦ MeasurableSet s ∧ T ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, rfl⟩
  measurableSet_compl := fun h ⟨hinit1, hinit2⟩ ↦ ⟨MeasurableSet.compl hinit1, congrArg compl hinit2⟩

  measurableSet_iUnion := by
    -- now we explicitly want s, so we need to intro it
    intro s
    dsimp
    intro hinit
    constructor
    · have hi1st : ∀ i, MeasurableSet (s i) := fun i ↦(hinit i).left
      exact MeasurableSet.iUnion hi1st
    · have hi2nd : ∀ i, T ⁻¹'(s i) = s i := fun i ↦ (hinit i).right
      rw [Set.preimage_iUnion]
      exact Set.iUnion_congr hi2nd

/- it was hard to find out what `m ≤ m0` meant, when `m, m0` are measurable spaces.
Hovering over the `≤` sign in infoview and following the links explained it:
instance : LE (MeasurableSpace α) where le m₁ m₂ := ∀ s, MeasurableSet[m₁] s → MeasurableSet[m₂] s
-/
/-- The invariant sigma algebra of T is a subalgebra of the measure space -/
lemma leq_InvSigmaAlg_FullAlg : invSigmaAlg T ≤ m0 := fun _ hs ↦ hs.left

open Finset in
/-- The max of the first `n` Birkhoff sums, i.e.,
`maxOfSums T φ x n` corresponds to
`max {birkhoffSum T φ 1 x,..., birkhoffSum T φ (n + 1) x}`.
This is because `birkhoffSum T φ 0 x := 0` is defined to be a sum over the empty set. -/
def maxOfSums (x : α) : OrderHom ℕ ℝ :=
  partialSups (fun n ↦ birkhoffSum T φ (n+1) x)

-- was:
-- def maxOfSums (x : α) (n : ℕ) :=
--     sup' (range (n + 1)) (nonempty_range_succ) (fun k ↦ birkhoffSum T φ (k + 1) x)

/- Note that maxOfSums T φ x n corresponds to Φ_{n+1} in our notates -/

theorem maxOfSums_zero : maxOfSums T φ x 0 = φ x := by
  unfold maxOfSums
  simp

/-- `maxOfSums` is monotone (one step version). -/
theorem maxOfSums_succ_le (x : α) (n : ℕ) : (maxOfSums T φ x n) ≤ (maxOfSums T φ x (n + 1)) := by
  unfold maxOfSums
  simp

/-- `maxOfSums` is monotone (general steps version). -/
theorem maxOfSums_le_le (x : α) (m n : ℕ) (hmn : m ≤ n) :
    (maxOfSums T φ x m) ≤ (maxOfSums T φ x n) := by
  induction' n with n hi
  · rw [Nat.le_zero.mp hmn]
  · rcases Nat.of_le_succ hmn with hc | hc
    exact le_trans (hi hc) (maxOfSums_succ_le T φ x n)
    rw [hc]

/-- `maxOfSums` is monotone.
(Uncertain which is the best phrasing to keep of these options.) -/
theorem maxOfSums_Monotone (x : α) : Monotone (fun n ↦ maxOfSums T φ x n) := maxOfSums_le_le T φ x

open Filter in
/-- The set of divergent points `{ x | lim_n Φ_{n+1} x = ∞}`. -/
def divSet := { x : α | Tendsto (fun n ↦ maxOfSums T φ x n) atTop atTop }

@[measurability]
lemma birkhoffSum_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    Measurable (birkhoffSum f φ n) := by
  apply Finset.measurable_sum
  measurability

@[measurability]
lemma maxOfSums_measurable
  : ∀ n : ℕ , Measurable (fun x ↦ maxOfSums T φ x n) := by
  intro n
  induction n
  · simp only [maxOfSums_zero]
    exact hphim
  · unfold maxOfSums
    measurability

    -- measurability


#exit


/- can probably be stated without the '[m0]' part -/
lemma divSet_measurable : MeasurableSet[m0] (divSet T φ) := by sorry
/-
For the above lemma we need to use that the set A, defined by all x s.t.
lim_n φ_n = ∞ is m0-measurable. Since φ is measurable (b/c integrable)
it all boils down to understanding what Lean means with φ : α → ℝ being
measurable, that is, wrt to what sigma-algebra in ℝ. Since ℝ is ℝ, Lean
might assume it's wrt the Lebesgue measurable sets. In this case, we're
good. Of course we still need to find a lemma in mathlib that says that
the "counterimage of ∞ is measurable". Note that the lemma can't say
exactly that becuase φ takes values in ℝ and not in ENNReal (in which
case we might have had a chance).
In any case, if we don't find such lemma, I can easily produce it.
-/


/- ∀ `x ∈ A`, `Φ_{n+1}(x) - Φ_{n}(T(x)) = φ(x) - min(0,Φ_{n}(T(x))) ≥ φ(x)` decreases to `φ(x)`. -/

/-- Convenient combination of `birkhoffSum` terms. -/
theorem birkhoffSum_succ_image (n : ℕ) (x : α) :
      birkhoffSum T φ n (T x) = birkhoffSum T φ (n + 1) x - φ x := by
    simp [birkhoffSum_add T φ n 1 x, eq_add_of_sub_eq' (birkhoffSum_apply_sub_birkhoffSum T φ n x),
      birkhoffSum_one', add_sub (birkhoffSum T φ n x) (φ (T^[n] x)) (φ x)]

/- Would expect this to be in `Mathlib/Data/Finset/Lattice`.
Or perhaps there is already an easier way to extract it from mathlib? -/
theorem sup'_eq_iff_le {s : Finset β} [SemilatticeSup α] (H : s.Nonempty) (f : β → α) (hs : a ∈ s) :
    s.sup' H f = f a ↔ ∀ b ∈ s, f b ≤ f a := ⟨fun h0 b h2 ↦ (h0 ▸ Finset.le_sup' f h2),
    fun h1 ↦ (LE.le.ge_iff_eq (by simp [Finset.sup'_le_iff]; exact h1)).mp (Finset.le_sup' f hs)⟩

/- convenient because used several times in proving claim 1 -/
theorem map_range_Nonempty (n : ℕ) : (Finset.map (addLeftEmbedding 1)
    (Finset.range (n + 1))).Nonempty := by simp

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
  simp [min_eq_left h8, h1]

open Filter in
/-- Eventual equality - variant with assumption on `T x`. -/
theorem diff_evenutally_of_divSet' (x : α) (hx : (T x) ∈ divSet T φ ):
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
/-- Eventual equality - variant with assumption on `x`. -/
theorem diff_evenutally_of_divSet (x : α) (hx : x ∈ divSet T φ):
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
      have h2 := diff_evenutally_of_divSet' T φ x hx
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
      have h2 := diff_evenutally_of_divSet T φ x hx
      simp at h2
      obtain ⟨k, hk⟩ := h2
      use k
      intros n hn
      suffices hs : maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n = φ x by linarith
      exact hk n hn
      ------------------------------------------------------------------------------------------
    exact Tendsto.congr' h2' (tendsto_atTop_add_const_right atTop (- φ x) hx')

/-- Framed formula: the negative difference of maxOfSums is monotone. -/
theorem diff_Monotone (x : α) : Monotone (fun n ↦ -(maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n)) := by
  unfold Monotone
  intros n m hnm
  simp_rw [claim1]
  simp
  by_cases hc : 0 ≤ maxOfSums T φ (T x) m
  · left
    exact hc
  · right
    exact maxOfSums_Monotone T φ (T x) hnm

open Filter in
/-- ✨ Outside the divergent set the limsup of Birkhoff average is non positive. -/
theorem non_positive_of_notin_divSet (x : α) (hx : x ∉ divSet T φ) :
    limsup (fun n ↦ (birkhoffAverage R T φ n x)) ≤ 0 := by
  /- By `hx` we know that `n ↦ birkhoffSum T φ n x` is bounded. Conclude dividing by `n`. -/
  sorry

/-- `divSet T φ` is a measurable set -/
theorem divSet_MeasurableSet : MeasurableSet (divSet T φ) := by
  /- ? -/
  sorry

open Filter Topology Measure in
/-- The integral of an observable over the divergent set is nonnegative. -/
theorem integral_nonneg : 0 ≤ ∫ x in (divSet T φ), φ x ∂μ := by
  have h0 (n : ℕ) : 0 ≤ ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1) - maxOfSums T φ x n) ∂μ := by
    have hn : n ≤ (n + 1) := by simp
    have h01 : ∀ x ∈ divSet T φ, 0 ≤ (maxOfSums T φ x (n + 1) - maxOfSums T φ x n) := by
      intros x hx
      have h00 := maxOfSums_Monotone T φ x hn
      linarith
    exact setIntegral_nonneg (divSet_MeasurableSet T φ) h01
  have h1 (n : ℕ) : ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1) - maxOfSums T φ x n) ∂μ =
      ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n) ∂μ := by
    have h10 : ∫ x in (divSet T φ), (maxOfSums T φ x n) ∂μ =
        ∫ x in (divSet T φ), (maxOfSums T φ (T x) n) ∂μ := by
      /- Invariance using that divSet and μ are invariant
      with
        - `divSet_inv`
      -/
      sorry
    have h11 (n : ℕ) : Integrable (fun x ↦ maxOfSums T φ x n) (restrict μ (divSet T φ)) := by
      sorry
    have h12 (n : ℕ) : Integrable (fun x ↦ maxOfSums T φ (T x) n) (restrict μ (divSet T φ)) := by
      sorry
    rw [integral_sub (h11 (n + 1)) (h11 n), h10, ← integral_sub (h11 (n + 1)) (h12 n)]
  have h2 :
      Tendsto (fun n ↦ ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1)
      - maxOfSums T φ (T x) n) ∂μ) atTop (nhds (∫ x in (divSet T φ), φ x ∂μ)) := by
    /- Use monotone convergence theorem
      - `lintegral_iSup`
      - `lintegral_tendsto_of_tendsto_of_monotone`
      - `lintegral_iSup'`
    with
      - `diff_Monotone`
      - `diff_evenutally_of_divSet`
    -/
    sorry
  have h3 (n : ℕ) : 0 ≤ ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1)
      - maxOfSums T φ (T x) n) ∂μ := by
    calc 0 ≤ ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1) - maxOfSums T φ x n) ∂μ := h0 n
    _ = ∫ x in (divSet T φ), (maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n) ∂μ := h1 n
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds h2 h3


-- Sketch of the proof of the main theorem, for reference

/- `A` is in `I = inv_sigma_algebra`. -/
-- idea: is it better to define a new type measureable sets in alpha and then restrict to that type?
-- def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ T⁻¹' S = S }
-- def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ IsInvariant (fun n x ↦ T^[n] x) S }

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

/- If `T` is ergodic, show that the invariant sigma-algebra is a.e. trivial. -/

/- Show that the conditional expectation with respect to an a.e. trivial subalgebra is a.e.
the integral. -/

/- Birkhoff theorem for ergodic maps. -/

end Ergodic_Theory
