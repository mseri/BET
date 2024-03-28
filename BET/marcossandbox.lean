import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

noncomputable section
open MeasureTheory

variable {α : Type*} [m0: MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {T : α → α} (hT: Measurable T)
-- variable (hT : Measurable T)
variable {f φ : α → ℝ}

def invSigmaAlg_test (hT : Measurable T) : MeasurableSpace α where
  MeasurableSet' := fun s ↦ MeasurableSet s ∧ T ⁻¹' s = s
  measurableSet_empty := by
    constructor
    · exact MeasurableSet.empty
    · exact rfl
  measurableSet_compl := sorry
  measurableSet_iUnion := sorry

lemma invSigmaAlg_le : invSigmaAlg hT ≤ m0 := sorry

lemma my_lemma2 (s : Set α) (hs : MeasurableSet s) :
  MeasurableSet sᶜ := MeasurableSet.compl hs -- also 'hs.compl'

lemma my_lemma (s : Set α) (hs : MeasurableSet[invSigmaAlg hT] s) :
  MeasurableSet[invSigmaAlg hT] sᶜ := MeasurableSet.compl hs -- also 'hs.compl'

example : α → ℝ := condexp (invSigmaAlg hT) μ f

end

--- my sandbox

section

variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  . right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

end


noncomputable section
open MeasureTheory

variable {α : Type*} [m0: MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable (T : α → α) (hT : Measurable T)
variable {f : α → ℝ} (hf : Integrable f μ)


/- when calling the definition below, T will be an explicit argument, because we made
T an explicit variable (and we couldn't do otherwise, Floris explained) and becauae we
used T in the construction of the definition -/
def invSigmaAlg : MeasurableSpace α where
  MeasurableSet' := fun s ↦ MeasurableSet s ∧ T ⁻¹' s = s
  -- also 'MeasurableSet' s := MeasurableSet s ∧ T ⁻¹' s = s'
  measurableSet_empty := by
    constructor
    · exact MeasurableSet.empty
    · exact rfl
  measurableSet_compl := by
    intro s
    dsimp only -- problems at least with infoview on this part
    intro hinit -- the last 3 lines can be abbreviated to: 'intro h hinit'
    obtain ⟨hinit1, hinit2⟩ := hinit
    constructor
    · exact MeasurableSet.compl hinit1
    · exact congrArg compl hinit2 -- this was suggested by Lean
  measurableSet_iUnion := by
    intro s
    dsimp
    intro hinit
    constructor
    · have hi1st : ∀ i, MeasurableSet (s i) := by
        intro i
        exact (hinit i).left
      exact MeasurableSet.iUnion hi1st
    · have hi2nd : ∀ i, T ⁻¹'(s i) = s i := by
        intro i
        exact (hinit i).right
      rw [Set.preimage_iUnion]
      exact Set.iUnion_congr hi2nd
    done

#check iUnion_congr

/- the lemma below was a problem because it was hard to find out what m ≤ m0 meant, when
m, m0 are measurable spaces. Hovering over the ≤ sign in infoview and following links
explained it:
instance : LE (MeasurableSpace α) where le m₁ m₂ := ∀ s, MeasurableSet[m₁] s → MeasurableSet[m₂] s
-/
lemma leq_InvSigmaAlg_FullAlg : invSigmaAlg T ≤ m0 := by
  intro s hs -- here the infoview is faulty and doesn't show everything (known Lean problem, Floris says)
  exact hs.left
  done


------------------------------------- OLD STUFF DOWN HERE

/- the following is an earlier version before I realized we never needed that T is
measurable for this definition -/
def invSigmaAlg_previous (hT : Measurable T) : MeasurableSpace α where
  MeasurableSet' := fun s ↦ MeasurableSet s ∧ T ⁻¹' s = s
  -- also 'MeasurableSet' s := MeasurableSet s ∧ T ⁻¹' s = s'
  measurableSet_empty := by
    constructor
    · exact MeasurableSet.empty
    · exact rfl
  measurableSet_compl := by
    intro s
    dsimp
    intro hinit -- the last 3 lines can be abbreviated to: 'intro h hinit'
    obtain ⟨hinit1, hinit2⟩ := hinit
    constructor
    · exact MeasurableSet.compl hinit1
    · exact congrArg compl hinit2 -- this was suggested by Lean
      -- problems at least with infoview on this part
  measurableSet_iUnion := by
    intro s
    dsimp
    intro hinit
    constructor
    · have hi1st : ∀ i, MeasurableSet (s i) := by
        intro i
        exact (hinit i).left
      exact MeasurableSet.iUnion hi1st
    · have hi2nd : ∀ i, T ⁻¹'(s i) = s i := by
        intro i
        exact (hinit i).right
      rw [Set.preimage_iUnion]
      exact my_count_union (fun i ↦ T ⁻¹' s i) (fun i ↦ s i) hi2nd
    done

-- the lemma below MUST be in mathlib, but I couldn't find it!
lemma my_count_union (A B: ℕ → Set α) (h : ∀ i, A i = B i) : ⋃ i, A i = ⋃ i, B i := by
  ext x
  simp
  constructor
  · intro hyp
    obtain ⟨i, hypa⟩ := hyp
    use i
    rw [← h]
    exact hypa
  · intro hyp
    obtain ⟨i, hypb⟩ := hyp
    use i
    rw [h]
    exact hypb
  done
