import Mathlib

noncomputable section
open MeasureTheory

variable {α : Type*} [m0: MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {T : α → α} (hT : Measurable T)
variable {f : α → ℝ} (hf : Integrable f μ)

lemma my_count_union (A B: ℕ → Set α) (h : ∀ i, A i = B i) : ⋃ i, A i = ⋃ i, B i := by sorry
-- the above MUST be in mathlib, but I couldn't find it!

def invSigmaAlg (hT : Measurable T) : MeasurableSpace α where
  MeasurableSet' s := MeasurableSet s ∧ T ⁻¹' s = s
  measurableSet_empty := by
    constructor
    · exact MeasurableSet.empty
    · exact rfl
  measurableSet_compl := by
    intro s
    dsimp
    intro hinit -- the lest 3 lines can be abbreviated to: 'intro h hinit'
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
    · have hi2nd : ∀ i, T ⁻¹'(s i) = s i := by sorry
      rw [Set.preimage_iUnion]
      exact my_count_union (fun i ↦ T ⁻¹' s i) (fun i ↦ s i) hi2nd
