import Mathlib

noncomputable section

open MeasureTheory

variable {α : Type*} [m0: MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable (T : α → α) (hT : Measurable T)
variable {f : α → ℝ} (hf : Integrable f μ)

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
