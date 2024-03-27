noncomputable section
open MeasureTheory

variable {α : Type*} [m0: MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {T : α → α} (hT : Measurable T)
variable {f : α → ℝ} (hf : Integrable f μ)

def invSigmaAlg (hT : Measurable T) : MeasurableSpace α where
  MeasurableSet' s := MeasurableSet s ∧ T ⁻¹' s = s
  measurableSet_empty := by
    constructor
    · exact MeasurableSet.empty
    · exact rfl
  measurableSet_compl := by
    intro s
    dsimp
    intro hinit -- the lest 3 line can be abbreviated to: 'intro h hinit'
    obtain ⟨hinit1, hinti2⟩ := hinit
    constructor
    · exact MeasurableSet.compl hinit1
    · rw [Set.preimage_compl]
      exact congrArg compl hinti2
  measurableSet_iUnion := by
    intro seq
    dsimp
    sorry
