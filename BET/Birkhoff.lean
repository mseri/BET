import Mathlib.Tactic
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle

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

/- standing assumptions: `f` is a measure preserving map of a probability space `(α, μ)`, and
`g : α → ℝ` is integrable. -/

variable {α : Type _} [MetricSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : MeasureTheory.Measure α} [IsProbabilityMeasure μ] {f : α → α}
  (hf : MeasurePreserving f μ) {g : α → ℝ} (hg : Integrable g μ)


/- Define Birkhoff sums. -/
noncomputable def birkhoffSum {α : Type _} (f : α → α) (g : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  1 / n * (∑ i in Finset.range n, g (f^[i] x))


/- Define the invariant sigma-algebra of `f` -/



/- Main lemma to prove Birkhoff ergodic theorem:
assume that the integral of `g` on any invariant set is strictly negative. Then, almost everywhere,
the Birkhoff sums `S_n g x` are bounded above.
-/


/- Deduce Birkhoff theorem from the main lemma, in the form that almost surely, `S_n f / n`
converges to the conditional expectation of `f` given the invariant sigma-algebra. -/


/- If `f` is ergodic, show that the invariant sigma-algebra is ae trivial -/


/- Show that the conditional expectation with respect to an ae trivial subalgebra is ae
the integral. -/


/- Give Birkhoff theorem for ergodic maps -/


end Ergodic_Theory
