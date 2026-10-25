import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Class.Analysis.MeasureTheory.Section_1_4_3


/-- Two finitely additive measures on the same algebra are equal as soon as they assign the same
value to every set; the other fields are propositions, so proof irrelevance disposes of them.
Tagged so that the `ext` tactic applies to these measures. -/
@[ext] theorem FinitelyAdditiveMeasure.ext {X:Type*} {B: ConcreteBooleanAlgebra X}
    {μ ν : FinitelyAdditiveMeasure B} (h : ∀ A, μ.measure A = ν.measure A) : μ = ν := by
  cases μ with | mk m hpos hempty hadd =>
  cases ν with | mk m' hpos' hempty' hadd' =>
  have hm : m = m' := funext h
  subst hm
  rfl

