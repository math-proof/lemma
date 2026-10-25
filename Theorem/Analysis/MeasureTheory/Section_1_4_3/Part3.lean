import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Class.Analysis.MeasureTheory.Section_1_4_3.Part2


/-- The analogue of {name}`FinitelyAdditiveMeasure.ext` for countably additive measures.  The
underlying finitely additive measure is an instance-implicit parent field, so it is enough to
know the two agree on every set. -/
@[ext] theorem CountablyAdditiveMeasure.ext {X:Type*} {B: ConcreteSigmaAlgebra X}
    {μ ν : CountablyAdditiveMeasure B} (h : ∀ A, μ.measure A = ν.measure A) : μ = ν := by
  have hf : μ.toFinitelyAdditiveMeasure = ν.toFinitelyAdditiveMeasure :=
    FinitelyAdditiveMeasure.ext h
  cases μ with | mk hcount =>
  cases ν with | mk hcount' =>
  subst hf
  rfl

