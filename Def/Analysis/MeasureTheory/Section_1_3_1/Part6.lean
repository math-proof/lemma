module
public import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
public import Theorem.Analysis.Misc.NatBitwise
public import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part5


public section

namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-- The weighted measure sum for a representation -/
noncomputable def weightedMeasureSum {d k : ℕ} (c : Fin k → EReal) (E : Fin k → Set (EuclideanSpace' d)) : EReal :=
  ∑ i, (c i) * Lebesgue_measure (E i)

end UnsignedSimpleFunction.IntegralWellDef
