module
public import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
public import Theorem.Analysis.Misc.NatBitwise
public import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part9


public section

/-- Definition 1.3.6 (Absolutely convergent simple integral, real) -/
def RealSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : Prop :=
  (hf.abs).integ < ⊤

/-- Definition 1.3.6 (Absolutely convergent simple integral, complex) -/
def ComplexSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : Prop :=
  (hf.abs).integ < ⊤

