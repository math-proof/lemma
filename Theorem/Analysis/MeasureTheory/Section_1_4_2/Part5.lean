module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
public import Def.Analysis.MeasureTheory.Section_1_4_2.Part6


public section

/-- Exercise 1.4.14 (i) -/
theorem BorelSigmaAlgebra.generated_by_open (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { U : Set (EuclideanSpace' d) | IsOpen U } := rfl

