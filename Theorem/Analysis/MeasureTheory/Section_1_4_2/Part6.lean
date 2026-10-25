import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Def.Analysis.MeasureTheory.Section_1_4_2.Part7


theorem BorelSigmaAlgebra.le_LebesgueSigmaAlgebra (d:ℕ) : BorelSigmaAlgebra (EuclideanSpace' d) ≤ LebesgueMeasurable.sigmaAlgebra d := by
  intro E hE
  exact hE (LebesgueMeasurable.sigmaAlgebra d) fun U hU => IsOpen.measurable hU

