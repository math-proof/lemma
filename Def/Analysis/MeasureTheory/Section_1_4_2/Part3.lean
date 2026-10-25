import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Theorem.Analysis.MeasureTheory.Section_1_4_2.Part2


def LebesgueMeasurable.sigmaAlgebra (d:ℕ) : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
  (LebesgueMeasurable.boolean_algebra.isSigmaAlgebra d).toSigmaAlgebra

def IsNull.sigmaAlgebra (d:ℕ) : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
  (IsNull.boolean_algebra.isSigmaAlgebra d).toSigmaAlgebra

