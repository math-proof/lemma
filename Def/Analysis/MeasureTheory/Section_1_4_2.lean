import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Class.Analysis.MeasureTheory.Section_1_4_2


def ConcreteBooleanAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteBooleanAlgebra X) : Prop :=
  ∀ E : ℕ → Set X, (∀ n, B.measurable (E n)) → B.measurable (⋃ n, E n)

