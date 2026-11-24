module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
public import Class.Analysis.MeasureTheory.Section_1_4_2


public section

def ConcreteBooleanAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteBooleanAlgebra X) : Prop :=
  ∀ E : ℕ → Set X, (∀ n, B.measurable (E n)) → B.measurable (⋃ n, E n)

