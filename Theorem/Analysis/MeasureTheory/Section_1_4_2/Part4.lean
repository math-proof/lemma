module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
public import Instance.Analysis.MeasureTheory.Section_1_4_2.Part2


public section

theorem ConcreteSigmaAlgebra.generated_by_le {X:Type*} (F: Set (Set X)) : ConcreteBooleanAlgebra.generated_by F ≤ (ConcreteSigmaAlgebra.generated_by F).toConcreteBooleanAlgebra := by
  intro E hE B hB
  exact hE B.toConcreteBooleanAlgebra fun A hA => hB A hA

