import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Instance.Analysis.MeasureTheory.Section_1_4_2.Part2


theorem ConcreteSigmaAlgebra.generated_by_le {X:Type*} (F: Set (Set X)) : ConcreteBooleanAlgebra.generated_by F ≤ (ConcreteSigmaAlgebra.generated_by F).toConcreteBooleanAlgebra := by
  intro E hE B hB
  exact hE B.toConcreteBooleanAlgebra fun A hA => hB A hA

