import Mathlib.Order.BooleanAlgebra.Defs
import Def.Analysis.MeasureTheory.Section_1_3_5.Part3
import Structure.Analysis.MeasureTheory.Section_1_4_1


instance ConcreteBooleanAlgebra.instLE (X:Type*) : LE (ConcreteBooleanAlgebra X) :=
  ⟨fun B1 B2 => ∀ E, B1.measurable E → B2.measurable E⟩

instance ConcreteBooleanAlgebra.instPartialOrder (X:Type*) : PartialOrder (ConcreteBooleanAlgebra X) :=
  {
    le_refl := fun B E hE => hE
    le_trans := fun A B C hAB hBC E hE => hBC E (hAB E hE)
    le_antisymm := by
      intro A B hAB hBA
      have : A.measurable = B.measurable := by
        ext E
        exact ⟨hAB E, hBA E⟩
      cases A
      cases B
      congr
  }

