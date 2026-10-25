import Mathlib.Order.BooleanAlgebra.Defs
import Def.Analysis.MeasureTheory.Section_1_3_5.Part3
import Def.Analysis.MeasureTheory.Section_1_4_1


/-- Example 1.4.3 (the largest algebra) -/
instance ConcreteBooleanAlgebra.instOrderTop {X:Type*} : OrderTop (ConcreteBooleanAlgebra X) :=
  {
    top := {
      measurable := fun _ => True
      empty_mem := trivial
      compl_mem := fun _ _ => trivial
      union_mem := fun _ _ _ _ => trivial
    }
    le_top := fun _ _ _ => trivial
  }

/-- Example 1.4.3 (the smallest algebra) -/
instance ConcreteBooleanAlgebra.instOrderBot {X:Type*} : OrderBot (ConcreteBooleanAlgebra X) :=
  {
    bot := {
      measurable := fun E => E = ∅ ∨ E = Set.univ
      empty_mem := by grind
      compl_mem := fun E hE => by grind
      union_mem := fun E F hE hF => by grind
    }
    bot_le := fun B E hE => by
      rcases hE with h | h
      · simpa [h] using B.empty_mem
      · simpa [h, Set.compl_empty] using B.compl_mem ∅ B.empty_mem
  }

