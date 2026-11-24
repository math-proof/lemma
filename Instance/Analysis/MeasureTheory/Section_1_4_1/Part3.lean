module
public import Mathlib.Order.BooleanAlgebra.Defs
public import Def.Analysis.MeasureTheory.Section_1_3_5.Part3
public import Def.Analysis.MeasureTheory.Section_1_4_1.Part2


public section

/-- Exercise 1.4.6 (Intersection of algebras) -/
instance ConcreteBooleanAlgebra.instInfSet {X:Type*} : InfSet (ConcreteBooleanAlgebra X) :=
  {
      sInf S :=
        {
          measurable := fun E => ∀ B ∈ S, B.measurable E
          empty_mem := fun B _ => B.empty_mem
          compl_mem := fun E hE B hB => B.compl_mem E (hE B hB)
          union_mem := fun E F hE hF B hB => B.union_mem E F (hE B hB) (hF B hB)
        }
  }

