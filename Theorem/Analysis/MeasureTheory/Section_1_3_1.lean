module
public import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
public import Theorem.Analysis.Misc.NatBitwise
public import Def.Analysis.MeasureTheory.Section_1_3_1


public section

theorem EReal.indicator_of_mem {X:Type*} {A: Set X} {x:X} (h: x ∈ A) : EReal.indicator A x = 1 := by
  simp [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem h]

theorem EReal.indicator_of_notMem {X:Type*} {A: Set X} {x:X} (h: x ∉ A) : EReal.indicator A x = 0 := by
  simp [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem h]

theorem EReal.indicator_eq_comp {X:Type*} (A: Set X) : EReal.indicator A = Real.toEReal ∘ A.indicator' := rfl

