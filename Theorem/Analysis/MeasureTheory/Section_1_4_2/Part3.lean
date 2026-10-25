import Mathlib.SetTheory.Cardinal.Aleph
import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
import Def.Analysis.MeasureTheory.Section_1_4_2.Part3


/-- Exercise 1.4.12 -/
theorem ConcreteSigmaAlgebra.restrict_is_sigma {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X): (B.restrict A).isSigmaAlgebra := by
  classical
  intro E hE
  choose E' hmeas heq using hE
  refine ⟨⋃ n, E' n, B.countable_union_mem E' hmeas, ?_⟩
  ext x
  simp [heq]

