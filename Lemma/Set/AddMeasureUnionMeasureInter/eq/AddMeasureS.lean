import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_4_3
open FinitelyAdditiveMeasure


/--
[FinitelyAdditiveMeasure.mes_union_add_mes_inter](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_3.lean)
-/
@[path]
private lemma main
  {B: ConcreteBooleanAlgebra X}
  {μ: FinitelyAdditiveMeasure B}
  {E F : Set X}
-- given
  (hE: B.measurable E)
  (hF: B.measurable F) :
-- imply
  μ.measure (E ∪ F) + μ.measure (E ∩ F) = μ.measure E + μ.measure F :=
-- proof
  FinitelyAdditiveMeasure.mes_union_add_mes_inter μ hE hF


-- created on 2026-10-22
