import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_4_3
open FinitelyAdditiveMeasure


/--
[FinitelyAdditiveMeasure.finite_additivity](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_3.lean)
-/
@[path]
private lemma main
  {B: ConcreteBooleanAlgebra X}
  {μ: FinitelyAdditiveMeasure B}
  {I: Finset J}
  {E: J → Set X}
-- given
  (hE: ∀ j:J, B.measurable (E j))
  (hdisj: Set.univ.PairwiseDisjoint E) :
-- imply
  μ.measure (⋃ j ∈ I, E j) = ∑ j ∈ I, μ.measure (E j) :=
-- proof
  FinitelyAdditiveMeasure.finite_additivity μ hE hdisj


-- created on 2026-10-22
