import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Section_1_4_3.Part5
open FinitelyAdditiveMeasure


/--
[FinitelyAdditiveMeasure.mono](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_3.lean)
-/
@[path]
private lemma main
  {B: ConcreteBooleanAlgebra X}
  {μ: FinitelyAdditiveMeasure B}
  {E F : Set X}
-- given
  (hE : B.measurable E)
  (hF : B.measurable F)
  (hsub : E ⊆ F) :
-- imply
  μ.measure E ≤ μ.measure F :=
-- proof
  FinitelyAdditiveMeasure.mono μ hE hF hsub


-- created on 2026-10-22
