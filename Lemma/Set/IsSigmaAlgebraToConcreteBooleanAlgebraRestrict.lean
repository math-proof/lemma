import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Section_1_4_2.Part8


/--
[ConcreteSigmaAlgebra.restrict_is_sigma](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_2.lean)
-/
@[path]
private lemma main
  {B: ConcreteSigmaAlgebra X}
  {A:Set X} :
-- imply
  ConcreteBooleanAlgebra.isSigmaAlgebra (B.restrict A).toConcreteBooleanAlgebra :=
-- proof
  ConcreteSigmaAlgebra.restrict_is_sigma B A


-- created on 2026-10-22
