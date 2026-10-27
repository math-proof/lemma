import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Section_1_4_2.Part8


/--
[ConcreteSigmaAlgebra.isSigmaAlgebra](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_2.lean)
-/
@[path]
private lemma main
  {B: ConcreteSigmaAlgebra X} :
-- imply
  ConcreteBooleanAlgebra.isSigmaAlgebra B.toConcreteBooleanAlgebra :=
-- proof
  ConcreteSigmaAlgebra.isSigmaAlgebra B


-- created on 2026-10-22
