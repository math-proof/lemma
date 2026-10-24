import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_4_2
open ConcreteSigmaAlgebra


/--
[ConcreteSigmaAlgebra.generated_by_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_2.lean)
-/
@[path]
private lemma main
  {F: Set (Set X)} :
-- imply
  ConcreteBooleanAlgebra.generated_by F ≤ (ConcreteSigmaAlgebra.generated_by F).toConcreteBooleanAlgebra :=
-- proof
  ConcreteSigmaAlgebra.generated_by_le F


-- created on 2026-10-22
