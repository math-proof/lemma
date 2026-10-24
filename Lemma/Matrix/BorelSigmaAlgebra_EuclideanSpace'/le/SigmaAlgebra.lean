import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_4_2
open BorelSigmaAlgebra


/--
[BorelSigmaAlgebra.le_LebesgueSigmaAlgebra](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_2.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  BorelSigmaAlgebra (EuclideanSpace' d) ≤ LebesgueMeasurable.sigmaAlgebra d :=
-- proof
  BorelSigmaAlgebra.le_LebesgueSigmaAlgebra d


-- created on 2026-10-22
