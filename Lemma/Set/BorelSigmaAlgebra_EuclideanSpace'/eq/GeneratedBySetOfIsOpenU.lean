import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_4_2
open BorelSigmaAlgebra


/--
[BorelSigmaAlgebra.generated_by_open](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_2.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  BorelSigmaAlgebra (EuclideanSpace' d) = ConcreteSigmaAlgebra.generated_by { U : Set (EuclideanSpace' d) | IsOpen U } :=
-- proof
  BorelSigmaAlgebra.generated_by_open d


-- created on 2026-10-22
