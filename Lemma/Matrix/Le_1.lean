import Mathlib
import sympy.Basic
import sympy.analysis.Misc.Probability
open ProbabilityTheory
open ProbabilityTheory.FinitelyAdditive


/--
[le_one](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Probability.lean)
-/
@[path]
private lemma main
  [BooleanAlgebra A] [BooleanAlgebra A']
  {P: FinitelyAdditive A}
  {P': FinitelyAdditive A'}
  {E:A} :
-- imply
  P E ≤ 1 :=
-- proof
  ProbabilityTheory.FinitelyAdditive.le_one P E


-- created on 2026-10-22
