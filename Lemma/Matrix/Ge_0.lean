import Mathlib
import sympy.Basic
import sympy.analysis.Misc.Probability
open ProbabilityTheory
open ProbabilityTheory.FinitelyAdditive


/--
[nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Probability.lean)
-/
@[path]
private lemma main
  [BooleanAlgebra A] [BooleanAlgebra A']
  {P: FinitelyAdditive A}
  {P': FinitelyAdditive A'}
  {E:A} :
-- imply
  0 ≤ P E :=
-- proof
  ProbabilityTheory.FinitelyAdditive.nonneg P E


-- created on 2026-10-22
