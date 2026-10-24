import Mathlib
import sympy.Basic
import sympy.analysis.Misc.Probability
open ProbabilityTheory
open ProbabilityTheory.FinitelyAdditive


/--
[sup_add_inf](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Probability.lean)
-/
@[path]
private lemma main
  [BooleanAlgebra A] [BooleanAlgebra A']
  {P: FinitelyAdditive A}
  {P': FinitelyAdditive A'}
  {E F:A} :
-- imply
  P (E ⊔ F) + P (E ⊓ F) = P E + P F :=
-- proof
  ProbabilityTheory.FinitelyAdditive.sup_add_inf P E F


-- created on 2026-10-22
