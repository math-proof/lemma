import Mathlib
import sympy.Basic
import Def.Analysis.Misc.Probability.Part2
open ProbabilityTheory
open ProbabilityTheory.FinitelyAdditive


/--
[top](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Probability.lean)
-/
@[path]
private lemma main
  [BooleanAlgebra A] [BooleanAlgebra A']
  {P: FinitelyAdditive A}
  {P': FinitelyAdditive A'} :
-- imply
  P ⊤ = 1 :=
-- proof
  ProbabilityTheory.FinitelyAdditive.top P


-- created on 2026-10-22
