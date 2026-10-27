import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.Misc.Probability.Part2
open ProbabilityTheory
open ProbabilityTheory.FinitelyAdditive


/--
[bot](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Probability.lean)
-/
@[path]
private lemma main
  [BooleanAlgebra A] [BooleanAlgebra A']
  {P: FinitelyAdditive A}
  {P': FinitelyAdditive A'} :
-- imply
  P ⊥ = 0 :=
-- proof
  ProbabilityTheory.FinitelyAdditive.bot P


-- created on 2026-10-22
