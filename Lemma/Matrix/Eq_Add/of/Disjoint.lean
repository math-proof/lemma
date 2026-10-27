import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.Misc.Probability.Part2
open ProbabilityTheory
open ProbabilityTheory.FinitelyAdditive


/--
[disj_sup](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Probability.lean)
-/
@[path]
private lemma main
  [BooleanAlgebra A] [BooleanAlgebra A']
  {P: FinitelyAdditive A}
  {P': FinitelyAdditive A'}
  {E F:A}
-- given
  (hEF: Disjoint E F) :
-- imply
  P (E ⊔ F) = P E + P F :=
-- proof
  ProbabilityTheory.FinitelyAdditive.disj_sup P hEF


-- created on 2026-10-22
