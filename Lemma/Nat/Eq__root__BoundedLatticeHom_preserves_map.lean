import Mathlib
import sympy.Basic
import sympy.analysis.Misc.Probability
open ProbabilityTheory
open ProbabilityTheory.FinitelyAdditive
open BoundedLatticeHom


/--
[_root_.BoundedLatticeHom.preserves.map](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Probability.lean)
-/
@[path]
private lemma main
  [BooleanAlgebra A] [BooleanAlgebra A']
  {P: FinitelyAdditive A}
  {P': FinitelyAdditive A'}
  {f: BoundedLatticeHom A A'}
  {E:A}
-- given
  (hf: f.preserves P P') :
-- imply
  P' (f E) = P E :=
-- proof
  BoundedLatticeHom.preserves.map P P' hf E


-- created on 2026-10-22
