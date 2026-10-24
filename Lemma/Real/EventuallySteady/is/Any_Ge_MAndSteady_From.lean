import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Real


/--
[Real.eventuallySteady_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {ε: ℝ}
  {a: Chapter6.Sequence} :
-- imply
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) :=
-- proof
  Real.eventuallySteady_def ε a


-- created on 2026-10-22
