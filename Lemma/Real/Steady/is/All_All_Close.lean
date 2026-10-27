import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Real


/--
[Real.steady_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {ε: ℝ}
  {a: Chapter6.Sequence} :
-- imply
  ε.Steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m) :=
-- proof
  Real.steady_def ε a


-- created on 2026-10-22
