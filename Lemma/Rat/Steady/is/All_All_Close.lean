import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_1
open Rat


/--
[Rat.steady_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {ε: ℚ}
  {a: Chapter5.Sequence} :
-- imply
  ε.Steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m) :=
-- proof
  Rat.steady_def ε a


-- created on 2026-10-22
