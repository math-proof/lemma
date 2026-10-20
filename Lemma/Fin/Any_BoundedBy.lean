import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_1
open Chapter5


/--
[finite](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {n:ℕ}
  {a: Fin n → ℚ} :
-- imply
  ∃ M ≥ 0,  BoundedBy a M :=
-- proof
  Chapter5.IsBounded.finite a


-- created on 2026-10-20
