import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_1
open Chapter5


/--
[boundedBy_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {n:ℕ}
  {a: Fin n → ℚ}
  {M:ℚ} :
-- imply
  BoundedBy a M ↔ ∀ i, |a i| ≤ M :=
-- proof
  Chapter5.boundedBy_def a M


-- created on 2026-10-20
