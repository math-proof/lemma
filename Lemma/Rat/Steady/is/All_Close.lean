import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_1.Part9
open Chapter5
open Chapter5.Rat
open Chapter5.Rat.Steady


/--
[Rat.Steady.coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {ε : ℚ}
  {a:ℕ → ℚ} :
-- imply
  ε.Steady a ↔ ∀ n m : ℕ, ε.Close (a n) (a m) :=
-- proof
  Chapter5.Rat.Steady.coe ε a


-- created on 2026-10-22
