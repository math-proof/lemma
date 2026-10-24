import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_1
open Chapter8
open Chapter8.Nat


/--
[Nat.atMostCountable_subset](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X: Set ℕ} :
-- imply
  AtMostCountable X :=
-- proof
  Chapter8.Nat.atMostCountable_subset X


-- created on 2026-10-22
