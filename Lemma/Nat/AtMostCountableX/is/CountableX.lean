import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_1.Part4
open Chapter8
open Chapter8.AtMostCountable


/--
[AtMostCountable.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  AtMostCountable X ↔ Countable X :=
-- proof
  Chapter8.AtMostCountable.iff X


-- created on 2026-10-22
