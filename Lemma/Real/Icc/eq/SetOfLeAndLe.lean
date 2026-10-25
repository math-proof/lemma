import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.Icc_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {x y:Chapter5.Real} :
-- imply
  .Icc x y = { z | x ≤ z ∧ z ≤ y } :=
-- proof
  Chapter5.Real.Icc_def x y


-- created on 2026-10-22
