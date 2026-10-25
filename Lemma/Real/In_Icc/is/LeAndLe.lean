import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.mem_Icc](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {x y z:Chapter5.Real} :
-- imply
  z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y :=
-- proof
  Chapter5.Real.mem_Icc x y z


-- created on 2026-10-22
