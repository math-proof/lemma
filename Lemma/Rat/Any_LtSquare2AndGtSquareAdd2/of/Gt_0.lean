import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_4
open Rat


/--
[Rat.exist_approx_sqrt_two](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_4.lean)
-/
@[path]
private lemma main
  {ε:ℚ}
-- given
  (hε:ε>0) :
-- imply
  ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 :=
-- proof
  Rat.exist_approx_sqrt_two hε


-- created on 2026-10-22
