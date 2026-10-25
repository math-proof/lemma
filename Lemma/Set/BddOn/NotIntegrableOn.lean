import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_11_7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[not_integrable](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_7.lean)
-/
@[path]
private lemma main
  :
-- imply
  BddOn f_9_3_21 (Icc 0 1) ∧ ¬ IntegrableOn f_9_3_21 (Icc 0 1) :=
-- proof
  Chapter11.not_integrable


-- created on 2026-10-22
