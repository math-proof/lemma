import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[α_length_of_pt](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {α: ℝ → ℝ}
  {a:ℝ} :
-- imply
  α[Icc a a]ₗ = jump α a :=
-- proof
  Chapter11.α_length_of_pt a


-- created on 2026-10-22
