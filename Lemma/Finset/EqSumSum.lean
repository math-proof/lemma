import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_7_1
open Finset


/--
[finite_series_refl](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {X: Finset XX}
  {Y: Finset YY}
  {f: XX × YY → ℝ} :
-- imply
  ∑ z ∈ X.product Y, f z = ∑ z ∈ Y.product X, f (z.2, z.1) :=
-- proof
  Finset.finite_series_refl X Y f


-- created on 2026-10-20
