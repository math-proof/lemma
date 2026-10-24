import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[tsum_geometric_inflate](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {δ : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  ∑' n : ℕ, δ / 2^(n+2) = δ / 2 :=
-- proof
  tsum_geometric_inflate hδ


-- created on 2026-10-22
