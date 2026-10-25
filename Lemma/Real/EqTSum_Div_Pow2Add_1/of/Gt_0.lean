import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[tsum_geometric_eps](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  ∑' n : ℕ, ε / 2^(n+1) = ε :=
-- proof
  tsum_geometric_eps ε hε


-- created on 2026-10-22
