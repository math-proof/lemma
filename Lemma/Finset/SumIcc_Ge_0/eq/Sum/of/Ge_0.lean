import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_4
open Chapter7
open Chapter7.Series


/--
[Series.sum_eq_sum](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_4.lean)
-/
@[path]
private lemma main
  {b:ℕ → ℝ}
  {N:ℤ}
-- given
  (hN: N ≥ 0) :
-- imply
  ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n :=
-- proof
  Chapter7.Series.sum_eq_sum b hN


-- created on 2026-10-22
