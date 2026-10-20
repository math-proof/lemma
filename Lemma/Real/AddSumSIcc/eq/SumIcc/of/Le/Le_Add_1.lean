import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[concat_finite_series](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {m n p:ℤ}
  {a: ℤ → ℝ}
-- given
  (hmn: m ≤ n+1)
  (hpn : n ≤ p) :
-- imply
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i :=
-- proof
  Finset.concat_finite_series hmn hpn a


-- created on 2026-10-20
