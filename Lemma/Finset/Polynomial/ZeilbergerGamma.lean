import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Polynomial.ZeilbergerGamma
open scoped BigOperators
open MetaMathlibExt


/--
[zeilberger_gamma_coefficient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Polynomial/ZeilbergerGamma.lean)
-/
@[path]
private lemma zeilberger_gamma_coefficient_eq
  {n k : ℕ}
  {gamma : ℕ → ℚ}
-- given
  (h : Polynomial ℚ)
  (hk : k ≤ n / 2)
  (hgamma : h = ∑ j ∈ Finset.range (n / 2 + 1), Polynomial.C (gamma j) * Polynomial.X ^ j * (1 + Polynomial.X) ^ (n - 2 * j)) :
-- imply
  let C : PowerSeries ℚ := by
-- proof
  apply MetaMathlibExt.zeilberger_gamma_coefficient n k h gamma hk hgamma


-- created on 2026-10-20
