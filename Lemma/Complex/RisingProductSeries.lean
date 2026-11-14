import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Topology.Algebra.InfiniteSum.RisingProductSeries


namespace Complex

/--
[RisingProductSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecificLimits/RisingProductSeries.lean)
-/
@[path]
private lemma summable_neg_pow_mul_pow_div_prod_add_mul_eq
-- given
  (b c : ℂ)
  (hc : ∀ r : ℕ, c + b * ((r + 1 : ℕ) : ℂ) ≠ 0)
  (x : ℂ) :
-- imply
  Summable (fun j : ℕ =>
    (-b) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1), (c + b * ((r + 1 : ℕ) : ℂ))) :=
-- proof
  summable_neg_pow_mul_pow_div_prod_add_mul x hc

end Complex


-- created on 2026-10-11
-- updated on 2026-10-26
