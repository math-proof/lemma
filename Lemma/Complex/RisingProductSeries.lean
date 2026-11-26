import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Topology.Algebra.InfiniteSum.RisingProductSeries
open Complex


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
    (-b) ^ j * x ^ (j + 1) / ∏ r < j + 1, (c + b * ((r + 1 : ℕ) : ℂ))) := by
-- proof
  simpa only [Nat.Iio_eq_range] using summable_neg_pow_mul_pow_div_prod_add_mul x hc


-- created on 2026-10-11
-- updated on 2026-11-26
