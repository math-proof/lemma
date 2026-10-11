import Mathlib
import sympy.Basic
import sympy.series.CentralBinomPowerSum

open MetaMathlibExt

/--
[CentralBinomPowerSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Series/CentralBinomPowerSum.lean)
-/
@[path]
private lemma central_binom_power_sum_stirling_eq
-- given
  (m : ℕ)
  (x : ℝ)
  (hx : |x| < 1 / 4) :
-- imply
  ∑' n : ℕ, (Nat.centralBinom n : ℝ) * (n : ℝ) ^ m * x ^ n =
    1 / Real.sqrt (1 - 4 * x) *
      ∑ k ∈ Finset.range (m + 1),
        (Nat.stirlingSecond m k : ℝ) * (Nat.centralBinom k : ℝ) *
          (Nat.factorial k : ℝ) * (x / (1 - 4 * x)) ^ k := by
-- proof
  apply MetaMathlibExt.central_binom_power_sum_stirling m x hx

-- created on 2026-10-10
