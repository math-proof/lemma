/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean -/


import Def.NumberTheory.LSeries.AbelContinuation
import Lemma.Nat.LSeries.AbelContinuation
import Def.MathlibExtTest.NumberTheory.LSeries.AbelContinuation
/-!
# Tests for the Abel continuation

Zero, one-point finite-support, and alternating examples: each has `O(n ^ 0)`
partial sums, so the continuation is holomorphic on `0 < s.re` and ordered
Dirichlet partial sums converge to it there with no summability assumed.
The alternating example additionally exercises absolute `LSeriesSummable`
at `1 < s.re` and agreement of the continuation with `LSeries` there. Every
`LSeriesSummable` check below is absolute summability; no conditional
convergence is claimed.
-/


namespace AbelContinuationTest

open Filter Asymptotics Topology

-- The alternating series is absolutely summable at `1 < s.re`.
-- (`LSeriesSummable` is absolute summability throughout; no conditional
-- convergence is claimed here.)
example {s : ℂ} (hs : (1 : ℝ) < s.re) : LSeriesSummable alt s :=
  LSeriesSummable_of_isBigO_rpow hs alt_pointwise_isBigO

-- Pointwise differentiability for the alternating sequence.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    DifferentiableAt ℂ (abelContinuation alt) s :=
  differentiableAt_abelContinuation _ hs alt_isBigO

-- Agreement with `LSeries` for the alternating sequence at `1 < s.re`.
example {s : ℂ} (hs : (1 : ℝ) < s.re) :
    abelContinuation alt s = LSeries alt s :=
  abelContinuation_eq_LSeries _ le_rfl (zero_lt_one.trans hs)
    (LSeriesSummable_of_isBigO_rpow hs alt_pointwise_isBigO) alt_isBigO

-- Ordered partial sums converge to the continuation for the alternating
-- sequence on `0 < s.re`, with no summability assumed.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, LSeries.term alt s n) atTop
      (𝓝 (abelContinuation alt s)) :=
  tendsto_abelContinuation_Icc _ hs alt_isBigO

end AbelContinuationTest
