/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean -/


import sympy.atlas.NumberTheory.LSeries.AbelContinuation
import Lemma.Nat.LSeries.AbelContinuation


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

-- The continuation of the zero sequence vanishes.
example (s : ℂ) : abelContinuation (fun _ => (0 : ℂ)) s = 0 := by
  simp [abelContinuation, abelSummatory, abelPartialSum]

-- Pointwise differentiability for the zero sequence.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    DifferentiableAt ℂ (abelContinuation (fun _ => (0 : ℂ))) s :=
  differentiableAt_abelContinuation _ hs zero_isBigO

-- Set-level analyticity for the zero sequence.
example : AnalyticOn ℂ (abelContinuation (fun _ => (0 : ℂ))) {s | (0 : ℝ) < s.re} :=
  analyticOn_abelContinuation _ zero_isBigO

-- Agreement with `LSeries` for the zero sequence.
example {s : ℂ} (hs : (0 : ℝ) < s.re) (hS : LSeriesSummable (fun _ => (0 : ℂ)) s) :
    abelContinuation (fun _ => (0 : ℂ)) s = LSeries (fun _ => (0 : ℂ)) s :=
  abelContinuation_eq_LSeries _ le_rfl hs hS zero_isBigO

-- Ordered partial sums converge for the zero sequence, with no summability.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, LSeries.term (fun _ => (0 : ℂ)) s n)
      atTop (𝓝 (abelContinuation (fun _ => (0 : ℂ)) s)) :=
  tendsto_abelContinuation_Icc _ hs zero_isBigO

-- Pointwise differentiability for the single-point sequence.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    DifferentiableAt ℂ
      (abelContinuation (fun n => if n = 1 then (1 : ℂ) else 0)) s :=
  differentiableAt_abelContinuation _ hs single_isBigO

-- Set-level analyticity for the single-point sequence.
example : AnalyticOn ℂ
    (abelContinuation (fun n => if n = 1 then (1 : ℂ) else 0))
    {s | (0 : ℝ) < s.re} :=
  analyticOn_abelContinuation _ single_isBigO

-- Ordered partial sums converge for the single-point sequence, with no
-- summability assumed.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N,
      LSeries.term (fun n => if n = 1 then (1 : ℂ) else 0) s n)
      atTop (𝓝 (abelContinuation
        (fun n => if n = 1 then (1 : ℂ) else 0) s)) :=
  tendsto_abelContinuation_Icc _ hs single_isBigO

/-- The alternating sequence. -/
noncomputable def alt : ℕ → ℂ := fun n => (-1) ^ n

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
