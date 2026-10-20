import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry2Corollary1DerivativeSeries
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry2Corollary1DerivativeSeries


/--
[ramanujan_part1_ch3_entry2_corollary1_derivative_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Corollary1DerivativeSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry2_corollary1_derivative_series_eq
  {R : ℝ}
  {f : ℂ → ℂ}
  {z : ℂ}
-- given
  (hR : 1 < R)
  (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R))
  (hz : ∀ n : ℕ, z + (n : ℂ) ≠ 0)
  (hSumm : Summable (fun p : ℕ × ℕ => (-1 : ℂ) ^ p.1 / (Finset.range (p.1 + 1)).prod (fun i => z + (i : ℂ)) * (iteratedDeriv (p.1 + p.2) f (0 : ℂ) / (Nat.factorial p.2 : ℂ)))) :
-- imply
  ∃ c : ℂ,
    HasSum (fun k : ℕ => iteratedDeriv k f (0 : ℂ) /
    ((z + (k : ℂ)) * (Nat.factorial k : ℂ))) c ∧
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k * iteratedDeriv k f (1 : ℂ) /
    (Finset.range (k + 1)).prod (fun i => z + (i : ℂ))) c := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Corollary1DerivativeSeries.ramanujan_part1_ch3_entry2_corollary1_derivative_series R hR f hf z hz hSumm


-- created on 2026-10-20
