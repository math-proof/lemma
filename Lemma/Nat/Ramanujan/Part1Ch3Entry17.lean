import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry17
open Filter Metric
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry17


/--
[ramanujan_part1_ch3_entry17](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry17.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry17_eq
  :
-- imply
  ∀ (a : ℝ), 1 / Real.exp 1 < a →
    ∃ (R : ℝ) (x : ℝ → ℝ), 0 < R ∧ AnalyticAt ℝ x (0 : ℝ) ∧ x 0 = a ∧
    (∀ h : ℝ, |h| < R → 0 < x h ∧ x h ^ x h = a ^ a * Real.exp h) ∧ ∀ r : ℕ, 2 ≤ r →
    (-a) ^ (r - 1) * iteratedDeriv r x 0 = (1 + Real.log a)⁻¹ * ((r : ℝ) - 2) *
    ((-a) ^ (r - 2) * iteratedDeriv (r - 1) x 0) + (1 + Real.log a)⁻¹ *
    ∑ k ∈ Finset.Icc 1 (r - 1), (Nat.choose (r - 1) k : ℝ) *
    ((-a) ^ (k - 1) * iteratedDeriv k x 0) *
    ((-a) ^ (r - k - 1) * iteratedDeriv (r - k) x 0) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry17.ramanujan_part1_ch3_entry17


-- created on 2026-10-20
