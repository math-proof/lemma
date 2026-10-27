import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.Covariance
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Finset


/--
Variance of a finite sum splits into the diagonal variances and the off-diagonal covariances:
`Var[∑ i, x i] = ∑ i, Var[x i] + ∑ i, ∑ j ≠ i, cov[x i, x j]`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [DecidableEq ι]
  {π : Measure Ω} [IsFiniteMeasure π]
  {x : ι → Ω → ℝ} [Fintype ι]
-- given
  (h₀ : ∀ i, MemLp (x i) 2 π) :
-- imply
  variance (fun ω => ∑ i, x i ω) π =
    ∑ i, variance (x i) π + ∑ i, ∑ j ∈ univ.erase i, covariance (x i) (x j) π := by
-- proof
  rw [variance_fun_sum h₀, sum_add_distrib.symm]
  refine sum_congr rfl fun i _ => ?_
  rw [← add_sum_erase univ (fun j => covariance (x i) (x j) π) (mem_univ i), covariance_self (h₀ i).aemeasurable]


-- created on 2023-04-19
-- updated on 2026-10-26
