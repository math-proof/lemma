import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Problem_1_5
open MeasureTheory ProbabilityTheory Real Finset


/--
[problem_1_5a_norm_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_5.lean)
-/
@[path]
lemma problem_1_5a_norm_comparison
  {n : ℕ}
  {q : ℝ}
  {x : Fin n → ℝ}
-- given
  (hq : 2 ≤ q) :
-- imply
  lqNorm n 2 x ≤ lqNorm n q x * (n : ℝ) ^ (1 / 2 - 1 / q) := by
-- proof
  unfold lqNorm
  have hq_pos : (0:ℝ) < q := by linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq2 : (1:ℝ) ≤ q / 2 := by linarith
  have h1q_pos : (0:ℝ) < 1 / q := by positivity
  have hS2 : (0:ℝ) ≤ ∑ i : Fin n, |x i| ^ (2:ℝ) :=
    Finset.sum_nonneg (fun i _ => rpow_nonneg (abs_nonneg _) _)
  have hSq : (0:ℝ) ≤ ∑ i : Fin n, |x i| ^ q :=
    Finset.sum_nonneg (fun i _ => rpow_nonneg (abs_nonneg _) _)
  have key : (∑ i : Fin n, |x i| ^ (2:ℝ)) ^ (q/2) ≤
    (↑n : ℝ) ^ (q / 2 - 1) * ∑ i : Fin n, |x i| ^ q := by
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.univ : Finset (Fin n))
      hq2 (fun i _ => rpow_nonneg (abs_nonneg (x i)) (2:ℝ))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    convert h using 2
    apply Finset.sum_congr rfl
    intro i _
    rw [← rpow_mul (abs_nonneg _)]
    ring_nf
  have key2 : ((∑ i : Fin n, |x i| ^ (2:ℝ)) ^ (q/2)) ^ (1/q) ≤
    ((↑n : ℝ) ^ (q / 2 - 1) * ∑ i : Fin n, |x i| ^ q) ^ (1/q) :=
    rpow_le_rpow (rpow_nonneg hS2 _) key (le_of_lt h1q_pos)
  rw [← rpow_mul hS2, show q / 2 * (1 / q) = 1 / 2 from by field_simp] at key2
  have hexp : (q / 2 - 1) * (1 / q) = 1 / 2 - 1 / q := by field_simp
  rw [mul_rpow (rpow_nonneg (Nat.cast_nonneg n) _) hSq,
    ← rpow_mul (Nat.cast_nonneg n), hexp] at key2
  linarith [mul_comm ((∑ i : Fin n, |x i| ^ q) ^ (1 / q)) ((↑n : ℝ) ^ (1 / 2 - 1 / q))]
/-- **Problem 1.5(b).** For independent sub-Gaussian variables `X₁,…,Xₙ` with
proxy `σ²` and `q > 1`, `E ‖X‖_q ≤ 4 σ · n^{1/q} · √q`. -/


-- created on 2026-10-23
