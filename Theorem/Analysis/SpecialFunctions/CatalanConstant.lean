/-
# Catalan's constant
-/
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Def.Analysis.SpecialFunctions.CatalanConstant


namespace Real

/-- The defining series of Catalan's constant converges absolutely: its
terms are bounded in norm by the convergent series `∑ n, 1 / (n + 1)^2`. -/
theorem summable_catalanConstant_terms :
    Summable (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2) := by
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) ?_ ?_
  · have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 := (summable_nat_add_iff 1).mpr h
    refine h2.congr (fun n => ?_)
    push_cast
    ring
  · intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_div]
    simp only [abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 * (n : ℝ) + 1 by positivity),
      abs_neg, abs_one, one_pow]
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- Characteristic equation: Catalan's constant is the sum of its
defining alternating series. Downstream users should rewrite with this
lemma (or `Real.hasSum_catalanConstant`) instead of unfolding the
definition. -/
theorem catalanConstant_eq_tsum :
    catalanConstant = ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 :=
  rfl

/-- The defining series of Catalan's constant has it as its sum. -/
theorem hasSum_catalanConstant :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2)
      catalanConstant :=
  summable_catalanConstant_terms.hasSum

end Real
