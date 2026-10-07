import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
`‖1{p z} * g z‖ ≤ C` whenever `‖g‖ ≤ C`.
-/
@[main]
private lemma main
  {p : α → Prop} [DecidablePred p]
  {g : α → ℝ}
  {C : ℝ}
-- given
  (hC : ∀ z, ‖g z‖ ≤ C)
  (z : α) :
-- imply
  ‖(if p z then (1:ℝ) else 0) * g z‖ ≤ C := by
-- proof
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by split_ifs <;> simp)).trans (hC z)


-- created on 2026-10-07
