module
public import Mathlib
public import Theorem.v1.Atlas.BooleanFunctions.code.GaussianNoiseSemigroup
open MeasureTheory ProbabilityTheory Real GaussianStability


public section

/--
[gaussianNoiseOperator_eq_ornsteinUhlenbeckOp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianNoiseSemigroup.lean)
-/
theorem GaussianStability.gaussianNoiseOperator_eq_ornsteinUhlenbeckOp
  {n : ℕ}
  {ρ : ℝ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ} :
-- imply
  gaussianNoiseOperator ρ f = GaussianSpace.ornsteinUhlenbeckOp ρ f := by
-- proof
  rfl


-- created on 2026-10-23
-- updated on 2026-11-24
