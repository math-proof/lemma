import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.BooleanFunctions.code.GaussianNoiseSemigroup
open MeasureTheory ProbabilityTheory Real GaussianStability


namespace GaussianStability

/--
[gaussianNoiseOperator_eq_ornsteinUhlenbeckOp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianNoiseSemigroup.lean)
-/
@[path]
lemma gaussianNoiseOperator_eq_ornsteinUhlenbeckOp
  {n : ℕ}
  {ρ : ℝ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ} :
-- imply
  gaussianNoiseOperator ρ f = GaussianSpace.ornsteinUhlenbeckOp ρ f := by
-- proof
  rfl

end GaussianStability


-- created on 2026-10-23
