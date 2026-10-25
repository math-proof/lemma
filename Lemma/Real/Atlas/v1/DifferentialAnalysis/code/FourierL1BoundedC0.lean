import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.FourierL1BoundedC0
open MeasureTheory Filter Complex FourierL1BoundedC0
open scoped FourierTransform RealInnerProductSpace Topology


namespace FourierL1BoundedC0

/--
[fourier_norm_le_L1_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierL1BoundedC0.lean)
-/
@[path]
lemma fourier_norm_le_L1_norm
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [NormedAddCommGroup E]
  [NormedSpace ℂ E]
  {f : V → E}
  {w : V} :
-- imply
  ‖𝓕 f w‖ ≤ ∫ v, ‖f v‖ :=
-- proof
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ f w

end FourierL1BoundedC0

namespace FourierL1BoundedC0

/--
[fourier_tendsto_zero_at_infty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierL1BoundedC0.lean)
-/
@[path]
lemma fourier_tendsto_zero_at_infty
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [NormedAddCommGroup E]
  [NormedSpace ℂ E]
  {f : V → E} :
-- imply
  Tendsto (𝓕 f) (cocompact V) (𝓝 0) :=
-- proof
  tendsto_integral_exp_inner_smul_cocompact f
end FourierL1BoundedC0



-- created on 2026-10-23
