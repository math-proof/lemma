/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/TaylorExpansion.lean -/

import sympy.atlas.Analysis.Complex.Wiman
import Mathlib.Analysis.Complex.TaylorSeries

namespace Complex

noncomputable section

/-- An entire function is the sum of the Taylor coefficients used by the Wiman definitions. -/
theorem hasSum_wimanTaylorCoefficient_mul_pow
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun n : ℕ => wimanTaylorCoefficient f n * z ^ n) (f z) := by
  simpa only [sub_zero, smul_eq_mul, wimanTaylorCoefficient, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using
    (Complex.hasSum_taylorSeries_of_entire hf 0 z)

end
