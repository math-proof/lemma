/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermLeModulus.lean -/

import sympy.atlas.Analysis.Complex.Wiman.MaximumModulusAttained
import sympy.atlas.Analysis.Complex.Wiman.MaximumTermAttained
import Mathlib.Analysis.Complex.Liouville

namespace Complex

noncomputable section

open Set

/-- The maximum Taylor term is bounded by the maximum modulus on every
positive-radius circle. -/
theorem wimanMaximumTerm_le_wimanMaximumModulus
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) :
    wimanMaximumTerm f r ≤ wimanMaximumModulus f r := by
  obtain ⟨z, hz, hzmax, hmax⟩ :=
    exists_mem_sphere_eq_wimanMaximumModulus f hf hr.le
  apply (wimanMaximumTerm_le_iff f hf r _).2
  intro n
  have hcircle :
      ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖f w‖ ≤ wimanMaximumModulus f r := by
    intro w hw
    rw [hzmax]
    exact hmax w hw
  have hcauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      n hr hf.diffContOnCl hcircle
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hrpow : 0 < r ^ n := pow_pos hr n
  rw [wimanTerm, abs_of_pos hr, wimanTaylorCoefficient, norm_div]
  simp only [Complex.norm_natCast]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hfac).2
  have hscaled := (le_div_iff₀ hrpow).1 hcauchy
  simpa only [mul_comm] using hscaled

end
