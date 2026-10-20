/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumModulusLeMajorant.lean -/

import sympy.atlas.Analysis.Complex.Wiman.MaximumModulusAttained
import sympy.atlas.Analysis.Complex.Wiman.RadialMajorant
namespace Complex

noncomputable section

/-- The maximum modulus on a circle is bounded by the positive radial Taylor majorant. -/
theorem wimanMaximumModulus_le_wimanMajorant
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 ≤ r) :
    wimanMaximumModulus f r ≤ wimanMajorant f r := by
  obtain ⟨z, hz, hmax, _⟩ :=
    exists_mem_sphere_eq_wimanMaximumModulus f hf hr
  rw [hmax]
  have hs := hasSum_wimanTaylorCoefficient_mul_pow f hf z
  calc
    ‖f z‖ = ‖∑' n : ℕ, wimanTaylorCoefficient f n * z ^ n‖ := by
      rw [hs.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖wimanTaylorCoefficient f n * z ^ n‖ :=
      norm_tsum_le_tsum_norm hs.summable.norm
    _ = wimanMajorant f r := by
      rw [wimanMajorant]
      apply tsum_congr
      intro n
      rw [norm_mul, norm_pow, mem_sphere_zero_iff_norm.mp hz, wimanTerm,
        abs_of_nonneg hr]

end
