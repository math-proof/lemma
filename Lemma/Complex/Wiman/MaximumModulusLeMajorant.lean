import Mathlib
import sympy.Basic
import Theorem.Analysis.Complex.Wiman.MaximumModulusLeMajorant
open Complex


namespace Complex

/--
[wimanMaximumModulus_le_wimanMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumModulusLeMajorant.lean)
-/
@[path]
lemma wimanMaximumModulus_le_wimanMajorant
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hr : 0 ≤ r) :
-- imply
  wimanMaximumModulus f r ≤ wimanMajorant f r := by
-- proof
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



-- created on 2026-10-20
-- updated on 2026-10-23
