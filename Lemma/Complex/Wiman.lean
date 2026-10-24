import Mathlib
import sympy.Basic
import sympy.calculus.complex.Wiman

open Complex.Wiman
open Complex Set


namespace Complex

/--
[wimanTerm_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
lemma wimanTerm_abs
-- given
  (f : ℂ → ℂ)
  (r : ℝ)
  (n : ℕ) :
-- imply
  wimanTerm f |r| n = wimanTerm f r n := by
-- proof
  simp [wimanTerm]

end Complex

namespace Complex

/--
[wimanMaximumTerm_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
lemma wimanMaximumTerm_abs
-- given
  (f : ℂ → ℂ)
  (r : ℝ) :
-- imply
  wimanMaximumTerm f |r| = wimanMaximumTerm f r := by
-- proof
  apply congrArg sSup
  apply congrArg Set.range
  funext n
  exact wimanTerm_abs f r n

end Complex

namespace Complex

/--
[wimanMaximumModulus_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
lemma wimanMaximumModulus_abs
-- given
  (f : ℂ → ℂ)
  (r : ℝ) :
-- imply
  wimanMaximumModulus f |r| = wimanMaximumModulus f r := by
-- proof
  simp [wimanMaximumModulus]

end Complex

namespace Complex

/--
[wimanTerm_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
lemma wimanTerm_neg
-- given
  (f : ℂ → ℂ)
  (r : ℝ)
  (n : ℕ) :
-- imply
  wimanTerm f (-r) n = wimanTerm f r n := by
-- proof
  simp [wimanTerm]

end Complex

namespace Complex

/--
[wimanMaximumTerm_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
lemma wimanMaximumTerm_neg
-- given
  (f : ℂ → ℂ)
  (r : ℝ) :
-- imply
  wimanMaximumTerm f (-r) = wimanMaximumTerm f r := by
-- proof
  apply congrArg sSup
  apply congrArg Set.range
  funext n
  exact wimanTerm_neg f r n

end Complex

namespace Complex

/--
[wimanMaximumModulus_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
lemma wimanMaximumModulus_neg
-- given
  (f : ℂ → ℂ)
  (r : ℝ) :
-- imply
  wimanMaximumModulus f (-r) = wimanMaximumModulus f r := by
-- proof
  simp [wimanMaximumModulus]

end Complex

namespace Complex

/--
[norm_le_wimanMaximumModulus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
lemma norm_le_wimanMaximumModulus
-- given
  {f : ℂ → ℂ}
  {r : ℝ}
  {z : ℂ}
  (hf : Continuous f)
  (hz : ‖z‖ = r) :
-- imply
  ‖f z‖ ≤ wimanMaximumModulus f r := by
-- proof
  have hr : 0 ≤ r := hz ▸ norm_nonneg z
  apply le_csSup
  · exact (isCompact_sphere (0 : ℂ) |r|).bddAbove_image
    ((continuous_norm.comp hf).continuousOn)
  · exact ⟨z, by simpa [Metric.mem_sphere, abs_of_nonneg hr] using hz, rfl⟩

end Complex

namespace Complex

/--
[cube_le_cube_mul_log_sq_of_wiman](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
lemma cube_le_cube_mul_log_sq_of_wiman
-- given
  {M μ : ℝ}
  (hM : 0 ≤ M)
  (hμ : 0 ≤ μ)
  (hlog : 0 ≤ Real.log μ)
  (hWiman : M ≤ μ * Real.log μ ^ (2 / 3 : ℝ)) :
-- imply
  M ^ 3 ≤ μ ^ 3 * Real.log μ ^ 2 := by
-- proof
  calc
    M ^ 3 ≤ (μ * Real.log μ ^ (2 / 3 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ hM hWiman 3
    _ = μ ^ 3 * (Real.log μ ^ (2 / 3 : ℝ)) ^ 3 := by
      rw [mul_pow]
    _ = μ ^ 3 * Real.log μ ^ 2 := by
      congr 1
      rw [← Real.rpow_mul_natCast hlog]
      norm_num [Real.rpow_two]
end



-- created on 2026-10-10
-- updated on 2026-10-23
