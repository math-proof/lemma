/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumModulusAttained.lean -/

import sympy.atlas.Analysis.Complex.Wiman
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

namespace Complex

noncomputable section

open Set

/-- The supremum defining the maximum modulus is attained on every
nonnegatively-sized circle. -/
theorem exists_mem_sphere_eq_wimanMaximumModulus
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ z ∈ Metric.sphere (0 : ℂ) r,
      wimanMaximumModulus f r = ‖f z‖ ∧
      ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖f w‖ ≤ ‖f z‖ := by
  obtain ⟨z, hz, hsup, hmax⟩ :=
    (isCompact_sphere (0 : ℂ) r).exists_sSup_image_eq_and_ge
      (NormedSpace.sphere_nonempty.mpr hr) hf.continuous.norm.continuousOn
  exact ⟨z, hz, by simpa [wimanMaximumModulus, abs_of_nonneg hr] using hsup, hmax⟩

end
