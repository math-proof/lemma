import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Complex.Wiman.MaximumModulusAttained
open Set
open Complex


namespace Complex

/--
[exists_mem_sphere_eq_wimanMaximumModulus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumModulusAttained.lean)
-/
@[path]
lemma exists_mem_sphere_eq_wimanMaximumModulus
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hr : 0 ≤ r) :
-- imply
  ∃ z ∈ Metric.sphere (0 : ℂ) r,
    wimanMaximumModulus f r = ‖f z‖ ∧
    ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖f w‖ ≤ ‖f z‖ := by
-- proof
  obtain ⟨z, hz, hsup, hmax⟩ :=
    (isCompact_sphere (0 : ℂ) r).exists_sSup_image_eq_and_ge
      (NormedSpace.sphere_nonempty.mpr hr) hf.continuous.norm.continuousOn
  exact ⟨z, hz, by simpa [wimanMaximumModulus, abs_of_nonneg hr] using hsup, hmax⟩
end



-- created on 2026-10-20
-- updated on 2026-10-26
