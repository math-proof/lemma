import Mathlib.Analysis.MellinTransform

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.ArchBessel

open MeasureTheory Set

def besselKernel (ν : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))

end LanglandsTunnell.ArchBessel

end
