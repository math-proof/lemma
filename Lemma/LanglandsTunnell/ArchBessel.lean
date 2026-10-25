import Mathlib.Analysis.MellinTransform
import Def.LanglandsTunnell_ArchBessel

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.ArchBessel

open MeasureTheory Set


theorem besselKernel_def (ν : ℂ) (x : ℝ) :
    besselKernel ν x = ∫ t in Ioi (0 : ℝ), (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1)) :=
  rfl

end LanglandsTunnell.ArchBessel

end
