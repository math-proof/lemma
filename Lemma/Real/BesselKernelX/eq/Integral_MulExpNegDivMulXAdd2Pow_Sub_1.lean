import Mathlib
import sympy.Basic
import Lemma.LanglandsTunnell.ArchBessel
open MeasureTheory Set LanglandsTunnell.ArchBessel


/--
Unfolding of besselKernel as the Mellin-type integral.
-/
@[path]
private lemma main
  {ν : ℂ}
  {x : ℝ} :
-- imply
  besselKernel ν x =
    ∫ t in Ioi (0 : ℝ), (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1)) := by
-- proof
  rfl


-- created on 2026-10-24
