import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Measure.ArchBessel
open MeasureTheory Set Measure.ArchBessel LanglandsTunnell.ArchBessel


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
  apply Measure.ArchBessel.besselKernel_def


-- created on 2026-10-24
-- updated on 2026-11-15
