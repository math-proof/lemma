import Theorem.Dynamics.PolicyTrajectory
import Def.Order.Miscellaneous
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The clamped reward `fun z ↦ clip z.1 (-R) R` is strongly measurable.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A} :
-- imply
  StronglyMeasurable fun z : ℝ × S × A ↦ clip z.1 (-M.env.R) M.env.R := by
-- proof
  unfold clip
  apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable


-- created on 2026-10-07
-- updated on 2026-10-26
