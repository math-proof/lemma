import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The clamped reward `rc` is strongly measurable.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A} :
-- imply
  StronglyMeasurable M.rc := by
-- proof
  change StronglyMeasurable fun z : ℝ × S × A => clip z.1 (-M.env.R) M.env.R
  unfold clip
  apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable


-- created on 2026-10-07
-- updated on 2026-10-11
