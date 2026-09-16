import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α]
  [Countable α]
  [MeasurableSingletonClass α]
  {𝕡 : Measure Ω}
  {a : Ω → α}
  {f : α → ENNReal} :
-- imply
  Expectation (𝕡.map a) f = ∑' «a.bvar» : α, f «a.bvar» * 𝕡.map a {«a.bvar»} := by
-- proof
  simp only [Expectation]
  exact lintegral_countable' f


-- created on 2023-03-20
-- updated on 2026-09-16
