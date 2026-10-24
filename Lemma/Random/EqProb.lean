import Lemma.Measure.EqRnDeriv_Count
import sympy.stats.joint_rv
open MeasureTheory Measure


/--
Over a `CountableMeasure` alphabet, the canonical density of a random variable at a point is the
measure of the corresponding event:
`ℙ(x = «x.bvar») = π {ω | x ω = «x.bvar»}`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α] [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω} {x : Ω → α} [h : SinglePSpace π x]
-- given
  («x.bvar» : α) :
-- imply
  ℙ[π](x = «x.bvar») = π (x ⁻¹' {«x.bvar»}) := by
-- proof
  unfold Measure.prob
  rw [CountableMeasure.measure_eq_count, EqRnDeriv_Count (μ := π.map x) «x.bvar»,
    Measure.map_apply_of_aemeasurable h.aemeasurable (measurableSet_singleton «x.bvar»)]


-- created on 2026-10-02
-- updated on 2026-10-23
