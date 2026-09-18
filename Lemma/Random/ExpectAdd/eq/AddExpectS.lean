import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main, comm]
private lemma main
  [MeasurableSpace α]
  {ν : Measure α}
  {f g : α → ENNReal}
-- given
  (hf : Measurable f) :
-- imply
  Expectation ν (f + g) = Expectation ν f + Expectation ν g := by
-- proof
  simp only [Expectation, Pi.add_apply]
  exact lintegral_add_left hf g


/--
Conditional version of `AddExpectS`: under the conditional law of `a` given
`s = «s.bvar»` (the reference measure with density `𝕡.condProb (a, s)`),
expectation distributes over addition. Additivity holds for an arbitrary measure,
so no discreteness hypothesis on the reference measure is needed.
-/
private lemma given
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α]
  [MeasurableSingletonClass α]
  {𝕡 : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f g : α → ENNReal}
-- given
  (hP : PSpace 𝕡 (a, s))
  (hf : Measurable f)
  («s.bvar» : β) :
-- imply
  Expectation (ReferenceMeasure.measure.withDensity
      (fun «a.bvar» ↦ 𝕡.condProb (a, s) («a.bvar», «s.bvar»))) (f + g) =
    Expectation (ReferenceMeasure.measure.withDensity
      (fun «a.bvar» ↦ 𝕡.condProb (a, s) («a.bvar», «s.bvar»))) f +
    Expectation (ReferenceMeasure.measure.withDensity
      (fun «a.bvar» ↦ 𝕡.condProb (a, s) («a.bvar», «s.bvar»))) g := by
-- proof
  simp only [Expectation, Pi.add_apply]
  exact lintegral_add_left hf g


-- created on 2023-03-24
-- updated on 2026-09-18
