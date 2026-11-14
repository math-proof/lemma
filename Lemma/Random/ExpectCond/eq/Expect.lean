import Lemma.Random.ProbCond_Joint.eq.ProbCond
open MeasureTheory Function Random
open scoped Classical


@[path]
private lemma main
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α] [ξ : ReferenceMeasure γ]
  [Countable α] [Countable γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass γ]
  [Expectation β]
  {π : Measure Ω} {x : Ω → α} {y : Ω → γ}
  {f : α → γ → β}
-- given
  (hP : SinglePSpace π (x, y))
  (hα : μ.measure = Measure.count)
  (hγ : ξ.measure = Measure.count) :
-- imply
  have : SinglePSpace π (x, y, y) := Random.PSpace_Joint_Joint.of.PSpace_Joint hP hα hγ
  Expectation.partialRV_RA π x y y f = 𝔼[x: π | y](f x y) := by
-- proof
  intro _
  change Expectation.partialRV_RA π x y y f = Expectation.partialRV π x y f
  funext ω
  simp only [Expectation.partialRV_RA, Expectation.partialRV, Expectation.partialRV_cond,
    Expectation.condRV]
  congr 1
  apply congrArg
  exact funext fun «\sf{x}» ↦ ProbCond_Joint.eq.ProbCond hP hα hγ «\sf{x}» (y ω)


-- created on 2026-09-20
-- updated on 2026-11-14
