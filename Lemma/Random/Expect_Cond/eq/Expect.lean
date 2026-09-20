import Lemma.Random.ProbCond_Joint.eq.ProbCond
open MeasureTheory Function Random
open scoped Classical


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  [Countable α] [Countable γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass γ]
  [Expectation β]
  {π : Measure Ω} {x : Ω → α} {y : Ω → γ}
  {f : α → γ → β}
-- given
  (hP : PSpace π (x, y))
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hγ : ReferenceMeasure.measure (α := γ) = Measure.count) :
-- imply
  have : PSpace π (x, y, y) := Random.PSpace_Joint_Joint.of.PSpace_Joint hP hα hγ
  𝔼[x: π | y](f x y | y) = 𝔼[x: π | y](f x y) := by
-- proof
  intro _
  change Expectation.partialRV_RA π x y y f = Expectation.partialRV π x y f
  funext ω
  simp only [Expectation.partialRV_RA, Expectation.partialRV, Expectation.partialRV_cond,
    Expectation.condRV]
  congr 1
  apply congrArg
  exact funext fun «x.bvar» ↦ ProbCond_Joint.eq.ProbCond hP hα hγ «x.bvar» (y ω)


-- created on 2026-09-20
