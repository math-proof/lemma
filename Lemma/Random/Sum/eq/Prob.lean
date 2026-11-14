import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Lemma.Random.All_EqIntegral_ProbJoint.of.PSpace_Joint
open Random MeasureTheory Measure


/--
Marginalization over a countable support: summing the joint point density
over all values of `x` gives the marginal density of `y`.

Python: Random.Sum.eq.Prob (marked `provable=False` there; proved here in the
discrete countable setting where the reference measure on `α` is `count`).

| attributes | lemma |
| :---: | :---: |
| path | Random.Sum.eq.Prob |
| comm | Random.Prob.eq.Sum |
-/
@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α] [ν : ReferenceMeasure β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : SinglePSpace π (x, y))
  (hα : μ.measure = Measure.count)
  (hβ : ν.measure = Measure.count)
  («\sf{y}» : β) :
-- imply
  have : SinglePSpace π y := SinglePSpace.of.SinglePSpace.snd hP
  ∑' «\sf{x}» : α, ℙ[π](x = «\sf{x}» ∧ y = «\sf{y}») =
    ℙ[π](y = «\sf{y}») := by
-- proof
  intro hPy
  have hleft : ∀ᵐ y₀ ∂ReferenceMeasure.measure,
      ∫⁻ x₀, π.prob (x, y) (x₀, y₀) ∂ReferenceMeasure.measure =
        π.prob y y₀ :=
    All_EqIntegral_ProbJoint.of.PSpace_Joint.left hP
  have hall := by
    rw [hα, hβ] at hleft
    exact ae_count_iff.mp hleft
  have h := hall «\sf{y}»
  rwa [lintegral_count] at h


-- created on 2020-12-21
-- updated on 2026-11-14
