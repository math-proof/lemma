import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Lemma.Random.All_EqIntegral_ProbJoint.of.PSpace_Joint
import sympy.stats.joint_rv
open Random MeasureTheory Measure


/--
Marginalization over a countable support: summing the joint point density
over all values of `x` gives the marginal density of `y`.

Python: Random.Sum.eq.Prob (marked `provable=False` there; proved here in the
discrete countable setting where the reference measure on `α` is `count`).

| attributes | lemma |
| :---: | :---: |
| main | Random.Sum.eq.Prob |
| comm | Random.Prob.eq.Sum |
-/
@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace π (x, y))
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hβ : ReferenceMeasure.measure (α := β) = Measure.count)
  («y.bvar» : β) :
-- imply
  have : PSpace π y := PSpace.of.PSpace_Joint.snd hP
  ∑' «x.bvar» : α, ℙ[π](x = «x.bvar» ∧ y = «y.bvar») =
    ℙ[π](y = «y.bvar») := by
-- proof
  intro hPy
  have hleft : ∀ᵐ y₀ ∂ReferenceMeasure.measure,
      ∫⁻ x₀, π.prob (x, y) (x₀, y₀) ∂ReferenceMeasure.measure =
        π.prob y y₀ :=
    All_EqIntegral_ProbJoint.of.PSpace_Joint.left hP
  have hall := by
    rw [hα, hβ] at hleft
    exact ae_count_iff.mp hleft
  have h := hall «y.bvar»
  rwa [lintegral_count] at h


-- created on 2026-09-26
