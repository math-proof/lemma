import Lemma.Random.All_Eq_MulProbCond.of.PSpace_Joint
open MeasureTheory Random


/--
| attributes | lemma |
| :---: | :---: |
| main | Random.All_IffNe0ProbCond |
| comm | Random.All_Iff_Ne0ProbCond |
| mp | Random.All_Imp_Ne0ProbCond |
| mpr | Random.All_ImpNe0ProbCond |
-/
@[main, comm, mp, mpr]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace π (x, y)) :
-- imply
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure, ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
    ℙ[π](x = «x.bvar» ∧ y = «y.bvar») ≠ 0 ↔
      ℙ[π](x = «x.bvar» | y = «y.bvar») ≠ 0 := by
-- proof
  have hmul := All_Eq_MulProbCond.of.PSpace_Joint hP
  have := PSpace.of.PSpace_Joint.snd hP
  have hzero : ∀ (a : α) (b : β),
      π.prob (x, y) (a, b) = 0 → π.condProb (x, y) (a, b) = 0 :=
    fun a b hz ↦ by
      simp only [Measure.condProb, hz, div_eq_mul_inv, zero_mul]
  refine hmul.mono fun «x.bvar» hx => hx.mono fun «y.bvar» hmul' => ?_
  constructor
  · intro hne
    have hprod :
        π.condProb (x, y) («x.bvar», «y.bvar») * π.prob y «y.bvar» ≠ 0 := by
      rwa [hmul'] at hne
    exact (mul_ne_zero_iff.mp hprod).1
  · intro hz hprob0
    exact hz (hzero «x.bvar» «y.bvar» hprob0)


-- created on 2026-09-21
