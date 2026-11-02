import Lemma.Random.All_Eq_MulProbCond.of.PSpace_Joint
open MeasureTheory Random


/--
| attributes | lemma |
| :---: | :---: |
| path | Random.All_IffNe0ProbCond |
| comm | Random.All_Iff_Ne0ProbCond |
| mp | Random.All_Imp_Ne0ProbCond |
| mpr | Random.All_ImpNe0ProbCond |
-/
@[path, comm, mp, mpr]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : SinglePSpace π (x, y)) :
-- imply
  ∀ᵐ «\sf{x}» ∂ReferenceMeasure.measure, ∀ᵐ «\sf{y}» ∂ReferenceMeasure.measure,
    ℙ[π](x = «\sf{x}» ∧ y = «\sf{y}») ≠ 0 ↔
      ℙ[π](x = «\sf{x}» | y = «\sf{y}») ≠ 0 := by
-- proof
  have hmul := All_Eq_MulProbCond.of.PSpace_Joint hP
  have := SinglePSpace.of.SinglePSpace.snd hP
  have hzero : ∀ (a : α) (b : β),
      π.prob (x, y) (a, b) = 0 → π.condProb (x, y) (a, b) = 0 :=
    fun a b hz ↦ by
      simp only [Measure.condProb, hz, div_eq_mul_inv, zero_mul]
  refine hmul.mono fun «\sf{x}» hx => hx.mono fun «\sf{y}» hmul' => ?_
  constructor
  · intro hne
    have hprod :
        π.condProb (x, y) («\sf{x}», «\sf{y}») * π.prob y «\sf{y}» ≠ 0 := by
      rwa [hmul'] at hne
    exact (mul_ne_zero_iff.mp hprod).1
  · intro hz hprob0
    exact hz (hzero «\sf{x}» «\sf{y}» hprob0)


-- created on 2026-09-21
-- updated on 2026-11-02
