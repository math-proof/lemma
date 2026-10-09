import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Random.SinglePSpace.of.All_Measurable.All_Measurable
import Lemma.Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
import Lemma.Random.EqProbJoint.All_Eq_Mul_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasureCount.EqMeasureCount.All_Measurable.All_Measurable
import sympy.stats.hidden_markov_sequence
import sympy.Basic
open MeasureTheory


/--
Base case of the Markov decision process factorization: `Pr(s[0] = s.bvar[0]) = Pr(s[:1] = s.bvar[:1], a[:0] = a.bvar[:0])`.
This is the left component of `Random.EqProbJoint.All_Eq_Mul_MulProbSCond…`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure S] [ReferenceMeasure A]
  [Countable S] [MeasurableSingletonClass S] [Countable A] [MeasurableSingletonClass A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S} {a : ℕ → Ω → A} {«s.bvar» : ℕ → S} {«a.bvar» : ℕ → A}
-- given
  (hs : ∀ k, Measurable (s k))
  (ha : ∀ k, Measurable (a k))
  (hS : ReferenceMeasure.measure (α := S) = Measure.count)
  (hA : ReferenceMeasure.measure (α := A) = Measure.count)
  (hpol : ∀ t, ∀ _ : Measurable (s t),
    a t ⟂ᵢ[π] (s[:t], a[:t]) | s t)
  (htrans : ∀ t, ∀ _ : Measurable (s t, a t),
    s (t + 1) ⟂ᵢ[π] (s[:t], a[:t]) | (s t, a t)) :
-- imply
  have : ∀ i, SinglePSpace π (s i) := fun i =>
    Random.SinglePSpace.of.EqMeasureCount.Measurable (hs i) hS
  have : ∀ i j, SinglePSpace π (a i, s j) := fun i j =>
    Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable (ha i) (hs j) hA hS
  have : ∀ i, SinglePSpace π (s (i + 1), s i, a i) := fun i =>
    Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable (hs (i + 1)) ((hs i).prodMk (ha i)) hS (by
      change (ReferenceMeasure.measure (α := S)).prod ReferenceMeasure.measure = Measure.count
      rw [hS, hA, ← Measure.Count.eq.ProdCountS])
  have : ∀ n, SinglePSpace π (s[:n + 1], a[:n]) := fun n =>
    Random.SinglePSpace.of.All_Measurable.All_Measurable hs ha
  ℙ[π](s[:0 + 1] = «s.bvar»[:0 + 1] ∧ a[:0] = «a.bvar»[:0]) = ℙ[π]((s 0) = «s.bvar» 0) := by
-- proof
  intro _ _ _ _
  exact (Random.EqProbJoint.All_Eq_Mul_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasureCount.EqMeasureCount.All_Measurable.All_Measurable hs ha hS hA hpol htrans).1


-- created on 2026-10-04
