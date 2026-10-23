import Lemma.Random.EqProbJoint.All_Eq_Mul_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasureCount.EqMeasureCount.All_Measurable.All_Measurable
open MeasureTheory Random


/--
Base case of the Markov decision process factorization: `ℙ(s[0] = s.bvar[0]) = ℙ(s[:1] = s.bvar[:1], a[:0] = a.bvar[:0])`.
This is the left component of `Random.EqProbJoint.All_Eq_Mul_MulProbSCond…`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure S] [CountableMeasure A]
  [Countable S] [MeasurableSingletonClass S] [Countable A] [MeasurableSingletonClass A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S} {a : ℕ → Ω → A} {«s.bvar» : ℕ → S} {«a.bvar» : ℕ → A}
-- given
  (hs : ∀ k, Measurable (s k))
  (ha : ∀ k, Measurable (a k))
  (hpol : ∀ t, ∀ _ : Measurable (s t),
    a t ⟂ᵢ[π] (s[:t], a[:t]) | s t)
  (htrans : ∀ t, ∀ _ : Measurable (s t, a t),
    s (t + 1) ⟂ᵢ[π] (s[:t], a[:t]) | (s t, a t)) :
-- imply
  have : ∀ i, SinglePSpace π (s i) := fun i =>
    SinglePSpace.of.EqMeasureCount.Measurable (hs i) CountableMeasure.measure_eq_count
  have : ∀ i j, SinglePSpace π (a i, s j) := fun i j =>
    SinglePSpace.of.Measurable.Measurable (ha i) (hs j)
  have : ∀ i, SinglePSpace π (s (i + 1), s i, a i) := fun i =>
    SinglePSpace.of.Measurable.Measurable (hs (i + 1)) ((hs i).prodMk (ha i))
  have : ∀ n, SinglePSpace π (s[:n + 1], a[:n]) := fun _ =>
    SinglePSpace.of.All_Measurable.All_Measurable hs ha
  ℙ[π](s[:0 + 1] = «s.bvar»[:0 + 1] ∧ a[:0] = «a.bvar»[:0]) = ℙ[π]((s 0) = «s.bvar» 0) := by
-- proof
  intro _ _ _ _
  exact (EqProbJoint.All_Eq_Mul_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasureCount.EqMeasureCount.All_Measurable.All_Measurable hs ha hpol htrans).1


-- created on 2026-10-04
-- updated on 2026-10-23
