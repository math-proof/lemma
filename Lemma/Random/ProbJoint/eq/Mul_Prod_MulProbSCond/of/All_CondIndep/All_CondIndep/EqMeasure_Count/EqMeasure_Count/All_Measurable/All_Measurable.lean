import Lemma.Measure.Measure.eq.Count.of.EqMeasure_Count.EqMeasure_Count
import Lemma.Random.EqProbJoint.All_Eq_Mul_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasure_Count.EqMeasure_Count.All_Measurable.All_Measurable
import Lemma.Random.Prob.eq.Mul_ProbS.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
open MeasureTheory Random


@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {«x.bvar» : ℕ → X} {«y.bvar» : ℕ → Y}
-- given
  (hx : ∀ k, Measurable (x k))
  (hy : ∀ k, Measurable (y k))
  (hX : ReferenceMeasure.measure (α := X) = Measure.count)
  (hY : ReferenceMeasure.measure (α := Y) = Measure.count)
  (h_emit : ∀ t, ∀ _ : Measurable (y (t + 1)), x (t + 1) ⟂ᵢ[π] (x[:t + 1], y[:t + 1]) | y (t + 1))
  (h_markov : ∀ t, ∀ _ : Measurable (y t), y (t + 1) ⟂ᵢ[π] (x[:t + 1], y[:t]) | y t)
  (t : ℕ) :
-- imply
  have : ∀ i j, SinglePSpace π (x i, y j) := fun i j =>
    Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable (hx i) (hy j) hX hY
  have : ∀ i j, SinglePSpace π (y i, y j) := fun i j =>
    Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable (hy i) (hy j) hY hY
  have : ∀ n, SinglePSpace π (x[:n], y[:n]) := fun n =>
    Random.SinglePSpace.of.All_Measurable.All_Measurable hx hy
  have : ∀ i, SinglePSpace π (y i) := fun i =>
    Random.SinglePSpace.of.EqMeasureCount.Measurable (hy i) hY
  ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[:t + 1] = «y.bvar»[:t + 1]) =
    ℙ[π]((x 0) = «x.bvar» 0 | (y 0) = «y.bvar» 0) * ℙ[π]((y 0) = «y.bvar» 0) *
      ∏ i ∈ Finset.Ico 1 (t + 1),
        ℙ[π]((y i) = «y.bvar» i | (y (i - 1)) = «y.bvar» (i - 1)) * ℙ[π]((x i) = «x.bvar» i | (y i) = «y.bvar» i) := by
-- proof
  intro _ _ _ _
  obtain ⟨h₀, h₁⟩ := Random.Prob.eq.Mul_ProbS.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
    (xo := «x.bvar») hx hy hX hY h_emit h_markov «y.bvar»
  induction t with
  | zero =>
    simpa using h₀
  | succ t ih =>
    rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ t + 1), Nat.add_sub_cancel]
    apply (h₁ t).trans
    rw [ih]
    ring


@[main]
private lemma mdp
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
    s (t + 1) ⟂ᵢ[π] (s[:t], a[:t]) | (s t, a t))
  (t : ℕ) :
-- imply
  have : ∀ i, SinglePSpace π (s i) := fun i =>
    Random.SinglePSpace.of.EqMeasureCount.Measurable (hs i) hS
  have : ∀ i j, SinglePSpace π (a i, s j) := fun i j =>
    Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable (ha i) (hs j) hA hS
  have : ∀ i, SinglePSpace π (s (i + 1), s i, a i) := fun i =>
    Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable (hs (i + 1)) ((hs i).prodMk (ha i)) hS
      (Measure.Measure.eq.Count.of.EqMeasure_Count.EqMeasure_Count hS hA)
  have : ∀ n, SinglePSpace π (s[:n + 1], a[:n]) := fun n =>
    Random.SinglePSpace.of.All_Measurable.All_Measurable hs ha
  ℙ[π](s[:t + 1] = «s.bvar»[:t + 1] ∧ a[:t] = «a.bvar»[:t]) =
    ℙ[π]((s 0) = «s.bvar» 0) *
      ∏ i ∈ Finset.range t,
        ℙ[π]((a i) = «a.bvar» i | (s i) = «s.bvar» i) * ℙ[π]((s (i + 1)) = «s.bvar» (i + 1) | (s i) = «s.bvar» i ∧ (a i) = «a.bvar» i) := by
-- proof
  intro _ _ _ _
  obtain ⟨h₀, h₁⟩ := Random.EqProbJoint.All_Eq_Mul_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasure_Count.EqMeasure_Count.All_Measurable.All_Measurable
    («s.bvar» := «s.bvar») («a.bvar» := «a.bvar») hs ha hS hA hpol htrans
  induction t with
  | zero =>
    simpa using h₀
  | succ t ih =>
    rw [Finset.prod_range_succ]
    apply (h₁ t).trans
    rw [ih]
    ring


-- created on 2026-10-02
-- updated on 2026-10-04
