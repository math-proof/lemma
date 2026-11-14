import Lemma.Random.EqProbJoint.All_Eq_Mul_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasureCount.EqMeasureCount.All_Measurable.All_Measurable
import Lemma.Random.Prob.eq.Mul_ProbS.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
open MeasureTheory Random
open IsDiscreteHMM


@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure Y] [CountableMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {«\sf{x}» : ℕ → X} {«\sf{y}» : ℕ → Y}
-- given
  (h : IsDiscreteHMM π x y)
  (t : ℕ) :
-- imply
  ℙ[π](x[:t + 1] = «\sf{x}»[:t + 1] ∧ y[:t + 1] = «\sf{y}»[:t + 1]) =
    ℙ[π]((x 0) = «\sf{x}» 0 | (y 0) = «\sf{y}» 0) * ℙ[π]((y 0) = «\sf{y}» 0) *
      ∏ i ∈ Finset.Ico 1 (t + 1),
        ℙ[π]((y i) = «\sf{y}» i | (y (i - 1)) = «\sf{y}» (i - 1)) * ℙ[π]((x i) = «\sf{x}» i | (y i) = «\sf{y}» i) := by
-- proof
  obtain ⟨h₀, h₁⟩ := Prob.eq.Mul_ProbS.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
    («\sf{x}» := «\sf{x}») h «\sf{y}»
  simp only [fun_getElem] at h₀ h₁
  induction t with
  | zero =>
    simpa using h₀
  | succ t ih =>
    rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ t + 1), Nat.add_sub_cancel]
    apply (h₁ t).trans
    rw [ih]
    ring

@[path]
private lemma mdp
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure S] [CountableMeasure A]
  [Countable S] [MeasurableSingletonClass S] [Countable A] [MeasurableSingletonClass A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S} {a : ℕ → Ω → A} {«\sf{s}» : ℕ → S} {«\sf{a}» : ℕ → A}
-- given
  (hs : ∀ k, Measurable (s k))
  (ha : ∀ k, Measurable (a k))
  (hpol : ∀ t, ∀ _ : Measurable (s t),
    a t ⟂ᵢ[π] (s[:t], a[:t]) | s t)
  (htrans : ∀ t, ∀ _ : Measurable (s t, a t),
    s (t + 1) ⟂ᵢ[π] (s[:t], a[:t]) | (s t, a t))
  (t : ℕ) :
-- imply
  have : ∀ i, SinglePSpace π (s i) := fun i =>
    SinglePSpace.of.Measurable (hs i)
  have : ∀ i j, SinglePSpace π (a i, s j) := fun i j =>
    SinglePSpace.of.Measurable.Measurable (ha i) (hs j)
  have : ∀ i, SinglePSpace π (s (i + 1), s i, a i) := fun i =>
    SinglePSpace.of.Measurable.Measurable (hs (i + 1)) ((hs i).prodMk (ha i))
  have : ∀ n, SinglePSpace π (s[:n + 1], a[:n]) := fun _ =>
    SinglePSpace.of.All_Measurable.All_Measurable hs ha
  ℙ[π](s[:t + 1] = «\sf{s}»[:t + 1] ∧ a[:t] = «\sf{a}»[:t]) =
    ℙ[π]((s 0) = «\sf{s}» 0) *
      ∏ i ∈ Finset.range t,
        ℙ[π]((a i) = «\sf{a}» i | (s i) = «\sf{s}» i) * ℙ[π]((s (i + 1)) = «\sf{s}» (i + 1) | (s i) = «\sf{s}» i ∧ (a i) = «\sf{a}» i) := by
-- proof
  intro _ _ _ _
  obtain ⟨h₀, h₁⟩ := EqProbJoint.All_Eq_Mul_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasureCount.EqMeasureCount.All_Measurable.All_Measurable
    («\sf{s}» := «\sf{s}») («\sf{a}» := «\sf{a}») hs ha hpol htrans
  induction t with
  | zero =>
    simpa using h₀
  | succ t ih =>
    rw [Finset.prod_range_succ]
    apply (h₁ t).trans
    rw [ih]
    ring


-- created on 2020-12-17
-- updated on 2026-11-02
