import Lemma.Random.Prob.eq.Mul_ProbS.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
open MeasureTheory IsDiscreteHMM Random
open scoped ENNReal.ToRealCoe


/--
The emission independence `x (t + 1) ⟂ (x[:t + 1], y[:t + 1]) | y (t + 1)` and the first-order Markov
property `y (t + 1) ⟂ (x[:t + 1], y[:t]) | y t` give the one-step factorization of the prefix probabilities
(`IsHiddenMarkovPr`) used by the CRF lemmas.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure Y] [CountableMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {xo : ℕ → X}
-- given
  (h : IsDiscreteHMM π x y) :
-- imply
  have : ∀ i, SinglePSpace π (y i) := fun i => IsDiscreteHMM.singlePSpace_y (x := x) i
  have : ∀ i j, SinglePSpace π (y i, y j) := fun i j => IsDiscreteHMM.singlePSpace_yy (x := x) i j
  IsHiddenMarkovPr π x y xo := by
-- proof
  intro hPy hPyy ys
  obtain ⟨h₀, h₁⟩ := Prob.eq.Mul_ProbS.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
    («\sf{x}» := xo) h ys
  simp only [fun_getElem] at h₀ h₁
  refine ⟨?_, fun t => ?_⟩
  · rw [h₀, ENNReal.toReal_mul]
  · rw [h₁ t, ENNReal.toReal_mul, ENNReal.toReal_mul]


-- created on 2026-10-02
-- updated on 2026-11-07
