import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Syntax.Probability.JointRv.Part6
import Def.Data.List.List.Part5
import Instance.Analysis.Real.Numbers
import Def.Fun
import Macro.Probability.Process.HiddenMarkovSequence
open MeasureTheory
open scoped ENNReal.ToRealCoe


/-- The py first-order hidden Markov assumptions in probability notation (py `markov_assumptions` + `Random.ProbJoint.eq.Mul_Prod_MulProbSCond.of.IsDiscreteHMM`):
for every label sequence `ys`,

  `ℙ(x[:1] = xo[:1], y[:1] = ys[:1]) = ℙ(x[0] = xo[0] | y[0] = ys[0]) * ℙ(y[0] = ys[0])`,
  `ℙ(x[:t+2] = xo[:t+2], y[:t+2] = ys[:t+2]) = ℙ(x[:t+1] = xo[:t+1], y[:t+1] = ys[:t+1])
      * (ℙ(y[t+1] = ys[t+1] | y[t] = ys[t]) * ℙ(x[t+1] = xo[t+1] | y[t+1] = ys[t+1]))`. -/
def IsHiddenMarkovPr {Ω Y X : Type*} [MeasurableSpace Ω] [ReferenceMeasure Y] [ReferenceMeasure X]
    [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
    (π : Measure Ω) (x : ℕ → Ω → X) (y : ℕ → Ω → Y) (xo : ℕ → X)
    [∀ i, SinglePSpace π (y i)] [∀ i j, SinglePSpace π (x i, y j)]
    [∀ i j, SinglePSpace π (y i, y j)]
    [∀ n, SinglePSpace π (x[:n], y[:n])] : Prop :=
  ∀ ys : ℕ → Y,
    (ℙ[π](x[:0 + 1] = xo[:0 + 1] ∧ y[:0 + 1] = ys[:0 + 1]) : ℝ) =
        (ℙ[π]((x 0) = xo 0 | (y 0) = ys 0) : ℝ) * (ℙ[π]((y 0) = ys 0) : ℝ) ∧
    ∀ t : ℕ, (ℙ[π](x[:t + 1 + 1] = xo[:t + 1 + 1] ∧ y[:t + 1 + 1] = ys[:t + 1 + 1]) : ℝ) =
      (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ) *
        ((ℙ[π]((y (t + 1)) = ys (t + 1) | (y t) = ys t) : ℝ) *
          (ℙ[π]((x (t + 1)) = xo (t + 1) | (y (t + 1)) = ys (t + 1)) : ℝ))


-- created on 2026-09-27
-- updated on 2026-10-22

