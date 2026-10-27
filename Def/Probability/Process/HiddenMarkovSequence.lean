import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Syntax.Probability.JointRv.Part6
import Def.Data.List.List.Part5
import Instance.Analysis.Real.Numbers
import Def.Fun


/-- Sequential (first-order, hidden) Markov structure of the prefix joint probabilities used by the
py CRF lemmas.  `P t ys` is `ℙ(x[:t+1] = x_obs[:t+1], y[:t+1] = ys[:t+1])` for the fixed observed
sequence, `π a = ℙ(y[0] = a)`, `T a b = ℙ(y[i] = b | y[i-1] = a)` (time-homogeneous) and
`E i b = ℙ(x[i] = x_obs[i] | y[i] = b)`.  The py independence assumptions
(`x[k] | x[:k] & y[:k] = x[k]`, `y[k] | y[:k] = y[k] | y[k-1]`, `y[k] | x[:k] = y[k]`) are used in py
only through the one-step factorization recorded here. -/
def IsHiddenMarkovSeq {Y : Type*} (P : ℕ → (ℕ → Y) → ℝ) (π : Y → ℝ) (T : Y → Y → ℝ) (E : ℕ → Y → ℝ) : Prop :=
  ∀ ys : ℕ → Y, P 0 ys = E 0 (ys 0) * π (ys 0) ∧
    ∀ t, P (t + 1) ys = P t ys * (T (ys t) (ys (t + 1)) * E (t + 1) (ys (t + 1)))


open MeasureTheory

open scoped ENNReal.ToRealCoe

/-- Generic form of `IsHiddenMarkovPr`: the one-step factorization of an abstract prefix-probability family `P`
(`IsHiddenMarkovPr` is this with `P t ys := ℙ(x[:t+1] = xo[:t+1], y[:t+1] = ys[:t+1])`).
Sequential (first-order, hidden) Markov structure of the prefix joint probabilities used by the
py CRF lemmas, stated directly in probability notation.  `y i : Ω → Y` are the hidden labels,
`x i : Ω → X` the observations and `xo i` the fixed observed value of `x i`.
`P t ys` is `ℙ(x[:t+1] = xo[:t+1], y[:t+1] = ys[:t+1])` and satisfies the one-step factorization

  `P 0 ys = ℙ(x[0] = xo[0] | y[0] = ys[0]) * ℙ(y[0] = ys[0])`,
  `P (t+1) ys = P t ys * (ℙ(y[t+1] = ys[t+1] | y[t] = ys[t]) * ℙ(x[t+1] = xo[t+1] | y[t+1] = ys[t+1]))`

which is all the py independence assumptions
(`x[k] | x[:k] & y[:k] = x[k]`, `y[k] | y[:k] = y[k] | y[k-1]`, `y[k] | x[:k] = y[k]`) are used for. -/
def IsHiddenMarkovFac {Ω Y X : Type*} [MeasurableSpace Ω] [ReferenceMeasure Y] [ReferenceMeasure X]
    (π : Measure Ω) (x : ℕ → Ω → X) (y : ℕ → Ω → Y) (xo : ℕ → X) (P : ℕ → (ℕ → Y) → ℝ)
    [∀ i, SinglePSpace π (y i)] [∀ i j, SinglePSpace π (x i, y j)]
    [∀ i j, SinglePSpace π (y i, y j)] : Prop :=
  ∀ ys : ℕ → Y,
    P 0 ys = (ℙ[π]((x 0) = xo 0 | (y 0) = ys 0) : ℝ) * (ℙ[π]((y 0) = ys 0) : ℝ) ∧
    ∀ t, P (t + 1) ys = P t ys * ((ℙ[π]((y (t + 1)) = ys (t + 1) | (y t) = ys t) : ℝ) *
      (ℙ[π]((x (t + 1)) = xo (t + 1) | (y (t + 1)) = ys (t + 1)) : ℝ))


