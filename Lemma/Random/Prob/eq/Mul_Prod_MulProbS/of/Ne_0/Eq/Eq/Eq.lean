import Lemma.Random.Prob.eq.Mul_ProbS.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
import sympy.stats.hidden_markov_sequence
import sympy.Basic
open MeasureTheory


/--
Joint probability of a hidden Markov sequence.
Let `x i` be the observations and `y i` the hidden labels (discrete, counting reference measures)
on a probability space.  Assume that for every `t`, the observation `x (t + 1)` is independent of the
past `(x[:t + 1], y[:t + 1])` given the current label `y (t + 1)`, and that the label `y (t + 1)` is
independent of `(x[:t + 1], y[:t])` given the previous label `y t` (first-order Markov property).  Then

  `Pr(x[:t+1] = xo[:t+1], y[:t+1] = ys[:t+1])
      = Pr(x[0] = xo[0] | y[0] = ys[0]) * Pr(y[0] = ys[0])
        * ∏ i ∈ [1, t+1), Pr(y[i] = ys[i] | y[i-1] = ys[i-1]) * Pr(x[i] = xo[i] | y[i] = ys[i])`.

The conditional independences are exactly what is needed to factorize the joint probability, and the
identity holds without any non-vanishing assumption (if a conditioning event is null, both sides vanish).
-/
@[main]
private lemma main
  {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {xo : ℕ → X}
  [∀ i, SinglePSpace π (y i)]
  [∀ i j, SinglePSpace π (x i, y j)]
  [∀ i j, SinglePSpace π (y i, y j)]
  [∀ n, SinglePSpace π (x[:n], y[:n])]
-- given
  (hx : ∀ k, Measurable (x k))
  (hy : ∀ k, Measurable (y k))
  (hX : ReferenceMeasure.measure (α := X) = Measure.count)
  (hY : ReferenceMeasure.measure (α := Y) = Measure.count)
  (h_emit : ∀ t, ∀ _ : Measurable (y (t + 1)),
    x (t + 1) ⟂ᵢ[π] (x[:t + 1], y[:t + 1]) | y (t + 1))
  (h_markov : ∀ t, ∀ _ : Measurable (y t),
    y (t + 1) ⟂ᵢ[π] (x[:t + 1], y[:t]) | y t)
  (ys : ℕ → Y)
  (t : ℕ) :
-- imply
  ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) =
    ℙ[π]((x 0) = xo 0 | (y 0) = ys 0) * ℙ[π]((y 0) = ys 0) *
      ∏ i ∈ Finset.Ico 1 (t + 1),
        ℙ[π]((y i) = ys i | (y (i - 1)) = ys (i - 1)) * ℙ[π]((x i) = xo i | (y i) = ys i) := by
-- proof
  obtain ⟨h₀, h₁⟩ := Random.Prob.eq.Mul_ProbS.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
    (xo := xo) hx hy hX hY h_emit h_markov ys
  induction t with
  | zero =>
    simpa using h₀
  | succ t ih =>
    rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ t + 1), Nat.add_sub_cancel]
    refine (h₁ t).trans ?_
    rw [ih]
    ring


-- created on 2026-10-02