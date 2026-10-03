import Lemma.Random.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
import sympy.stats.hidden_markov_sequence
import sympy.Basic
open MeasureTheory


/--
Joint probability of a Markov decision process trajectory.
Let `s i` be the states and `a i` the actions (discrete, counting reference measures) on a probability
space.  Assume that for every `t` the action depends on the history only through the current state,
`a t ⟂ (s[:t], a[:t]) | s t`, and the next state only through the current state and action,
`s (t + 1) ⟂ (s[:t], a[:t]) | (s t, a t)`.  Then for the fixed values `sv` and `av`

  `Pr(s[:t+1] = sv[:t+1], a[:t] = av[:t])
      = Pr(s[0] = sv[0]) * ∏ i < t, Pr(a[i] = av[i] | s[i] = sv[i]) * Pr(s[i+1] = sv[i+1] | s[i] = sv[i] ∧ a[i] = av[i])`.

No non-vanishing assumption is needed: when a conditioning event is null, both sides vanish.
(The py lemma `Random.Eq.of.Ne_0.Eq.Eq.Eq.markov.decision` also carries the rewards `r`, which have no
reference measure on `Fin t → ℝ` here, so the joint is taken over states and actions only; its
marginal independence hypotheses `s[k + 1] | s[:k] & a[:k] = s[k + 1]` are too weak for this
factorization, hence the conditional form.)

Python: Random.Eq.of.Ne_0.Eq.Eq.Eq.markov.decision.
-/
@[main]
private lemma main
  {Ω S A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure S] [ReferenceMeasure A]
  [Countable S] [MeasurableSingletonClass S] [Countable A] [MeasurableSingletonClass A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S} {a : ℕ → Ω → A} {sv : ℕ → S} {av : ℕ → A}
  [∀ i, SinglePSpace π (s i)]
  [∀ i j, SinglePSpace π (a i, s j)]
  [∀ i, SinglePSpace π (JointRandomSymbol (s (i + 1)) (JointRandomSymbol (s i) (a i)))]
  [∀ n, SinglePSpace π (s[:n + 1], a[:n])]
-- given
  (hs : ∀ k, Measurable (s k))
  (ha : ∀ k, Measurable (a k))
  (hS : ReferenceMeasure.measure (α := S) = Measure.count)
  (hA : ReferenceMeasure.measure (α := A) = Measure.count)
  (hpol : ∀ t, ∀ _ : Measurable (s t),
    a t ⟂ᵢ[π] (s[:t], a[:t]) | s t)
  (htrans : ∀ t, ∀ _ : Measurable (JointRandomSymbol (s t) (a t)),
    s (t + 1) ⟂ᵢ[π] (s[:t], a[:t]) | JointRandomSymbol (s t) (a t))
  (t : ℕ) :
-- imply
  ℙ[π](s[:t + 1] = sv[:t + 1] ∧ a[:t] = av[:t]) =
    ℙ[π]((s 0) = sv 0) *
      ∏ i ∈ Finset.range t,
        ℙ[π]((a i) = av i | (s i) = sv i) * ℙ[π]((s (i + 1)) = sv (i + 1) | (s i) = sv i ∧ (a i) = av i) := by
-- proof
  obtain ⟨h₀, h₁⟩ := Random.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
    (sv := sv) (av := av) hs ha hS hA hpol htrans
  induction t with
  | zero =>
    simpa using h₀
  | succ t ih =>
    rw [Finset.prod_range_succ]
    refine (h₁ t).trans ?_
    rw [ih]
    ring


-- created on 2023-03-22
-- updated on 2023-05-17