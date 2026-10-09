import Lemma.Random.MEqExpect.of.CondIndep.Integrable.Measurable.Measurable.Measurable.Measurable
import sympy.stats.hidden_markov_sequence
open MeasureTheory ProbabilityTheory Random


/--
Forgetting histories (corrected `Random.EqConditioned.of.Eq_Conditioned.independence_assumption.bidirectional.forget_histories`):
if, given the current step `(s t, a t)`, the future reward path `r[t:]` is conditionally independent of the
history `(r, s, a)[:t]`, then conditioning a function of `r[t:]` on the whole history up to step `t`
(`(r, s, a)[:t]` together with `(s t, a t)`) is the same, π-a.e., as conditioning on `(s t, a t)` alone.
The py lemma assumes only the plain independence `r t ⟂ (s[:t], a[:t])`, which does not suffice
(counterexample: fair bits `a 0, a 1` and `r 1 = a 0 xor a 1`).
Density-free: σ-algebra conditional expectations, via
`Random.MEqExpect.of.CondIndep.Integrable.Measurable.Measurable.Measurable.Measurable`.
The hypothesis `h₃` follows from the one-step Markov property by `Random.CondIndep.of.All_CondIndep.All_Measurable`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace S] [MeasurableSpace A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S}
  {a : ℕ → Ω → A}
  {r : ℕ → Ω → ℝ}
  {t : ℕ}
  {g : (ℕ → ℝ) → ℝ}
-- given
  (h₀ : ∀ t, Measurable (r t, s t, a t))
  (h₁ : Measurable g)
  (h₂ : Integrable (rv%[π] (g r[t:])) π)
  (h₃ : r[t:] ⟂ᵢ[π] (r, s, a)[:t] | (s t, a t)) :
-- imply
  𝔼[r: π](g r[t:] | (r, s, a)[:t], s t, a t) =ᵐ[π] 𝔼[r: π](g r[t:] | s t, a t) := by
-- proof
  apply MEqExpect.of.CondIndep.Integrable.Measurable.Measurable.Measurable.Measurable
    (F := Expectation.asRV r[t:]) (X := (r, s, a)[:t]) (Z := (s t, a t))
    (Measurable.of_eval fun k ↦ (h₀ (t + k)).fst) (Measurable.of_eval fun i ↦ h₀ i) (h₀ t).snd h₁ h₂ h₃


-- created on 2026-10-07
