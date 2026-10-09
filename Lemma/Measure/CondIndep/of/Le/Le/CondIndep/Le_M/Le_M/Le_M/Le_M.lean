import Mathlib.Probability.Independence.Conditional
import Lemma.Measure.CondIndep.is.All_MEq.of.Le_M.Le_M.Le_M
open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ProbabilityTheory

/--
Weak union of conditional independence, in the general form: if `m₁` and `m₂` are conditionally
independent given `m'`, then `m₁` and `m₃` are conditionally independent given any `m''` that refines
`m'` without exceeding `m' ⊔ m₂`, as long as `m'' ⊔ m₃ ≤ m' ⊔ m₂`.
With `m'' = m' ⊔ m₃` and `m₂ = m₂' ⊔ m₃` this is the textbook rule
`A ⟂ (B, C) | G → A ⟂ B | (G, C)`; with `m'' = m'` it is decomposition.
-/
@[path]
private lemma main
  {m' m₁ m₂ m'' m₃ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {hm' : m' ≤ mΩ}
-- given
  (hm₁ : m₁ ≤ mΩ)
  (hm₂ : m₂ ≤ mΩ)
  (hm'' : m'' ≤ mΩ)
  (hm₃ : m₃ ≤ mΩ)
  (h₀ : CondIndep m' m₁ m₂ hm' μ)
  (h₁ : m' ≤ m'')
  (h₂ : m'' ⊔ m₃ ≤ m' ⊔ m₂) :
-- imply
  CondIndep m'' m₁ m₃ hm'' μ := by
-- proof
  have hsup : m' ⊔ m₂ ≤ mΩ := sup_le hm' hm₂
  rw [Measure.CondIndep.is.All_MEq.of.Le_M.Le_M.Le_M hm'' hm₁ hm₃]
  intro t ht
  have e := (Measure.CondIndep.is.All_MEq.of.Le_M.Le_M.Le_M hm' hm₁ hm₂).1 h₀ t ht
  -- every `n` between `m'` and `m' ⊔ m₂` gives the same conditional probability of `t`
  have key : ∀ n : MeasurableSpace Ω, m' ≤ n → n ≤ m' ⊔ m₂ → μ⟦t | n⟧ =ᵐ[μ] μ⟦t | m'⟧ := by
    intro n hn hn'
    have hnΩ : n ≤ mΩ := hn'.trans hsup
    calc μ⟦t | n⟧ =ᵐ[μ] μ[μ⟦t | m' ⊔ m₂⟧ | n] := (condExp_condExp_of_le hn' hsup).symm
      _ =ᵐ[μ] μ[μ⟦t | m'⟧ | n] := condExp_congr_ae e
      _ = μ⟦t | m'⟧ := condExp_of_stronglyMeasurable hnΩ (stronglyMeasurable_condExp.mono hn)
          integrable_condExp
  exact (key _ (h₁.trans le_sup_left) h₂).trans (key _ h₁ (le_sup_left.trans h₂)).symm


-- created on 2026-10-06