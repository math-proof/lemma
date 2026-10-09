import Mathlib.Probability.Independence.Conditional
import Lemma.Measure.CondIndep.is.All_MEq.of.Le_M.Le_M.Le_M
open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ProbabilityTheory

/--
Contraction of conditional independence: if `m₁` and `m₂` are conditionally independent given `m'`,
and `m₁` and `m₃` are conditionally independent given `m' ⊔ m₂`, then `m₁` is conditionally
independent of `m₂ ⊔ m₃` given `m'` (`A ⟂ B | G → A ⟂ C | (G, B) → A ⟂ (B, C) | G`).
-/
@[path]
private lemma main
  {m' m₁ m₂ m₃ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {hm' : m' ≤ mΩ}
-- given
  (hm₁ : m₁ ≤ mΩ)
  (hm₂ : m₂ ≤ mΩ)
  (hm₃ : m₃ ≤ mΩ)
  (h₀ : CondIndep m' m₁ m₂ hm' μ)
  (h₁ : CondIndep (m' ⊔ m₂) m₁ m₃ (sup_le hm' hm₂) μ) :
-- imply
  CondIndep m' m₁ (m₂ ⊔ m₃) hm' μ := by
-- proof
  rw [Measure.CondIndep.is.All_MEq.of.Le_M.Le_M.Le_M hm' hm₁ (sup_le hm₂ hm₃)]
  intro t ht
  rw [← sup_assoc]
  exact ((Measure.CondIndep.is.All_MEq.of.Le_M.Le_M.Le_M (sup_le hm' hm₂) hm₁ hm₃).1 h₁ t ht).trans
    ((Measure.CondIndep.is.All_MEq.of.Le_M.Le_M.Le_M hm' hm₁ hm₂).1 h₀ t ht)


-- created on 2026-10-06