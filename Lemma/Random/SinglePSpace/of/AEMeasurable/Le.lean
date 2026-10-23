import Lemma.Random.SinglePSpace.of.EqMeasureCount.AEMeasurable
import sympy.stats.hidden_markov_sequence
open MeasureTheory Random Fun


/--
A prefix of an almost-everywhere measurable random vector is a `SinglePSpace`.
For `t ≤ n`, `x[:t]` is the image of `x[:n]` under the measurable map
`v ↦ v ∘ Fin.castLE`, and that codomain carries counting measure.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α]
  [Countable α]
  [MeasurableSingletonClass α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ ⇀ Ω → α} {n : ℕ}
-- given
  (t : ℕ)
  (ht : t ≤ n)
  (hx : AEMeasurable x[:n] π) :
-- imply
  SinglePSpace π x[:t] := by
-- proof
  let g : (Fin n → α) → Fin t → α := fun v => v ∘ Fin.castLE ht
  have hg : Measurable g :=
    Measurable.of_eval fun i => measurable_pi_apply (Fin.castLE ht i)
  rw [← show g ∘ x[:n] = x[:t] by funext ω i; rfl]
  apply SinglePSpace.of.EqMeasureCount.AEMeasurable (hg.comp_aemeasurable hx)
  apply CountableMeasure.measure_eq_count


-- created on 2026-10-23
