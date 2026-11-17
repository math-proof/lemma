import Lemma.Random.SinglePSpace.of.AEMeasurable
import Instance.Probability.Rv.Part2
import Def.Probability.Process.HiddenMarkovSequence.Part2
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
  have : CountableMeasure (Fin t → α) := inferInstance
  have hacc : π.map (g ∘ x[:n]) ≪ ReferenceMeasure.measure := by
    have : ReferenceMeasure.measure (α := Fin t → α) = Measure.count := rfl
    rw [this]
    intro s hs0
    rw [Measure.count_eq_zero_iff.mp hs0]
    apply measure_empty
  let q := (π.map (g ∘ x[:n])).rnDeriv ReferenceMeasure.measure
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hg.comp_aemeasurable hx
    exists_distribution :=
      ⟨q, Measure.measurable_rnDeriv _ _, (Measure.withDensity_rnDeriv_eq _ _ hacc).symm⟩
  }

-- created on 2026-10-23
-- updated on 2026-11-16
