import Lemma.Random.SinglePSpace.of.All_Measurable.All_Measurable
import Theorem.Random.SinglePSpace.of.Measurable.Measurable
import Theorem.Random.SinglePSpace.of.Measurable
import Def.Probability.Process.HiddenMarkovSequence.Part2
import Instance.Probability.Process.DiscreteHMM
import Instance.Probability.Rv
open MeasureTheory


section

variable {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure Y] [CountableMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π] {x : ℕ → Ω → X} {y : ℕ → Ω → Y}

omit [Countable X] [MeasurableSingletonClass X] in
theorem IsDiscreteHMM.singlePSpace_yy [h : IsDiscreteHMM π x y] (i j : ℕ) : SinglePSpace π (y i, y j) :=
  Random.SinglePSpace.of.Measurable.Measurable
    (h.measurable_y i) (h.measurable_y j)

omit [Countable Y] [MeasurableSingletonClass Y] in
theorem IsDiscreteHMM.singlePSpace_x [h : IsDiscreteHMM π x y] (a b : ℤ) : SinglePSpace π x[a:b] := by
  have hx' : Measurable (x[a:b]) := by
    unfold Function.getSlice FunSlice.slice
    exact Measurable.of_eval fun _ => h.measurable_x _
  have hμ : ReferenceMeasure.measure
      (α := Fin ((⟨a, b, 1⟩ : Slice).stop.toNat - (⟨a, b, 1⟩ : Slice).start.toNat) → X) =
      Measure.count := rfl
  have hacc : π.map (x[a:b]) ≪ ReferenceMeasure.measure := by
    rw [hμ]
    intro s hs0
    rw [Measure.count_eq_zero_iff.mp hs0]
    apply measure_empty
  let q := (π.map (x[a:b])).rnDeriv ReferenceMeasure.measure
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hx'.aemeasurable
    exists_distribution :=
      ⟨q, Measure.measurable_rnDeriv _ _, (Measure.withDensity_rnDeriv_eq _ _ hacc).symm⟩
  }

end
