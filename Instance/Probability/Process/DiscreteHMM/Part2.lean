module
public import Theorem.Random.SinglePSpace.of.All_Measurable.All_Measurable
public import Theorem.Random.SinglePSpace.of.Measurable.Measurable
public import Theorem.Random.SinglePSpace.of.Measurable
public import Def.Probability.Process.HiddenMarkovSequence.Part2
public import Theorem.Probability.Process.DiscreteHMM.Part2
open MeasureTheory


public section

section

variable {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure Y] [CountableMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π] {x : ℕ → Ω → X} {y : ℕ → Ω → Y}

instance [h : IsDiscreteHMM π x y] (n m : ℤ) : SinglePSpace π (x[:n], y[:m]) :=
  Random.SinglePSpace.of.All_Measurable.All_Measurable h.measurable_x h.measurable_y

instance [h : IsDiscreteHMM π x y] (a b : ℤ) (j : ℕ) : SinglePSpace π (JointRandomSymbol x[a:b] (y j)) := by
  have hx' : Measurable (x[a:b]) := by
    unfold Function.getSlice FunSlice.slice
    exact Measurable.of_eval fun _ => h.measurable_x _
  have hy' : Measurable (y j) := h.measurable_y j
  have hμ : ReferenceMeasure.measure
      (α := (Fin ((⟨a, b, 1⟩ : Slice).stop.toNat - (⟨a, b, 1⟩ : Slice).start.toNat) → X) × Y) =
      Measure.count := by
    change (ReferenceMeasure.measure
        (α := Fin ((⟨a, b, 1⟩ : Slice).stop.toNat - (⟨a, b, 1⟩ : Slice).start.toNat) → X)).prod
        ReferenceMeasure.measure = Measure.count
    rw [show ReferenceMeasure.measure
          (α := Fin ((⟨a, b, 1⟩ : Slice).stop.toNat - (⟨a, b, 1⟩ : Slice).start.toNat) → X) =
          Measure.count from rfl,
        CountableMeasure.measure_eq_count, ← Measure.Count.eq.ProdCountS]
  have hacc : π.map (JointRandomSymbol x[a:b] (y j)) ≪ ReferenceMeasure.measure := by
    rw [hμ]
    intro s hs0
    rw [Measure.count_eq_zero_iff.mp hs0]
    apply measure_empty
  let q := (π.map (JointRandomSymbol x[a:b] (y j))).rnDeriv ReferenceMeasure.measure
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := (hx'.prodMk hy').aemeasurable
    exists_distribution :=
      ⟨q, Measure.measurable_rnDeriv _ _, (Measure.withDensity_rnDeriv_eq _ _ hacc).symm⟩
  }

-- y-only `SinglePSpace` instances: `x` cannot be inferred from them, so they are scoped and only
-- active after `open IsDiscreteHMM` (Lean then finds `x` from the hypothesis `h : IsDiscreteHMM π x y`).

end
