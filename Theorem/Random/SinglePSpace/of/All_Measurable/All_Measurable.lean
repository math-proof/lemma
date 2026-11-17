module

public import Theorem.Random.SinglePSpace.of.Measurable.Measurable
public import Instance.Probability.Process.HiddenMarkovSequence.Part2
public import Syntax.Data.List
public import Instance.Probability.Rv
public import Instance.Probability.JointRv
public import Theorem.Measure.Count.eq.ProdCountS
import all Notation.Fun

public section

open MeasureTheory Random

set_option linter.dupNamespace false


/--
The joint law of two prefix vectors `x[:n]` and `y[:m]` of discrete random sequences has a density.
If every `x k : Ω → α` and `y k : Ω → β` is measurable and `α`, `β` are countable (with measurable
singletons), then `(x[:n], y[:m])` spans a `SinglePSpace π`; the reference measure on the vector
types `Fin _ → α` is the counting measure.
-/
public theorem Random.SinglePSpace.of.All_Measurable.All_Measurable
  [MeasurableSpace Ω]
  [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → α} {y : ℕ → Ω → β}
  {n m : ℤ}
-- given
  (hx : ∀ k, _root_.Measurable (x k))
  (hy : ∀ k, _root_.Measurable (y k)) :
-- imply
  SinglePSpace π (x[:n], y[:m]) := by
-- proof
  have hx' : _root_.Measurable (x[:n]) := by
    unfold Function.getSlice FunSlice.slice
    exact _root_.Measurable.of_eval fun i => hx _
  have hy' : _root_.Measurable (y[:m]) := by
    unfold Function.getSlice FunSlice.slice
    exact _root_.Measurable.of_eval fun i => hy _
  have hμα : ReferenceMeasure.measure (α := FunSlice.Vec α ⟨(0 : ℤ), n, (1 : ℤ)⟩) = Measure.count :=
    rfl
  have hμβ : ReferenceMeasure.measure (α := FunSlice.Vec β ⟨(0 : ℤ), m, (1 : ℤ)⟩) = Measure.count :=
    rfl
  have hμ : ReferenceMeasure.measure
      (α := FunSlice.Vec α ⟨(0 : ℤ), n, (1 : ℤ)⟩ × FunSlice.Vec β ⟨(0 : ℤ), m, (1 : ℤ)⟩) =
      Measure.count := by
    change (ReferenceMeasure.measure (α := FunSlice.Vec α ⟨(0 : ℤ), n, (1 : ℤ)⟩)).prod
        ReferenceMeasure.measure = Measure.count
    rw [hμα, hμβ, ← Measure.Count.eq.ProdCountS]
  have hacc : π.map (x[:n], y[:m]) ≪ ReferenceMeasure.measure := by
    rw [hμ]
    intro s hs0
    rw [Measure.count_eq_zero_iff.mp hs0]
    apply measure_empty
  let q := (π.map (x[:n], y[:m])).rnDeriv ReferenceMeasure.measure
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := (hx'.prodMk hy').aemeasurable
    exists_distribution :=
      ⟨q, Measure.measurable_rnDeriv _ _, (Measure.withDensity_rnDeriv_eq _ _ hacc).symm⟩
  }


-- created on 2026-10-03
-- updated on 2026-11-17
