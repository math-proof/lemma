import Lemma.Random.SinglePSpace.of.All_Measurable.All_Measurable
import Lemma.Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import sympy.stats.hidden_markov_sequence
open MeasureTheory


/-- `x` (observations) and `y` (hidden labels) form a first-order hidden Markov model over discrete
(counting-measure) spaces: every `x k`, `y k` is measurable, `X` and `Y` carry the counting measure,
`x (t + 1)` is independent of the past `(x[:t + 1], y[:t + 1])` given `y (t + 1)` (emission), and
`y (t + 1)` is independent of `(x[:t + 1], y[:t])` given `y t` (first-order Markov property). -/
class IsDiscreteHMM {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [ReferenceMeasure Y] [ReferenceMeasure X]
    (π : Measure Ω) [IsProbabilityMeasure π] (x : ℕ → Ω → X) (y : ℕ → Ω → Y) : Prop where
  measurable_x : ∀ k, Measurable (x k)
  measurable_y : ∀ k, Measurable (y k)
  count_x : ReferenceMeasure.measure (α := X) = Measure.count
  count_y : ReferenceMeasure.measure (α := Y) = Measure.count
  emit : ∀ t, ∀ _ : Measurable (y (t + 1)),
    x (t + 1) ⟂ᵢ[π] (x[:t + 1], y[:t + 1]) | y (t + 1)
  markov : ∀ t, ∀ _ : Measurable (y t),
    y (t + 1) ⟂ᵢ[π] (x[:t + 1], y[:t]) | y t

section
variable {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X] [Countable Y] [MeasurableSingletonClass Y]
  [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π] {x : ℕ → Ω → X} {y : ℕ → Ω → Y}

omit [Countable X] [MeasurableSingletonClass X] in
theorem IsDiscreteHMM.singlePSpace_y [h : IsDiscreteHMM π x y] (i : ℕ) : SinglePSpace π (y i) :=
  Random.SinglePSpace.of.EqMeasureCount.Measurable (h.measurable_y i) h.count_y

instance [h : IsDiscreteHMM π x y] (i j : ℕ) : SinglePSpace π (x i, y j) :=
  Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
    (h.measurable_x i) (h.measurable_y j) h.count_x h.count_y

omit [Countable X] [MeasurableSingletonClass X] in
theorem IsDiscreteHMM.singlePSpace_yy [h : IsDiscreteHMM π x y] (i j : ℕ) : SinglePSpace π (y i, y j) :=
  Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
    (h.measurable_y i) (h.measurable_y j) h.count_y h.count_y

omit [Countable Y] [MeasurableSingletonClass Y] in
theorem IsDiscreteHMM.singlePSpace_x [h : IsDiscreteHMM π x y] (a b : ℤ) : SinglePSpace π x[a:b] :=
  Random.SinglePSpace.of.EqMeasureCount.Measurable
    (Measurable.of_eval fun _ => h.measurable_x _) rfl

instance [h : IsDiscreteHMM π x y] (n m : ℤ) : SinglePSpace π (x[:n], y[:m]) :=
  Random.SinglePSpace.of.All_Measurable.All_Measurable h.measurable_x h.measurable_y

instance [h : IsDiscreteHMM π x y] (a b : ℤ) (j : ℕ) : SinglePSpace π (JointRandomSymbol x[a:b] (y j)) :=
  Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
    (Measurable.of_eval fun _ => h.measurable_x _) (h.measurable_y j) rfl h.count_y
end

namespace IsDiscreteHMM
-- y-only `SinglePSpace` instances: `x` cannot be inferred from them, so they are scoped and only
-- active after `open IsDiscreteHMM` (Lean then finds `x` from the hypothesis `h : IsDiscreteHMM π x y`).
set_option synthInstance.checkSynthOrder false in
attribute [scoped instance] singlePSpace_y singlePSpace_yy singlePSpace_x
end IsDiscreteHMM
